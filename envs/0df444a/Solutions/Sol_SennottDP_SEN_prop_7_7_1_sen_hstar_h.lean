-- Prove2me | solution 1 for SennottDP.SEN.prop_7_7_1_sen_hstar_h
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:54:43.570312+00:00
-- url     : https://prove2.me/submissions/07e3c1c3-1001-4fdb-b440-d7a815876017

import Mathlib
import Definitions.Def_SennottDP_SEN_Assumptions



namespace SennottDP.SEN

open scoped ENNReal NNReal
open Filter Topology

def snocE (X : Type) (n : ℕ) : (Fin n → X) × X ≃ (Fin (n+1) → X) where
  toFun p := Fin.snoc p.1 p.2
  invFun f := (Fin.init f, f (Fin.last n))
  left_inv p := by simp [Fin.init_snoc, Fin.snoc_last]
  right_inv f := by simp [Fin.snoc_init_self]

lemma tsum_snocE {X : Type} (n : ℕ) (F : (Fin (n+1) → X) → ℝ≥0∞) :
    ∑' s, F s = ∑' p : (Fin n → X), ∑' x, F (Fin.snoc p x) := by
  rw [← (snocE X n).tsum_eq]
  exact ENNReal.tsum_prod (f := fun p x => F (Fin.snoc p x))

variable {S : Type} [Countable S] {Act : Type}

lemma expState_zero' (M : SennottDP.Discounted.MDC S Act) (θ : SennottDP.Discounted.Policy M) (i : S)
    (W : S → ℝ≥0∞) : SennottDP.Discounted.expState M θ i 0 W = W i := by
  unfold SennottDP.Discounted.expState
  rw [tsum_eq_single (fun _ => i)]
  · simp [SennottDP.Discounted.histProb]
  · intro s hs
    have : s 0 ≠ i := by
      intro h; apply hs; funext k; rw [Fin.fin_one_eq_zero k]; exact h
    simp [SennottDP.Discounted.histProb, this]

lemma expState_succ' (M : SennottDP.Discounted.MDC S Act) (θ : SennottDP.Discounted.Policy M) (i : S)
    (n : ℕ) (W : S → ℝ≥0∞) : SennottDP.Discounted.expState M θ i (n+1) W =
    ∑' p, ∑' q, SennottDP.Discounted.histProb M θ i n p q *
      ∑' a, θ.dist n p q a * ∑' x, M.P (p (Fin.last n)) a x * W x := by
  unfold SennottDP.Discounted.expState
  rw [tsum_snocE]
  simp_rw [tsum_snocE (X := Act)]
  simp only [SennottDP.Discounted.histProb, Fin.init_snoc, Fin.snoc_last, Fin.snoc_castSucc]
  congr 1; funext p
  rw [ENNReal.tsum_comm]
  congr 1; funext q
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_left]
  congr 1; funext a
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  congr 1; funext x
  ring

lemma stat_dist (M : SennottDP.Discounted.MDC S Act) (e : StationaryPolicy M) (n : ℕ) p q (g : Act → ℝ≥0∞) :
    ∑' a, e.toPolicy.dist n p q a * g a = g (e.1 (p (Fin.last n))) := by
  simp only [StationaryPolicy.toPolicy]
  rw [tsum_eq_single (e.1 (p (Fin.last n)))]
  · simp
  · intro a ha; simp [ha]

lemma expState_succ_stat (M : SennottDP.Discounted.MDC S Act) (e : StationaryPolicy M) (i : S)
    (n : ℕ) (W : S → ℝ≥0∞) : SennottDP.Discounted.expState M e.toPolicy i (n+1) W =
    SennottDP.Discounted.expState M e.toPolicy i n (fun k => ∑' x, M.P k (e.1 k) x * W x) := by
  rw [expState_succ']
  simp only [stat_dist]
  rfl

lemma expState_const_stat (M : SennottDP.Discounted.MDC S Act) (e : StationaryPolicy M) (i : S)
    (n : ℕ) (c : ℝ≥0∞) : SennottDP.Discounted.expState M e.toPolicy i n (fun _ => c) = c := by
  induction n with
  | zero => exact expState_zero' _ _ _ _
  | succ n ih =>
    rw [expState_succ_stat]
    have : (fun k => ∑' x, M.P k (e.1 k) x * c) = fun _ => c := by
      funext k; rw [ENNReal.tsum_mul_right, M.P_sum k _ (e.2 k), one_mul]
    rw [this, ih]

lemma expState_add (M : SennottDP.Discounted.MDC S Act) (θ : SennottDP.Discounted.Policy M) (i : S)
    (n : ℕ) (W V : S → ℝ≥0∞) : SennottDP.Discounted.expState M θ i n (fun k => W k + V k) =
    SennottDP.Discounted.expState M θ i n W + SennottDP.Discounted.expState M θ i n V := by
  unfold SennottDP.Discounted.expState
  simp only [mul_add]
  rw [← ENNReal.tsum_add]; congr 1; funext s; rw [← ENNReal.tsum_add]

lemma expState_mono (M : SennottDP.Discounted.MDC S Act) (θ : SennottDP.Discounted.Policy M) (i : S)
    (n : ℕ) {W V : S → ℝ≥0∞} (h : ∀ k, W k ≤ V k) : SennottDP.Discounted.expState M θ i n W ≤
    SennottDP.Discounted.expState M θ i n V := by
  unfold SennottDP.Discounted.expState
  gcongr with s as
  exact h _

lemma stateProb_tsum (M : SennottDP.Discounted.MDC S Act) (θ : SennottDP.Discounted.Policy M) (i : S)
    (n : ℕ) (W : S → ℝ≥0∞) : ∑' j, stateProb M θ i n j * W j =
    SennottDP.Discounted.expState M θ i n W := by
  unfold stateProb SennottDP.Discounted.expState
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]; congr 1; funext s
  rw [ENNReal.tsum_comm]; congr 1; funext as
  rw [tsum_eq_single (s (Fin.last n))]
  · simp
  · intro j hj; simp [Ne.symm hj]

lemma expCost_stat (M : SennottDP.Discounted.MDC S Act) (e : StationaryPolicy M) (i : S) (t : ℕ) :
    SennottDP.Discounted.expCost M e.toPolicy i t =
    SennottDP.Discounted.expState M e.toPolicy i t (fun k => (M.C k (e.1 k) : ℝ≥0∞)) := by
  unfold SennottDP.Discounted.expCost SennottDP.Discounted.expState
  congr 1; funext s; congr 1; funext as; congr 1
  simp only [StationaryPolicy.toPolicy]
  rw [Finset.sum_eq_single (e.1 (s (Fin.last t)))]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (e.2 _) h

lemma limfun_ge (M : SennottDP.Discounted.MDC S Act) (z : S) (Lf : S → ℝ) (hL : H3 M z Lf)
    (h : S → ℝ) (hh : IsLimitFunction M z h) (i : S) : -Lf i ≤ h i := by
  obtain ⟨_, αs, φ, hαs, _, _, ht⟩ := hh
  have := ge_of_tendsto' (ht i) (fun n => hL.2 _ (hαs _) i)
  exact_mod_cast this

lemma ereal_aux (A B E : ℝ≥0∞) (hBE : B ≤ E) (hE : E ≠ ⊤) (n : ℕ) (hn : 1 ≤ n) :
    -(((E / (n : ℝ≥0∞)) : ℝ≥0∞) : EReal) ≤ (((n : ℝ)⁻¹ : ℝ) : EReal) * ((A : EReal) - (B : EReal)) := by
  have hB : B ≠ ⊤ := ne_top_of_le_ne_top hE hBE
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hED : E / (n : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top hE (by simp; omega)
  rw [← EReal.coe_ennreal_toReal hED, ← EReal.coe_ennreal_toReal hB, ENNReal.toReal_div,
    ENNReal.toReal_natCast]
  rcases eq_or_ne A ⊤ with hA | hA
  · subst hA
    rw [EReal.coe_ennreal_top, EReal.top_sub_coe, EReal.mul_top_of_pos (by exact_mod_cast inv_pos.mpr hnpos)]
    exact le_top
  · rw [← EReal.coe_ennreal_toReal hA, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_neg]
    rw [EReal.coe_le_coe_iff]
    have h1 : B.toReal ≤ E.toReal := ENNReal.toReal_mono hE hBE
    have h2 : 0 ≤ A.toReal := ENNReal.toReal_nonneg
    rw [div_eq_mul_inv]
    have h3 : 0 < (n:ℝ)⁻¹ := inv_pos.mpr hnpos
    nlinarith

lemma s771_core (M : SennottDP.Discounted.MDC S Act) (z : S) :
    (∀ (Mf : S → ℝ) (L : ℝ), SENAssumptions M z Mf L → HStarAssumptions M z Mf (fun _ => L)) ∧
      ∀ Mf Lf : S → ℝ, HStarAssumptions M z Mf Lf → HAssumptions M z Mf Lf := by
  constructor
  · intro Mf L ⟨h1, h2, hL0, hL⟩
    refine ⟨h1, h2, ⟨fun _ => hL0, hL⟩, ?_, ?_⟩
    · intro i a ha
      rw [ENNReal.tsum_mul_right, M.P_sum i a ha, one_mul]
      exact ENNReal.ofReal_ne_top
    · intro e i
      simp only [expState_const_stat]
      refine ⟨fun _ _ => ENNReal.ofReal_ne_top, ?_⟩
      have : Tendsto (fun n : ℕ => ENNReal.ofReal L * (n : ℝ≥0∞)⁻¹) atTop (𝓝 (ENNReal.ofReal L * 0)) :=
        ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr ENNReal.ofReal_ne_top)
      rw [mul_zero] at this
      simpa [div_eq_mul_inv] using this
  · intro Mf Lf ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, h4, ?_⟩
    intro h hh e i
    have hge := limfun_ge M z Lf h3 h hh
    set E := fun n => SennottDP.Discounted.expState M e.toPolicy i n (fun j => ENNReal.ofReal (Lf j))
      with hEdef
    have hBE : ∀ n, (∑' j, stateProb M e.toPolicy i n j * ENNReal.ofReal (-h j)) ≤ E n := by
      intro n
      rw [hEdef]; dsimp only
      rw [← stateProb_tsum]
      gcongr with j
      linarith [hge j]
    constructor
    · intro n hn
      unfold expReal wsum
      have hB : (∑' j, stateProb M e.toPolicy i n j * ENNReal.ofReal (-h j)) ≠ ⊤ :=
        ne_top_of_le_ne_top ((h5 e i).1 n hn) (hBE n)
      rw [← EReal.coe_ennreal_toReal hB]
      rcases eq_or_ne (∑' j, stateProb M e.toPolicy i n j * ENNReal.ofReal (h j)) ⊤ with hA | hA
      · rw [hA, EReal.coe_ennreal_top, EReal.top_sub_coe]; exact bot_lt_top
      · rw [← EReal.coe_ennreal_toReal hA, ← EReal.coe_sub]; exact EReal.bot_lt_coe _
    · have hT := (h5 e i).2
      have hT' : Tendsto (fun n : ℕ => -(((E n / (n : ℝ≥0∞)) : ℝ≥0∞) : EReal)) atTop (𝓝 0) := by
        have := (continuous_neg.tendsto (0:EReal)).comp
          ((continuous_coe_ennreal_ereal.tendsto 0).comp hT)
        simp only [EReal.coe_ennreal_zero, neg_zero] at this
        exact this
      rw [← hT'.liminf_eq]
      refine Filter.liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
      filter_upwards [Filter.eventually_ge_atTop 2] with n hn
      unfold expReal wsum
      exact ereal_aux _ _ _ (hBE n) ((h5 e i).1 n hn) n (by omega)

end SennottDP.SEN

open SennottDP.SEN


theorem solution {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act) (z : S) :
    (∀ (Mf : S → ℝ) (L : ℝ), SENAssumptions M z Mf L → HStarAssumptions M z Mf (fun _ => L)) ∧
      ∀ Mf Lf : S → ℝ, HStarAssumptions M z Mf Lf → HAssumptions M z Mf Lf := by
  exact s771_core M z
