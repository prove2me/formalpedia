-- Prove2me | solution 1 for Sennott1989.AvgCost.lemma_A1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:22:17.837604+00:00
-- url     : https://prove2.me/submissions/383cd4ef-e32f-48db-8af9-63506376edf7

import Mathlib
import Definitions.Def_Sennott1989_AvgCost_Assumptions
import Theorems.Thm_SennottDP_SEN_lemma_7_2_1_acoi_bound

open scoped ENNReal NNReal
open Filter Topology

namespace SennottA1Aux

open SennottDP.SEN

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

lemma stat_dist (M : SennottDP.Discounted.MDC S Act) (e : SennottDP.SEN.StationaryPolicy M) (n : ℕ) p q (g : Act → ℝ≥0∞) :
    ∑' a, e.toPolicy.dist n p q a * g a = g (e.1 (p (Fin.last n))) := by
  simp only [StationaryPolicy.toPolicy]
  rw [tsum_eq_single (e.1 (p (Fin.last n)))]
  · simp
  · intro a ha; simp [ha]

lemma expState_succ_stat (M : SennottDP.Discounted.MDC S Act) (e : SennottDP.SEN.StationaryPolicy M) (i : S)
    (n : ℕ) (W : S → ℝ≥0∞) : SennottDP.Discounted.expState M e.toPolicy i (n+1) W =
    SennottDP.Discounted.expState M e.toPolicy i n (fun k => ∑' x, M.P k (e.1 k) x * W x) := by
  rw [expState_succ']
  simp only [stat_dist]
  rfl

lemma expState_const_stat (M : SennottDP.Discounted.MDC S Act) (e : SennottDP.SEN.StationaryPolicy M) (i : S)
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
    (n : ℕ) (W : S → ℝ≥0∞) : ∑' j, SennottDP.SEN.stateProb M θ i n j * W j =
    SennottDP.Discounted.expState M θ i n W := by
  unfold SennottDP.SEN.stateProb SennottDP.Discounted.expState
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]; congr 1; funext s
  rw [ENNReal.tsum_comm]; congr 1; funext as
  rw [tsum_eq_single (s (Fin.last n))]
  · simp
  · intro j hj; simp [Ne.symm hj]

lemma expCost_stat (M : SennottDP.Discounted.MDC S Act) (e : SennottDP.SEN.StationaryPolicy M) (i : S) (t : ℕ) :
    SennottDP.Discounted.expCost M e.toPolicy i t =
    SennottDP.Discounted.expState M e.toPolicy i t (fun k => (M.C k (e.1 k) : ℝ≥0∞)) := by
  unfold SennottDP.Discounted.expCost SennottDP.Discounted.expState
  congr 1; funext s; congr 1; funext as; congr 1
  simp only [StationaryPolicy.toPolicy]
  rw [Finset.sum_eq_single (e.1 (s (Fin.last t)))]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (e.2 _) h


lemma keyRev (p : S → ℝ≥0∞) (hp : ∑' x, p x = 1) (c : ℝ≥0) (h : S → ℝ) (N g hk : ℝ)
    (hN0 : 0 ≤ N) (hN : ∀ j, h j ≤ N) (hkN : hk ≤ N)
    (H : ((g + hk : ℝ) : EReal) ≤ ((c : ℝ) : EReal) + wsum p h) :
    ENNReal.ofReal (max g 0) + ∑' x, p x * ENNReal.ofReal (N - h x) ≤
      (c : ℝ≥0∞) + ENNReal.ofReal (N - hk) + ENNReal.ofReal (max (-g) 0) := by
  unfold wsum at H
  set Pos := ∑' j, p j * ENNReal.ofReal (h j) with hPos
  set Ng := ∑' j, p j * ENNReal.ofReal (-h j) with hNg
  set PG := ∑' x, p x * ENNReal.ofReal (N - h x) with hPG
  have hsum : PG + Pos = Ng + ENNReal.ofReal N := by
    have hc : ENNReal.ofReal N = ∑' x, p x * ENNReal.ofReal N := by
      rw [ENNReal.tsum_mul_right, hp, one_mul]
    rw [hc, hPG, hNg, hPos, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
    congr 1; funext x
    rw [← mul_add, ← mul_add]; congr 1
    have hx := hN x
    rcases le_total 0 (h x) with h0 | h0
    · rw [ENNReal.ofReal_of_nonpos (by linarith : -h x ≤ 0), zero_add,
        ← ENNReal.ofReal_add (by linarith) h0]
      congr 1; ring
    · rw [ENNReal.ofReal_of_nonpos h0, add_zero, ← ENNReal.ofReal_add (by linarith) hN0]
      congr 1; ring
  have hPosle : Pos ≤ ENNReal.ofReal N := by
    calc Pos ≤ ∑' x, p x * ENNReal.ofReal N := by
          rw [hPos]; gcongr with x; exact hN x
      _ = ENNReal.ofReal N := by rw [ENNReal.tsum_mul_right, hp, one_mul]
  have hPosf : Pos ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hPosle
  have hNgf : Ng ≠ ⊤ := by
    intro hT
    rw [hT, ← EReal.coe_ennreal_toReal hPosf, EReal.coe_ennreal_top, EReal.sub_top,
      EReal.add_bot] at H
    exact absurd H (not_le.mpr (EReal.bot_lt_coe _))
  have hPGf : PG ≠ ⊤ := by
    intro hT
    rw [hT, top_add] at hsum
    exact (ENNReal.add_ne_top.mpr ⟨hNgf, ENNReal.ofReal_ne_top⟩) hsum.symm
  have hr : PG.toReal + Pos.toReal = Ng.toReal + N := by
    have := congrArg ENNReal.toReal hsum
    rwa [ENNReal.toReal_add hPGf hPosf, ENNReal.toReal_add hNgf ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hN0] at this
  rw [← EReal.coe_ennreal_toReal hPosf, ← EReal.coe_ennreal_toReal hNgf, ← EReal.coe_sub,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at H
  have hg : max g 0 - max (-g) 0 = g := by
    rcases le_total 0 g with hg | hg
    · rw [max_eq_left hg, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hg, max_eq_left (by linarith)]; ring
  have e1 : ENNReal.ofReal (max g 0) + PG = ENNReal.ofReal (max g 0 + PG.toReal) := by
    rw [ENNReal.ofReal_add (le_max_right _ _) ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hPGf]
  have e2 : (c : ℝ≥0∞) + ENNReal.ofReal (N - hk) + ENNReal.ofReal (max (-g) 0) =
      ENNReal.ofReal ((c : ℝ) + (N - hk) + max (-g) 0) := by
    rw [ENNReal.ofReal_add, ENNReal.ofReal_add, ENNReal.ofReal_coe_nnreal]
    · exact c.2
    · linarith
    · have := c.2; linarith
    · exact le_max_right _ _
  rw [e1, e2]
  apply ENNReal.ofReal_le_ofReal
  linarith

lemma iterRev (M : SennottDP.Discounted.MDC S Act) (e : SennottDP.SEN.StationaryPolicy M)
    (G : S → ℝ≥0∞) (a b : ℝ≥0∞)
    (hk : ∀ k, a + ∑' x, M.P k (e.1 k) x * G x ≤ (M.C k (e.1 k) : ℝ≥0∞) + G k + b) (i : S) :
    ∀ n : ℕ, n * a + SennottDP.Discounted.expState M e.toPolicy i n G ≤
      SennottDP.SEN.horizonCost M e.toPolicy n i + G i + n * b := by
  intro n
  induction n with
  | zero => simp [SennottDP.SEN.horizonCost, expState_zero']
  | succ n ih =>
    have step : a + SennottDP.Discounted.expState M e.toPolicy i (n+1) G ≤
        SennottDP.Discounted.expCost M e.toPolicy i n +
          SennottDP.Discounted.expState M e.toPolicy i n G + b := by
      rw [expCost_stat, expState_succ_stat, ← expState_const_stat M e i n b, ← expState_add,
        ← expState_add, ← expState_const_stat M e i n a, ← expState_add]
      exact expState_mono _ _ _ _ (fun k => hk k)
    unfold SennottDP.SEN.horizonCost at ih ⊢
    rw [Finset.sum_range_succ]
    push_cast
    set E := SennottDP.Discounted.expState M e.toPolicy i n G
    set E' := SennottDP.Discounted.expState M e.toPolicy i (n + 1) G
    set H := ∑ x ∈ Finset.range n, SennottDP.Discounted.expCost M e.toPolicy i x
    set c := SennottDP.Discounted.expCost M e.toPolicy i n
    calc ((n : ℝ≥0∞) + 1) * a + E' = n * a + (a + E') := by ring
      _ ≤ n * a + (c + E + b) := add_le_add le_rfl step
      _ = (n * a + E) + (c + b) := by ring
      _ ≤ (H + G i + n * b) + (c + b) := add_le_add ih le_rfl
      _ = H + c + G i + (n + 1) * b := by ring

end SennottA1Aux

open SennottDP.Discounted Sennott1989.AvgCost SennottA1Aux in
theorem solution {Act : Type} (M : MDC ℕ Act) (f : StationaryPolicy M) (g : ℝ) (h : ℕ → ℝ)
    (N : ℝ) :
    ((∀ i, -N ≤ h i) →
      (∀ i, acoiTerm M h i (f.1 i) ≤ ((g + h i : ℝ) : EReal)) →
        ∀ i, (SennottDP.SEN.avgCost M f.toPolicy i : EReal) ≤ (g : EReal)) ∧
      ((∀ i, h i ≤ N) → (∀ i, ((g + h i : ℝ) : EReal) ≤ acoiTerm M h i (f.1 i)) →
        ∀ i, (g : EReal) ≤ (SennottDP.SEN.avgCost M f.toPolicy i : EReal)) := by
  let e : SennottDP.SEN.StationaryPolicy M := f
  have hpol : f.toPolicy = e.toPolicy := rfl
  refine ⟨fun hlow hA1 i => ?_, fun hup hA1 i => ?_⟩
  · rw [hpol]
    exact SennottDP.SEN.lemma_7_2_1_acoi_bound M e g h ⟨-N, by rintro _ ⟨j, rfl⟩; exact hlow j⟩
      hA1 i
  · rw [hpol]
    rcases le_or_gt g 0 with hg | hg
    · exact le_trans (EReal.coe_le_coe_iff.2 hg) (EReal.coe_ennreal_nonneg _)
    set N' := max N 0
    have hN0 : 0 ≤ N' := le_max_right _ _
    have hN' : ∀ j, h j ≤ N' := fun j => (hup j).trans (le_max_left _ _)
    have hk := fun k => keyRev (M.P k (e.1 k)) (M.P_sum k _ (e.2 k)) (M.C k (e.1 k)) h N' g (h k)
      hN0 hN' (hN' k) (hA1 k)
    have hit := iterRev M e (fun x => ENNReal.ofReal (N' - h x)) _ _ hk i
    simp only [max_eq_left hg.le, max_eq_right (by linarith : -g ≤ 0), ENNReal.ofReal_zero,
      mul_zero, add_zero] at hit
    -- n g ≤ v_n + (N' - h i)
    have hc : ∀ n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal g ≤
        SennottDP.SEN.horizonCost M e.toPolicy n i + ENNReal.ofReal (N' - h i) :=
      fun n => le_trans le_self_add (hit n)
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal g - ENNReal.ofReal (N' - h i) * (n : ℝ≥0∞)⁻¹)
        atTop (𝓝 (ENNReal.ofReal g - ENNReal.ofReal (N' - h i) * 0)) := by
      refine ENNReal.Tendsto.sub tendsto_const_nhds
        (ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
          (Or.inr ENNReal.ofReal_ne_top)) (Or.inl ENNReal.ofReal_ne_top)
    rw [mul_zero, tsub_zero] at hlim
    have hav : ENNReal.ofReal g ≤ SennottDP.SEN.avgCost M e.toPolicy i := by
      unfold SennottDP.SEN.avgCost
      rw [← hlim.limsup_eq]
      refine Filter.limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by simp; omega
      rw [tsub_le_iff_right]
      calc ENNReal.ofReal g = (ENNReal.ofReal g * n) / n := by
            rw [ENNReal.mul_div_cancel_right hn0 (ENNReal.natCast_ne_top n)]
        _ ≤ (SennottDP.SEN.horizonCost M e.toPolicy n i + ENNReal.ofReal (N' - h i)) / n := by
            gcongr; rw [mul_comm]; exact hc n
        _ = _ := by rw [ENNReal.add_div, div_eq_mul_inv (ENNReal.ofReal (N' - h i))]
    calc (g : EReal) = ((ENNReal.ofReal g : ℝ≥0∞) : EReal) := by
          rw [EReal.coe_ennreal_ofReal, max_eq_left hg.le]
      _ ≤ _ := EReal.coe_ennreal_le_coe_ennreal_iff.mpr hav
