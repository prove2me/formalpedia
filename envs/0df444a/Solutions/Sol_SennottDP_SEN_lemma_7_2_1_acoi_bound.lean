-- Prove2me | solution 1 for SennottDP.SEN.lemma_7_2_1_acoi_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:57:23.461798+00:00
-- url     : https://prove2.me/submissions/e45150bc-9b8e-4436-9e33-e03888c61239

import Mathlib
import Definitions.Def_SennottDP_SEN_Assumptions
import Definitions.Def_SennottDP_SEN_Criteria

open scoped ENNReal NNReal


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

lemma key721 (p : S → ℝ≥0∞) (hp : ∑' x, p x = 1) (c : ℝ≥0) (h : S → ℝ) (b J hk : ℝ) (hb : ∀ j, -b ≤ h j) (hkb : -b ≤ hk)
    (hb0 : 0 ≤ b) (H : ((c : ℝ) : EReal) + wsum p h ≤ ((J + hk : ℝ) : EReal)) :
    (c : ℝ≥0∞) + ∑' x, p x * ENNReal.ofReal (h x + b) + ENNReal.ofReal (max (-J) 0) ≤
      ENNReal.ofReal (max J 0) + ENNReal.ofReal (hk + b) := by
  unfold wsum at H
  set Pos := ∑' j, p j * ENNReal.ofReal (h j) with hPos
  set N := ∑' j, p j * ENNReal.ofReal (-h j) with hN
  set PG := ∑' x, p x * ENNReal.ofReal (h x + b) with hPG
  have hsum : PG + N = Pos + ENNReal.ofReal b := by
    have hc : ENNReal.ofReal b = ∑' x, p x * ENNReal.ofReal b := by
      rw [ENNReal.tsum_mul_right, hp, one_mul]
    rw [hc, hPG, hN, hPos, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
    congr 1; funext x
    rw [← mul_add, ← mul_add]; congr 1
    rcases le_total 0 (h x) with hx | hx
    · rw [ENNReal.ofReal_of_nonpos (by linarith : -h x ≤ 0), add_zero,
        ENNReal.ofReal_add hx hb0]
    · rw [ENNReal.ofReal_of_nonpos hx, zero_add, ← ENNReal.ofReal_add (by linarith [hb x]) (by linarith)]
      congr 1; ring
  have hNle : N ≤ ENNReal.ofReal b := by
    calc N ≤ ∑' x, p x * ENNReal.ofReal b := by
          rw [hN]; gcongr with x; linarith [hb x]
      _ = ENNReal.ofReal b := by rw [ENNReal.tsum_mul_right, hp, one_mul]
  have hNf : N ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hNle
  have hPosf : Pos ≠ ⊤ := by
    intro hP
    rw [hP, ← EReal.coe_ennreal_toReal hNf, EReal.coe_ennreal_top, EReal.top_sub_coe,
      EReal.coe_add_top] at H
    exact absurd H (not_le.mpr (EReal.coe_lt_top _))
  have hPGf : PG ≠ ⊤ := by
    intro hP
    rw [hP, top_add] at hsum
    exact (ENNReal.add_ne_top.mpr ⟨hPosf, ENNReal.ofReal_ne_top⟩) hsum.symm
  have hr : PG.toReal + N.toReal = Pos.toReal + b := by
    have := congrArg ENNReal.toReal hsum
    rwa [ENNReal.toReal_add hPGf hNf, ENNReal.toReal_add hPosf ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hb0] at this
  rw [← EReal.coe_ennreal_toReal hPosf, ← EReal.coe_ennreal_toReal hNf, ← EReal.coe_sub,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at H
  have hJ : max J 0 - max (-J) 0 = J := by
    rcases le_total 0 J with hJ | hJ
    · rw [max_eq_left hJ, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hJ, max_eq_left (by linarith)]; ring
  have hk0 : 0 ≤ hk + b := by linarith
  have e1 : (c : ℝ≥0∞) + PG + ENNReal.ofReal (max (-J) 0) =
      ENNReal.ofReal ((c : ℝ) + PG.toReal + max (-J) 0) := by
    rw [ENNReal.ofReal_add (by positivity) (le_max_right _ _),
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_toReal hPGf,
      ENNReal.ofReal_coe_nnreal]
  rw [e1, ← ENNReal.ofReal_add (le_max_right _ _) hk0]
  apply ENNReal.ofReal_le_ofReal
  linarith

lemma iter721 (M : SennottDP.Discounted.MDC S Act) (e : StationaryPolicy M) (G : S → ℝ≥0∞) (a b : ℝ≥0∞)
    (hk : ∀ k, (M.C k (e.1 k) : ℝ≥0∞) + ∑' x, M.P k (e.1 k) x * G x + b ≤ a + G k) (i : S) :
    ∀ n : ℕ, horizonCost M e.toPolicy n i + SennottDP.Discounted.expState M e.toPolicy i n G + n * b ≤
      n * a + G i := by
  intro n
  induction n with
  | zero => simp [horizonCost, expState_zero']
  | succ n ih =>
    have step : SennottDP.Discounted.expCost M e.toPolicy i n +
        SennottDP.Discounted.expState M e.toPolicy i (n+1) G + b ≤
        a + SennottDP.Discounted.expState M e.toPolicy i n G := by
      rw [expCost_stat, expState_succ_stat, ← expState_const_stat M e i n b, ← expState_add,
        ← expState_add, ← expState_const_stat M e i n a, ← expState_add]
      exact expState_mono _ _ _ _ (fun k => hk k)
    unfold horizonCost at ih ⊢
    rw [Finset.sum_range_succ]
    push_cast
    calc (∑ x ∈ Finset.range n, SennottDP.Discounted.expCost M e.toPolicy i x) +
          SennottDP.Discounted.expCost M e.toPolicy i n +
          SennottDP.Discounted.expState M e.toPolicy i (n + 1) G + (↑n + 1) * b
        = ((∑ x ∈ Finset.range n, SennottDP.Discounted.expCost M e.toPolicy i x) + n * b) +
          (SennottDP.Discounted.expCost M e.toPolicy i n +
          SennottDP.Discounted.expState M e.toPolicy i (n + 1) G + b) := by ring
      _ ≤ ((∑ x ∈ Finset.range n, SennottDP.Discounted.expCost M e.toPolicy i x) + n * b) +
          (a + SennottDP.Discounted.expState M e.toPolicy i n G) := add_le_add le_rfl step
      _ = ((∑ x ∈ Finset.range n, SennottDP.Discounted.expCost M e.toPolicy i x) +
          SennottDP.Discounted.expState M e.toPolicy i n G + n * b) + a := by ring
      _ ≤ (n * a + G i) + a := add_le_add ih le_rfl
      _ = (↑n + 1) * a + G i := by ring

lemma s721_core (M : SennottDP.Discounted.MDC S Act)
    (e : StationaryPolicy M) (J : ℝ) (h : S → ℝ) (hbdd : BddBelow (Set.range h))
    (h74 : ∀ i, ((M.C i (e.1 i) : ℝ) : EReal) + wsum (M.P i (e.1 i)) h ≤ ((J + h i : ℝ) : EReal)) :
    ∀ i, (avgCost M e.toPolicy i : EReal) ≤ (J : EReal) := by
  obtain ⟨m, hm⟩ := hbdd
  set b := max (-m) 0 with hbdef
  have hb0 : 0 ≤ b := le_max_right _ _
  have hb : ∀ j, -b ≤ h j := fun j => by
    have := hm ⟨j, rfl⟩; have := le_max_left (-m) 0; linarith
  have hk := fun k => key721 (M.P k (e.1 k)) (M.P_sum k _ (e.2 k)) (M.C k (e.1 k)) h b J (h k)
    hb (hb k) hb0 (h74 k)
  intro i
  have hit := iter721 M e (fun x => ENNReal.ofReal (h x + b)) _ _ hk i
  rcases lt_or_ge J 0 with hJ | hJ
  · exfalso
    have hJm : 0 < max (-J) 0 := lt_max_of_lt_left (by linarith)
    obtain ⟨n, hn⟩ := exists_nat_gt ((h i + b) / max (-J) 0)
    have h1 := hit n
    rw [max_eq_right hJ.le, ENNReal.ofReal_zero, mul_zero, zero_add] at h1
    have h2 : (n : ℝ≥0∞) * ENNReal.ofReal (max (-J) 0) ≤ ENNReal.ofReal (h i + b) :=
      le_trans le_add_self h1
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by linarith [hb i])] at h2
    rw [div_lt_iff₀ hJm] at hn
    linarith
  · have hc : ∀ n : ℕ, horizonCost M e.toPolicy n i ≤ n * ENNReal.ofReal J + ENNReal.ofReal (h i + b) := by
      intro n
      have h1 := hit n
      rw [max_eq_left hJ, max_eq_right (by linarith : -J ≤ 0)] at h1
      exact le_trans (le_trans le_self_add le_self_add) h1
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal J + ENNReal.ofReal (h i + b) * (n : ℝ≥0∞)⁻¹) atTop
        (𝓝 (ENNReal.ofReal J + ENNReal.ofReal (h i + b) * 0)) :=
      tendsto_const_nhds.add (ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
        (Or.inr ENNReal.ofReal_ne_top))
    rw [mul_zero, add_zero] at hlim
    have hav : avgCost M e.toPolicy i ≤ ENNReal.ofReal J := by
      unfold avgCost
      rw [← hlim.limsup_eq]
      refine Filter.limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by simp; omega
      rw [ENNReal.div_le_iff hn0 (ENNReal.natCast_ne_top n), add_mul, mul_assoc,
        ENNReal.inv_mul_cancel hn0 (ENNReal.natCast_ne_top n), mul_one, mul_comm]
      exact hc n
    calc (avgCost M e.toPolicy i : EReal) ≤ ((ENNReal.ofReal J : ℝ≥0∞) : EReal) :=
          EReal.coe_ennreal_le_coe_ennreal_iff.mpr hav
      _ = (J : EReal) := by rw [EReal.coe_ennreal_ofReal, max_eq_left hJ]

end SennottDP.SEN

open SennottDP.SEN


theorem solution {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act)
    (e : StationaryPolicy M) (J : ℝ) (h : S → ℝ) (hbdd : BddBelow (Set.range h))
    (h74 : ∀ i, ((M.C i (e.1 i) : ℝ) : EReal) + wsum (M.P i (e.1 i)) h ≤ ((J + h i : ℝ) : EReal)) :
    ∀ i, (avgCost M e.toPolicy i : EReal) ≤ (J : EReal) := by
  exact s721_core M e J h hbdd h74
