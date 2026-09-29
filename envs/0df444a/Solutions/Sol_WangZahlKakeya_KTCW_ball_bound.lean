-- Prove2me | solution 1 for WangZahlKakeya.KTCW_ball_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T04:33:23.986277+00:00
-- url     : https://prove2.me/submissions/5c4a6657-ccfc-4eb9-9861-3bb2152f7b01

import Mathlib
import Definitions.Def_WangZahlKakeya_wolff

/-! 4b64d04c WangZahlKakeya.KTCW_ball_bound, with `B = |B_1|` (volume of the closed unit ball).
Route: the admissible set `S` of constants is nonempty (any convex `W` holding a tube holds a
ball of radius `δ`, so `C = n·|T|/|B_δ| + 1` works), and testing `W = closedBall 0 1`, which holds
every tube, shows each `C ∈ S` has `n·|T| ≤ C·|B_1|`. Hence `n·|T| ≤ |B_1| · KTCW`. -/

set_option autoImplicit false

namespace WZKTCWAux

open MeasureTheory Metric Set WangZahlKakeya
open scoped ENNReal

lemma closedBall_subset_tube (p w : E3) (δ : ℝ) : closedBall p δ ⊆ tube p w δ := by
  intro x hx
  simp only [tube, mem_iUnion, exists_prop]
  exact ⟨0, ⟨le_refl _, zero_le_one⟩, by simpa using hx⟩

lemma tube_subset_closedBall (p w : E3) (δ : ℝ) (hw : ‖w‖ ≤ 1) :
    tube p w δ ⊆ closedBall p (1 + δ) := by
  intro x hx
  simp only [tube, mem_iUnion, exists_prop] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, hxt⟩ := hx
  rw [mem_closedBall] at hxt ⊢
  have h1 : dist (p + t • w) p ≤ 1 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    nlinarith [norm_nonneg w]
  calc dist x p ≤ dist x (p + t • w) + dist (p + t • w) p := dist_triangle _ _ _
    _ ≤ 1 + δ := by linarith

lemma tubeVol_nonneg (δ : ℝ) : 0 ≤ tubeVol δ := ENNReal.toReal_nonneg

lemma tubeVol_pos {δ : ℝ} (hδ : 0 < δ) : 0 < tubeVol δ := by
  unfold tubeVol
  have hfin : volume (tube (0 : E3) (EuclideanSpace.single 0 (1 : ℝ)) δ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top measure_closedBall_lt_top.ne
      (measure_mono (tube_subset_closedBall _ _ _ ?_))
    simp
  have hpos : 0 < volume (tube (0 : E3) (EuclideanSpace.single 0 (1 : ℝ)) δ) :=
    lt_of_lt_of_le (measure_closedBall_pos volume 0 hδ) (measure_mono (closedBall_subset_tube _ _ _))
  exact ENNReal.toReal_pos hpos.ne' hfin

lemma count_le (δ : ℝ) (n : ℕ) (p v : Fin n → E3) (W : Set E3) :
    tubeCountIn δ n p v W ≤ n := by
  unfold tubeCountIn
  calc {i : Fin n | tube (p i) (v i) δ ⊆ W}.ncard ≤ Nat.card (Fin n) := Set.ncard_le_card _
    _ = n := Nat.card_eq_fintype_card.trans (Fintype.card_fin n)

lemma count_ball (δ : ℝ) (n : ℕ) (p v : Fin n → E3)
    (hsub : ∀ i, tube (p i) (v i) δ ⊆ closedBall (0 : E3) 1) :
    tubeCountIn δ n p v (closedBall (0 : E3) 1) = n := by
  unfold tubeCountIn
  have h : {i : Fin n | tube (p i) (v i) δ ⊆ closedBall (0 : E3) 1} = Set.univ :=
    Set.eq_univ_of_forall hsub
  rw [h, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

lemma ktcw_set_nonempty {δ : ℝ} (hδ : 0 < δ) (n : ℕ) (p v : Fin n → E3) :
    {C : ℝ | 0 < C ∧ ∀ W : Set E3, Convex ℝ W →
      (tubeCountIn δ n p v W : ℝ≥0∞) * ENNReal.ofReal (tubeVol δ) ≤
        ENNReal.ofReal C * volume W}.Nonempty := by
  set β : ℝ := (volume (closedBall (0 : E3) δ)).toReal with hβ
  have hβfin : volume (closedBall (0 : E3) δ) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hβpos : 0 < β := ENNReal.toReal_pos (measure_closedBall_pos volume 0 hδ).ne' hβfin
  have htv : 0 ≤ tubeVol δ := tubeVol_nonneg δ
  refine ⟨n * tubeVol δ / β + 1, by positivity, fun W _ => ?_⟩
  by_cases h0 : tubeCountIn δ n p v W = 0
  · simp [h0]
  obtain ⟨i, hi⟩ : {i : Fin n | tube (p i) (v i) δ ⊆ W}.Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]
    exact Nat.pos_of_ne_zero h0
  have hW : volume (closedBall (0 : E3) δ) ≤ volume W := by
    rw [← Measure.addHaar_closedBall_center volume (p i)]
    exact measure_mono ((closedBall_subset_tube _ _ _).trans hi)
  have hcount : (tubeCountIn δ n p v W : ℝ≥0∞) ≤ n := by
    exact_mod_cast count_le δ n p v W
  calc (tubeCountIn δ n p v W : ℝ≥0∞) * ENNReal.ofReal (tubeVol δ)
        ≤ (n : ℝ≥0∞) * ENNReal.ofReal (tubeVol δ) := by gcongr
    _ = ENNReal.ofReal (n * tubeVol δ) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((n * tubeVol δ / β + 1) * β) := by
        apply ENNReal.ofReal_le_ofReal
        rw [add_mul, div_mul_cancel₀ _ hβpos.ne']
        linarith
    _ = ENNReal.ofReal (n * tubeVol δ / β + 1) * volume (closedBall (0 : E3) δ) := by
        rw [ENNReal.ofReal_mul (by positivity), hβ, ENNReal.ofReal_toReal hβfin]
    _ ≤ ENNReal.ofReal (n * tubeVol δ / β + 1) * volume W := by gcongr

lemma ktcw_mem_lower {δ : ℝ} {n : ℕ} {p v : Fin n → E3}
    (hsub : ∀ i, tube (p i) (v i) δ ⊆ closedBall (0 : E3) 1) {C : ℝ}
    (hC : C ∈ {C : ℝ | 0 < C ∧ ∀ W : Set E3, Convex ℝ W →
      (tubeCountIn δ n p v W : ℝ≥0∞) * ENNReal.ofReal (tubeVol δ) ≤
        ENNReal.ofReal C * volume W}) :
    (n : ℝ) * tubeVol δ ≤ C * (volume (closedBall (0 : E3) 1)).toReal := by
  have h := hC.2 (closedBall (0 : E3) 1) (convex_closedBall 0 1)
  rw [count_ball δ n p v hsub] at h
  have hfin : ENNReal.ofReal C * volume (closedBall (0 : E3) 1) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
  have := ENNReal.toReal_mono hfin h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (tubeVol_nonneg δ),
    ENNReal.toReal_ofReal hC.1.le, ENNReal.toReal_natCast] at this

lemma ktcw_lower {δ : ℝ} {n : ℕ} {p v : Fin n → E3} (hδ : 0 < δ)
    (hsub : ∀ i, tube (p i) (v i) δ ⊆ closedBall (0 : E3) 1) :
    (n : ℝ) * tubeVol δ / (volume (closedBall (0 : E3) 1)).toReal ≤ KTCW δ n p v := by
  have hV : 0 < (volume (closedBall (0 : E3) 1)).toReal :=
    ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne' measure_closedBall_lt_top.ne
  unfold KTCW
  refine le_csInf (ktcw_set_nonempty hδ n p v) (fun C hC => ?_)
  rw [div_le_iff₀ hV]
  exact ktcw_mem_lower hsub hC

end WZKTCWAux

open MeasureTheory Metric Set WangZahlKakeya in
theorem solution :
    ∃ B > (0 : ℝ), ∀ (δ : ℝ) (n : ℕ) (p v : Fin n → E3) (Y : Fin n → Set E3),
      IsTubeSystem δ n p v Y → (n : ℝ) * tubeVol δ ≤ B * KTCW δ n p v := by
  have hV : 0 < (volume (closedBall (0 : E3) 1)).toReal :=
    ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne' measure_closedBall_lt_top.ne
  refine ⟨(volume (closedBall (0 : E3) 1)).toReal, hV, fun δ n p v Y hT => ?_⟩
  have h := WZKTCWAux.ktcw_lower (n := n) (p := p) (v := v) hT.1 hT.2.2.1
  rw [div_le_iff₀ hV] at h
  linarith
