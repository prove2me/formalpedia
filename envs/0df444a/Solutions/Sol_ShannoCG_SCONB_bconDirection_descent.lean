-- Prove2me | solution 1 for ShannoCG.SCONB.bconDirection_descent
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:33:03.888589+00:00
-- url     : https://prove2.me/submissions/3b9f2fe7-5c05-4823-90e6-70eeb622e711

import Mathlib
import Definitions.Def_ShannoCG_SCONB_bconDirection
import Definitions.Def_ShannoCG_SCONB_sconbDirection
open Matrix ShannoCG.SCONB

private theorem bfgs_positive {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ v, v ≠ 0 → 0 < v ⬝ᵥ (H *ᵥ v)) (p y : Fin n → ℝ)
    (hpy : 0 < p ⬝ᵥ y) (v : Fin n → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ (bfgsUpdate H p y *ᵥ v) := by
  let z := v - ((p ⬝ᵥ v) / (p ⬝ᵥ y)) • y
  have hid : v ⬝ᵥ (bfgsUpdate H p y *ᵥ v) =
      z ⬝ᵥ (H *ᵥ z) + (p ⬝ᵥ v) ^ 2 / (p ⬝ᵥ y) := by
    simp only [z, bfgsUpdate, add_mulVec, smul_mulVec, sub_mulVec, vecMulVec_mulVec,
      mulVec_sub, mulVec_smul, dotProduct_add, dotProduct_sub, dotProduct_smul,
      sub_dotProduct, smul_dotProduct, ← dotProduct_mulVec]
    simp [smul_eq_mul, div_eq_mul_inv]
    rw [dotProduct_comm v p]
    field_simp [ne_of_gt hpy]
    <;> ring
  rw [hid]
  by_cases hpv : p ⬝ᵥ v = 0
  · have hz : z = v := by simp [z, hpv]
    simpa [hz, hpv] using hH v hv
  · have hq : 0 < (p ⬝ᵥ v) ^ 2 / (p ⬝ᵥ y) := div_pos (sq_pos_of_ne_zero hpv) hpy
    have hz : 0 ≤ z ⬝ᵥ (H *ᵥ z) := by
      by_cases hz : z = 0
      · simp [hz]
      · exact (hH z hz).le
    linarith

private theorem self_dot_pos {n : ℕ} (v : Fin n → ℝ) (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  have hn : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  have he : v ⬝ᵥ v ≠ 0 := fun h => hv (dotProduct_self_eq_zero.mp h)
  exact lt_of_le_of_ne hn (Ne.symm he)

private theorem unscaled_as_update {n : ℕ} (p y : Fin n → ℝ) :
    unscaledRestart p y = bfgsUpdate (1 : Matrix (Fin n) (Fin n) ℝ) p y := by
  simp only [unscaledRestart, bfgsUpdate, one_mulVec, vecMul_one]

private theorem scaled_as_update {n : ℕ} (p y : Fin n → ℝ) (hpy : 0 < p ⬝ᵥ y) :
    scaledRestart p y = bfgsUpdate (gammaScale p y • (1 : Matrix (Fin n) (Fin n) ℝ)) p y := by
  have hy : y ≠ 0 := by intro h; subst y; simpa using hpy
  have hyy := self_dot_pos y hy
  simp only [scaledRestart, bfgsUpdate, smul_mulVec, vecMul_smul, one_mulVec, vecMul_one,
    dotProduct_smul]
  ext i j
  simp [gammaScale, smul_eq_mul, Matrix.vecMulVec]
  field_simp
  <;> ring

theorem solution {n : ℕ} (pt yt pk yk g : Fin n → ℝ) (hpyt : 0 < pt ⬝ᵥ yt)
    (hpyk : 0 < pk ⬝ᵥ yk) (hg : g ≠ 0) :
    g ⬝ᵥ bconDirection pt yt pk yk g < 0 := by
  have hbase : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) := by
    intro v hv
    simpa using self_dot_pos v hv
  have ht : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (unscaledRestart pt yt *ᵥ v) := by
    intro v hv
    rw [unscaled_as_update]
    exact bfgs_positive _ hbase pt yt hpyt v hv
  have hk := bfgs_positive _ ht pk yk hpyk g hg
  simpa [bconDirection, dotProduct_neg] using neg_neg_of_pos hk
