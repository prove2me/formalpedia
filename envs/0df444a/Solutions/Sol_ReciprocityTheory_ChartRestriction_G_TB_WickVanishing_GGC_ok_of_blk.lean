-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.ok_of_blk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:35.231886+00:00
-- url     : https://prove2.me/submissions/bcabb0d9-95c0-401e-a51a-3392368dbefc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConnA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_Gy_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {r : ℕ} (p0 : ℕ)
variable {p0}
variable {p0 : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
theorem _root_.solution {y : Matrix (Fin r) (Fin r) ℂ}
    (hy : ∀ k a : Fin r, ¬((k : ℕ) < p0 ↔ (a : ℕ) < p0) → y k a = 0) (hd : y.det ≠ 0) : Ok p0 y := by
  have key : diagonal (sv p0) * Gy p0 y = (y.map (starRingEnd ℂ))ᴴ * y.map (starRingEnd ℂ) := by
    ext a b
    rw [Matrix.diagonal_mul, Gy_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def, Complex.conj_conj]
    by_cases hka : ((k : ℕ) < p0 ↔ (a : ℕ) < p0)
    · have hs : sv p0 a * sv p0 k = 1 := by
        unfold sv
        by_cases hk : (k : ℕ) < p0 <;> by_cases ha : (a : ℕ) < p0
        · rw [if_pos ha, if_pos hk]; norm_num
        · exact absurd (hka.1 hk) ha
        · exact absurd (hka.2 ha) hk
        · rw [if_neg ha, if_neg hk]; norm_num
      calc sv p0 a * (y k a * sv p0 k * (starRingEnd ℂ) (y k b))
          = (sv p0 a * sv p0 k) * (y k a * (starRingEnd ℂ) (y k b)) := by ring
        _ = y k a * (starRingEnd ℂ) (y k b) := by rw [hs, one_mul]
    · rw [hy k a hka]
      ring
  unfold Ok
  rw [key]
  apply Matrix.PosDef.conjTranspose_mul_self
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have hdet : (y.map (starRingEnd ℂ)).det = starRingEnd ℂ y.det := (RingHom.map_det _ _).symm
  rw [hdet]
  exact (map_ne_zero _).2 hd
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
