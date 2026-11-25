-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_hermChartPot_conj_179aa3d33806
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:07:28.099875+00:00
-- url     : https://prove2.me/submissions/cade19f5-1820-4731-9cff-76c8f744e0d7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartMassInvariant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_mulVec_cons_of_row_zero_5b804bab8996

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
variable {e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
theorem _root_.solution (M T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef)
    (hT : ∀ j : Fin e, T 0 j.succ = 0) (ht : T 0 0 ≠ 0) (y : Fin e → ℂ) :
    hermChartPot (Tᴴ * M * T) y =
      hermChartPot M ((T 0 0)⁻¹ • (fun i => T i.succ 0) + ((T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ) *ᵥ y) +
        Real.log ‖T 0 0‖ := by
  set w : Fin e → ℂ := (T 0 0)⁻¹ • (fun i => T i.succ 0) + ((T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ) *ᵥ y with hw
  set u : Fin (e + 1) → ℂ := Fin.cons 1 w with hu
  have hTv : T *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ) = T 0 0 • u := by
    rw [mulVec_cons_of_row_zero T hT]
    funext p
    refine Fin.cases ?_ (fun i => ?_) p
    · simp [u]
    · have hm : (((T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ) *ᵥ y) i =
          (T 0 0)⁻¹ * ((T.submatrix Fin.succ Fin.succ) *ᵥ y) i := by
        simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      simp only [u, w, Fin.cons_succ, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hm]
      field_simp
  have hq : star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ ((Tᴴ * M * T) *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)) =
      (Complex.normSq (T 0 0) : ℂ) * (star u ⬝ᵥ (M *ᵥ u)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, hTv, star_smul, mulVec_smul,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.normSq_eq_conj_mul_self,
      starRingEnd_apply]
    ring
  have hu0 : u ≠ 0 := fun h => by
    have := congrFun h 0
    simp [u] at this
  have hx : 0 < (star u ⬝ᵥ (M *ᵥ u)).re := (Complex.pos_iff.mp (hM.dotProduct_mulVec_pos hu0)).1
  simp only [hermChartPot]
  rw [hq, Complex.re_ofReal_mul, Real.sqrt_mul (Complex.normSq_nonneg (T 0 0)), ← Complex.norm_def,
    Real.log_mul (norm_ne_zero_iff.mpr ht) (Real.sqrt_pos.mpr hx).ne']
  ring
end GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
