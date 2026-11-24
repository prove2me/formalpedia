-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RecQOfRecursion_exists_C_mul_of_isChowForm_6628fc869e62
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:17.02925+00:00
-- url     : https://prove2.me/submissions/504ae016-7fd4-4292-9c11-10fa1af57923

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MemConePointsSpanX0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_FiniteSupportLogCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MemMinimalPrimesOfMemFundCycleSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PObjectsDivCycleGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDivSuppHorizontalArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_HeightMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRecQOfRecursion

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
noncomputable section
open GroundTheory.Heights₂.Heights.RecQOfRecursion
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt geoNum charOf arInt)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.RecQOfRecursion
theorem _root_.solution {F : Type*} [Field F] {I : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {f g : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (hg : IsChowForm I k g) :
    ∃ r : F, r ≠ 0 ∧ g = C r * f := by
  obtain ⟨a, rfl⟩ : f ∣ g := (hf.2 g).mp ((hg.2 g).mpr dvd_rfl)
  obtain ⟨b, hb⟩ : f * a ∣ f := (hg.2 f).mp ((hf.2 f).mpr dvd_rfl)
  have hab : a * b = 1 := by
    apply mul_left_cancel₀ hf.1
    rw [mul_one, ← mul_assoc, ← hb]
  obtain ⟨r, hr, rfl⟩ := (isUnit_iff_eq_C_of_isReduced (P := a)).mp (isUnit_iff_exists_inv.mpr ⟨b, hab⟩)
  exact ⟨r, hr.ne_zero, mul_comm _ _⟩
end GroundTheory.Heights₂.Heights.RecQOfRecursion
