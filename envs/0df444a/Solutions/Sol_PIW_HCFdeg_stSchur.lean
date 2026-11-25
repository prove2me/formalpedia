-- Prove2me | solution 1 for PIW.HCFdeg.stSchur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:43:04.685798+00:00
-- url     : https://prove2.me/submissions/c766ac03-6253-4743-8978-7dee2ba1ec1f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_CommuteStar
import Theorems.Thm_PIW_HCFdeg_commute_star
import Theorems.Thm_PIW_HCFdeg_sa_scalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open scoped InnerProductSpace ComplexStarModule
open ContinuousLinearMap
namespace PIW.HCFdeg
theorem _root_.solution : StSchur := by
  intro G H iG iH iI iC π hπ hirr T hT
  have hc : ∀ g, Commute T (π g) := fun g => by
    first
    | exact hT g
    | simpa [Commute, SemiconjBy, ContinuousLinearMap.mul_def] using hT g
  have hcs : ∀ g, Commute (star T) (π g) := fun g => commute_star π hπ T hc g
  obtain ⟨r1, h1⟩ := sa_scalar π hirr (ℜ T : H →L[ℂ] H) (ℜ T).2 (fun g => by
    rw [realPart_apply_coe]
    exact ((hc g).add_left (hcs g)).smul_left _)
  obtain ⟨r2, h2⟩ := sa_scalar π hirr (ℑ T : H →L[ℂ] H) (ℑ T).2 (fun g => by
    rw [imaginaryPart_apply_coe]
    exact (((hc g).sub_left (hcs g)).smul_left _).smul_left _)
  refine ⟨(r1 : ℂ) + Complex.I * r2, ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T]
  rw [h1, h2]
  ext v
  simp [Algebra.algebraMap_eq_smul_one, add_smul, mul_smul]
end PIW.HCFdeg
