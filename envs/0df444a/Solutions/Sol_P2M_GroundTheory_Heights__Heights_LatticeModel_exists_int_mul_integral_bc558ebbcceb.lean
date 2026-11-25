-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_exists_int_mul_integral_bc558ebbcceb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:38:24.523914+00:00
-- url     : https://prove2.me/submissions/d72454cb-eff3-4072-8fb7-be9c959dca57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_isAlgebraic_int_977159973bad

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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (x : K) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = n * x := by
  obtain ⟨n, s, hn, h⟩ := (isAlgebraic_int x).exists_smul_eq (𝓞 K)
  exact ⟨n, hn, s, by rw [← h, zsmul_eq_mul]⟩
end GroundTheory.Heights₂.Heights.LatticeModel
