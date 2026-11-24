-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_isAlgebraic_of_adjoin_b50a6ba2f986
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:13.02072+00:00
-- url     : https://prove2.me/submissions/7a920ffa-9712-4829-8f8b-86a345d43c98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualArithmeticVariety
variable {K : Type} [Field K]
namespace GroundTheory.Heights₂.Heights.DualArithmeticVariety
theorem _root_.solution {m : ℕ} (S : Set (ProjField K m))
    (h : ∀ z, z ∈ IntermediateField.adjoin K S) :
    Algebra.IsAlgebraic (Algebra.adjoin K S) (ProjField K m) := by
  rw [← IntermediateField.isAlgebraic_adjoin_iff_top]
  exact ⟨fun z => isAlgebraic_algebraMap (⟨z, h z⟩ : IntermediateField.adjoin K S)⟩
end GroundTheory.Heights₂.Heights.DualArithmeticVariety
