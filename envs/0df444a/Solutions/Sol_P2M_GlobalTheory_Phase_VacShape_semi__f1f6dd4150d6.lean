-- Prove2me | solution 1 for P2M_GlobalTheory_Phase_VacShape_semi__f1f6dd4150d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:58:12.196366+00:00
-- url     : https://prove2.me/submissions/e58ec130-3cfa-4306-9aee-ddc580b08939

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SelfDualVacuumGaussianShapeRootOfUnityPhases
import Theorems.Thm_GlobalTheory_SW_Vac_om_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.VacShape
open GlobalTheory.SW.Vac
variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
  {A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ)} {ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ}
  {φ : Matrix κ ι ℚ → ℂ}
omit [DecidableEq ι]
namespace GlobalTheory.Phase.VacShape
theorem _root_.solution (h : VacS A ε φ) : ∀ y ∈ A, ∀ y' ∈ A,
    ε (y + y') = ε y * ε y' * ex (pr y.1 y'.2 - pr y'.1 y.2) := by
  intro y hy y' hy'
  rw [h.semi y hy y' hy', om, om_eq, ex]
end GlobalTheory.Phase.VacShape
