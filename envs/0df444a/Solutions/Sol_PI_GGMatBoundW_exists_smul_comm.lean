-- Prove2me | solution 1 for PI.GGMatBoundW.exists_smul_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:50.875801+00:00
-- url     : https://prove2.me/submissions/44e9007b-172c-414c-993a-0f540b263e58

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_GammaMatrixInverse
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_MatrixCoefficientEquation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {G : Type} [Group G] {X : Type} [MulAction Gᵐᵒᵖ X]
namespace PI.GGMatBoundW
theorem _root_.solution (i j : X) : (∃ x : Gᵐᵒᵖ, x • j = i) ↔ ∃ x : Gᵐᵒᵖ, x • i = j :=
  ⟨fun ⟨x, hx⟩ => ⟨x⁻¹, by rw [← hx, inv_smul_smul]⟩, fun ⟨x, hx⟩ => ⟨x⁻¹, by rw [← hx, inv_smul_smul]⟩⟩
end PI.GGMatBoundW
