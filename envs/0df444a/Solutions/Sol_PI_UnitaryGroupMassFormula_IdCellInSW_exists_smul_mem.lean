-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.IdCellInSW.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:40.098339+00:00
-- url     : https://prove2.me/submissions/ecb484ff-12fb-42f5-b348-eaebd20c2506

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Lemmata_GeneralBFactThirdTail_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdentityCellTrace_ExistsSmulMem
import Theorems.Thm_P2M_Bl_general_b_fact_third_______goal1_4ace80324855


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IdCellInSW
variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
namespace PI.UnitaryGroupMassFormula.IdCellInSW
theorem _root_.solution (Λ : Submodule (𝓞 E) V) (hsp : Submodule.span E (Λ : Set V) = ⊤) (x : V) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ Λ := by
  first | exact Bl.general_b_fact_third''''''.goal1 .. | (apply Bl.general_b_fact_third''''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third''''''.goal1 <;> assumption)
end PI.UnitaryGroupMassFormula.IdCellInSW
