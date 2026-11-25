-- Prove2me | solution 1 for PI.InvTopW.single_mem_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:59.919304+00:00
-- url     : https://prove2.me/submissions/923c7138-a879-4d27-8218-ba55f279af8f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LatticeOfEntriesIntegral
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.InvTopW
theorem _root_.solution {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (c : ℕ)
    (hs : ∀ j, (c : E) • Pi.single j (1 : E) ∈ L) (j : Fin n) :
    Pi.single j (c : E ⊗[F] Formalism.MainNotions.S.Af F) ∈ Formalism.MainNotions.S.lamAf (F := F) L := by
  have hx : (fun i => Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F)
      (((c : E) • Pi.single j (1 : E) : Fin n → E) i)) = Pi.single j (c : E ⊗[F] Formalism.MainNotions.S.Af F) := by
    funext i
    by_cases h : i = j
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  rw [← hx]
  unfold Formalism.MainNotions.S.lamAf
  exact Submodule.subset_span ⟨⟨_, hs j⟩, rfl⟩
end PI.InvTopW
