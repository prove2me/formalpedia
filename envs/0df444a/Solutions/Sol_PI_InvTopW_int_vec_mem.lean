-- Prove2me | solution 1 for PI.InvTopW.int_vec_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:51:43.146808+00:00
-- url     : https://prove2.me/submissions/295c399e-85bb-47d2-a6f7-249575554653

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LatticeOfEntriesIntegral
import Theorems.Thm_PI_InvTopW_single_mem_lat
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
    (hs : ∀ j, (c : E) • Pi.single j (1 : E) ∈ L) (u : Fin n → E ⊗[F] Formalism.MainNotions.S.Af F)
    (hu : ∀ i, u i ∈ Formalism.MainNotions.S.IntAf F E) :
    (fun i => (c : E ⊗[F] Formalism.MainNotions.S.Af F) * u i) ∈ Formalism.MainNotions.S.lamAf (F := F) L := by
  have h : (fun i => (c : E ⊗[F] Formalism.MainNotions.S.Af F) * u i) =
      ∑ j, (⟨u j, hu j⟩ : Formalism.MainNotions.S.IntAf F E) • Pi.single j (c : E ⊗[F] Formalism.MainNotions.S.Af F) := by
    funext i
    rw [Finset.sum_apply]
    simp [Pi.single_apply, Subring.smul_def, mul_comm]
  rw [h]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (single_mem_lat L c hs j)
end PI.InvTopW
