-- Prove2me | solution 1 for PI.ScRefExists.GlueA.sigA_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:36:37.818556+00:00
-- url     : https://prove2.me/submissions/967a353f-e88b-4564-b142-d54d09826789

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Theorems.Thm_PI_ScRefExists_GlueA_inclE_tmul
import Theorems.Thm_PI_ScRefExists_GlueA_star_int
import Theorems.Thm_PI_ScRefExists_GlueA_inclE_mem
import Theorems.Thm_PI_ScRefExists_GlueA_sigA_inclE
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
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GlueA
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.GlueA
theorem _root_.solution {x : (I.E ⊗[I.F] Af I.F)} (hx : x ∈ IntAf I.F I.E) : sigA I x ∈ IntAf I.F I.E := by
  have e1 : ∀ r : Af I.F, sigA I ((1 : I.E) ⊗ₜ[I.F] r) = (1 : I.E) ⊗ₜ[I.F] r := fun r => by
    first
      | simp only [sigA, Formalism.UG.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq]
      | (show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) ((1 : I.E) ⊗ₜ[I.F] r) = _
         rw [Algebra.TensorProduct.map_tmul, map_one]
         rfl)
      | simp [sigA, Formalism.UG.sigR]
  have h : IntAf I.F I.E ≤ (IntAf I.F I.E).comap (sigA I) := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro y (⟨⟨e, he⟩, rfl⟩ | ⟨⟨r, hr⟩, rfl⟩)
    · show sigA I (e ⊗ₜ[I.F] (1 : Af I.F)) ∈ IntAf I.F I.E
      rw [← inclE_tmul, sigA_inclE]
      obtain ⟨t, rfl⟩ := he
      exact inclE_mem I (star_int I t)
    · show sigA I ((1 : I.E) ⊗ₜ[I.F] (r : Af I.F)) ∈ IntAf I.F I.E
      rw [e1]
      exact Subring.subset_closure (Set.mem_union_right _ ⟨⟨r, hr⟩, rfl⟩)
  exact h hx
end PI.ScRefExists.GlueA
