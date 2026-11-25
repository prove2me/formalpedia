-- Prove2me | solution 1 for PI.ScRefExists.LG.locGlob_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:09:09.510837+00:00
-- url     : https://prove2.me/submissions/92a4c0db-d91e-436b-be3f-c2a987fa548d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_LocGlob
import Theorems.Thm_PI_ScRefExists_LG_int_of_mem_intAd
import Theorems.Thm_PI_ScRefExists_LG_Phi_tmul
import Theorems.Thm_PI_ScRefExists_LG_Phi_mem
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
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
open PI PI.ScRefExists PI.ScRefExists.LG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.ScRefExists.LG
theorem _root_.solution (t : E) (ht : Formalism.UG.inclE (F := F) (Af F) t ∈ IntAf F E) :
    ∃ s : 𝓞 E, algebraMap (𝓞 E) E s = t := by
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have hd : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero (𝓞 F) F h1
  have hmem : t ∈ FractionalIdeal.dual (𝓞 F) F
      (FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E)) := by
    rw [FractionalIdeal.mem_dual hd]
    intro a ha
    rw [FractionalIdeal.mem_dual h1] at ha
    have ha' : ∀ o : 𝓞 E, Algebra.trace F E (a * algebraMap (𝓞 E) E o) ∈
        (algebraMap (𝓞 F) F).range := by
      intro o
      have := ha (algebraMap (𝓞 E) E o) ((FractionalIdeal.mem_one_iff (𝓞 E)⁰).mpr ⟨o, rfl⟩)
      simpa [Algebra.traceForm_apply] using this
    have hP := Phi_mem a ha' ht
    have hx : Phi a (Formalism.UG.inclE (F := F) (Af F) t) =
        algebraMap F (Af F) (Algebra.trace F E (a * t)) := by
      simp [Formalism.UG.inclE, Phi_tmul]
    rw [hx] at hP
    have := int_of_mem_intAd _ hP
    simpa [Algebra.traceForm_apply, mul_comm] using this
  rw [FractionalIdeal.dual_dual] at hmem
  exact (FractionalIdeal.mem_one_iff (𝓞 E)⁰).mp hmem
end PI.ScRefExists.LG
