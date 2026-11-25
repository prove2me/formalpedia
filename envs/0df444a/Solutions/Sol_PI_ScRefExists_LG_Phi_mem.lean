-- Prove2me | solution 1 for PI.ScRefExists.LG.Phi_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:42:53.482447+00:00
-- url     : https://prove2.me/submissions/fc5550a6-bb4c-4f91-a47d-7b68a8e09e67

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_LocGlob
import Theorems.Thm_PI_ScRefExists_LG_int_mem_intAd
import Theorems.Thm_PI_ScRefExists_LG_Phi_tmul
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
theorem _root_.solution (a : E) (ha : ∀ o : 𝓞 E, Algebra.trace F E (a * algebraMap (𝓞 E) E o) ∈
    (algebraMap (𝓞 F) F).range) {y : E ⊗[F] Af F} (hy : y ∈ IntAf F E) :
    Phi a y ∈ Formalism.UG.intAd F := by
  have hy' : y ∈ AddSubgroup.closure ((Submonoid.closure
      (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪
        Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F))) : Set _)) :=
    Subring.mem_closure_iff.mp hy
  have hle : Submonoid.closure
      (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪
        Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F))) ≤ (Gens : Submonoid _) := by
    rw [Submonoid.closure_le]
    rintro _ (⟨⟨x, o, rfl⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · exact ⟨o, 1, one_mem _, rfl⟩
    · exact ⟨1, c, hc, by simp⟩
  have hy2 := AddSubgroup.closure_mono hle hy'
  clear hy hy' hle
  induction hy2 using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨o, c, hc, rfl⟩ := hx
    rw [Phi_tmul]
    obtain ⟨r, hr⟩ := ha o
    rw [← hr]
    exact mul_mem (int_mem_intAd r) hc
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
end PI.ScRefExists.LG
