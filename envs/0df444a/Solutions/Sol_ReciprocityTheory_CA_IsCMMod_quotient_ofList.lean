-- Prove2me | solution 1 for ReciprocityTheory.CA.IsCMMod.quotient_ofList
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:06:21.767891+00:00
-- url     : https://prove2.me/submissions/a7bc28dd-7319-498c-a09a-3dfc2c2ab80c

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_AssDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
import Theorems.Thm_ReciprocityTheory_CA_IsCMMod_quotSMulTop
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_quotSMulTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
private theorem unm_modDepthGE_congr {N : Type*} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) {n : ℕ} (h : ModDepthGE R M n) : ModDepthGE R N n := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := id h
  unfold ModDepthGE
  refine ⟨rs, hlen, hmem, ?_⟩
  first
  | exact (LinearEquiv.isRegular_congr e rs).mp hreg
  | exact (e.isRegular_congr rs).mp hreg
  | exact (LinearEquiv.isRegular_congr' e rs).mp hreg
private theorem unm_isCMMod_congr {N : Type*} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (h : IsCMMod R M) : IsCMMod R N := by
  obtain ⟨hR, hfin, n, hdim, hdep⟩ := id h
  haveI := hfin
  have hs : Module.support R N = Module.support R M :=
    (Module.support_subset_of_surjective e.toLinearMap e.surjective).antisymm
      (Module.support_subset_of_surjective e.symm.toLinearMap e.symm.surjective)
  unfold IsCMMod
  refine ⟨hR, Module.Finite.equiv e, n, ?_, unm_modDepthGE_congr e hdep⟩
  rw [← hdim]
  first
  | (unfold Module.supportDim; rw [hs])
  | (simp only [Module.supportDim, hs])
  | exact (Module.supportDim_eq_of_equiv e).symm
end ReciprocityTheory.CA
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
namespace ReciprocityTheory.CA
namespace IsCMMod
theorem _root_.solution (h : IsCMMod R M) {rs : List R}
    (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R) (reg : IsRegular M rs) :
    IsCMMod R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) := by
  induction rs generalizing M with
  | nil =>
    refine unm_isCMMod_congr (Submodule.quotEquivOfEqBot _ ?_).symm h
    first | simp | simp [Ideal.ofList]
  | cons r rs ih =>
    rw [RingTheory.Sequence.isRegular_cons_iff] at reg
    have hr : r ∈ maximalIdeal R := hrs r (by simp)
    have h1 := h.quotSMulTop hr reg.1
    have h2 := ih h1 (fun s hs => hrs s (by simp [hs])) reg.2
    exact unm_isCMMod_congr
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M r rs).symm h2
end IsCMMod
end ReciprocityTheory.CA
