-- Prove2me | solution 1 for QECCertificates.exists_leftInverse_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:45.789779+00:00
-- url     : https://prove2.me/submissions/b6b78efa-e6f8-4c69-902a-f9f781ac5b8c

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {p q r s a b : ℕ}
namespace QECCertificates
theorem _root_.solution {u : Fin a → Vec p}
    (hu : LinearIndependent (ZMod 2) u) :
    ∃ L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2), ∀ c : Fin a → ZMod 2, L (∑ k, c k • u k) = c := by
  classical
  let φ : (Fin a → ZMod 2) →ₗ[ZMod 2] Vec p :=
    { toFun := fun c => ∑ k, c k • u k
      map_add' := fun c d => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun t c => by
        simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, RingHom.id_apply,
          smul_eq_mul] }
  have hker : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    funext k
    exact Fintype.linearIndependent_iff.mp hu c hc k
  obtain ⟨L, hL⟩ := φ.exists_leftInverse_of_injective hker
  exact ⟨L, fun c => LinearMap.congr_fun hL c⟩
end QECCertificates
