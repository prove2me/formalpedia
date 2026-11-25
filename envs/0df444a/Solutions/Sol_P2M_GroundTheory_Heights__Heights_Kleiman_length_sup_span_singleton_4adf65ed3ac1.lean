-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_length_sup_span_singleton_4adf65ed3ac1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:02:50.338802+00:00
-- url     : https://prove2.me/submissions/e92d11f8-91e6-441c-9a5f-1cdac9103a61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {R : Type*} [CommRing R] {L : Type*} [AddCommGroup L] [Module R L]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (A : Submodule R L) (y : L) :
    Module.length R (A ⊔ Submodule.span R {y} : Submodule R L) =
      Module.length R A + Module.length R (R ⧸ colonIdeal A y) := by
  set B : Submodule R L := A ⊔ Submodule.span R {y}
  let A' : Submodule R B := A.comap B.subtype
  have e1 : Module.length R B = Module.length R A' + Module.length R (B ⧸ A') :=
    Module.length_eq_add_of_exact A'.subtype A'.mkQ A'.injective_subtype A'.mkQ_surjective
      (LinearMap.exact_subtype_mkQ A')
  let yB : B := ⟨y, Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)⟩
  let φ : R →ₗ[R] B ⧸ A' := A'.mkQ ∘ₗ LinearMap.toSpanSingleton R B yB
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨⟨m, hm⟩, rfl⟩ := A'.mkQ_surjective z
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hb
    refine ⟨r, ?_⟩
    simp only [φ, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    change (r • y - (a + r • y) : L) ∈ A
    simpa using A.neg_mem ha
  have hker : LinearMap.ker φ = colonIdeal A y := by
    ext r
    simp only [LinearMap.mem_ker, φ, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, mem_colonIdeal]
    rfl
  have e3 : (R ⧸ colonIdeal A y) ≃ₗ[R] B ⧸ A' :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hφ)
  rw [e1, (Submodule.comapSubtypeEquivOfLe (le_sup_left : A ≤ B)).length_eq, e3.length_eq]
end GroundTheory.Heights₂.Heights.Kleiman
