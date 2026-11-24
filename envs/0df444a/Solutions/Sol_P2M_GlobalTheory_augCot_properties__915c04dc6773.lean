-- Prove2me | solution 1 for P2M_GlobalTheory_augCot_properties__915c04dc6773
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:36:17.377196+00:00
-- url     : https://prove2.me/submissions/9db09d5b-bcba-44d8-ade5-ecc952f27ae2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AugCot_map_comp
import Theorems.Thm_GlobalTheory_AugCot_map_surjective
import Theorems.Thm_GlobalTheory_AugCot_exact_kerMap_map
import Theorems.Thm_GlobalTheory_AugCot_map_bijective_of_etale
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_nonempty_basis_of_isStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AugCot_smooth_of_locally
import Theorems.Thm_GlobalTheory_AugCot_rankAtStalk_of_locally
import Theorems.Thm_GlobalTheory_AugCot_nonempty_basis_of_locally
import Theorems.Thm_GlobalTheory_AugCot_locally_iff_smoothOfRelativeDimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d

set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory
open AugCot
namespace GlobalTheory
namespace augCot_properties
theorem _root_.solution.{u} {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (ε : A →ₐ[R] R) :

    (∀ a : A, d ε a = (RingHom.ker ε).toCotangent
      ⟨a - algebraMap R A (ε a), by simp [RingHom.mem_ker]⟩) ∧

    (letI : Algebra A R := (ε : A →+* R).toAlgebra
     ∃ e : AugCot ε ≃ₗ[R] R ⊗[A] Ω[A⁄R],
      ∀ a, e (d ε a) = 1 ⊗ₜ KaehlerDifferential.D R A a) ∧

    (∀ (N : Type u) [AddCommGroup N] [Module R N],
      letI : Module A N := Module.compHom N (ε : A →+* R)
      haveI : IsScalarTower R A N := isScalarTower_of_smul_eq ε fun _ _ => rfl
      ∃ e : Derivation R A N ≃ₗ[R] (AugCot ε →ₗ[R] N), ∀ D a, e D (d ε a) = D a) ∧

    (∀ (N : Type u) [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N],
      ∃ e : {φ : A →ₐ[R] TrivSqZeroExt R N // (TrivSqZeroExt.fstHom R R N).comp φ = ε} ≃
        (AugCot ε →ₗ[R] N), ∀ φ a, e φ (d ε a) = (φ.1 a).snd) ∧

    (∀ (R' : Type u) [CommRing R'] [Algebra R R'],
      (∀ r a, baseChangeAug R' ε (r ⊗ₜ a) = r * algebraMap R R' (ε a)) ∧
      ∃ e : R' ⊗[R] AugCot ε ≃ₗ[R'] AugCot (baseChangeAug R' ε),
        ∀ r a, e (r ⊗ₜ d ε a) = r • d _ (1 ⊗ₜ a)) ∧

    (map (AlgHom.id R A) (AlgHom.comp_id ε) = LinearMap.id) ∧
    (∀ (B : Type u) [CommRing B] [Algebra R B] (εB : B →ₐ[R] R) (φ : A →ₐ[R] B)
      (h : εB.comp φ = ε),
      (∀ a, map φ h (d ε a) = d εB (φ a)) ∧
      (∀ (C : Type u) [CommRing C] [Algebra R C] (εC : C →ₐ[R] R) (ψ : B →ₐ[R] C)
        (h' : εC.comp ψ = εB) (h'' : εC.comp (ψ.comp φ) = ε),
        map (ψ.comp φ) h'' = map ψ h' ∘ₗ map φ h) ∧

      ((φ : A →+* B).Etale → Function.Bijective (map φ h)) ∧

      (Function.Surjective φ →
        (∀ x : RingHom.ker φ, kerMap φ h x = (RingHom.ker ε).toCotangent ⟨x, ker_le φ h x.2⟩) ∧
        Function.Exact (kerMap φ h) (map φ h) ∧ Function.Surjective (map φ h))) ∧

    (∀ (f : A) (B : Type u) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
      [IsLocalization.Away f B],
      (IsUnit (ε f) → ∃ εB : B →ₐ[R] R, εB.comp (IsScalarTower.toAlgHom R A B) = ε) ∧
      ∀ (εB : B →ₐ[R] R) (h : εB.comp (IsScalarTower.toAlgHom R A B) = ε),
        Function.Bijective (map _ h)) ∧

    (∀ (B : Type u) [CommRing B] [Algebra R B] (εB : B →ₐ[R] R),
      ∃ e : AugCot (Algebra.TensorProduct.productMap ε εB) ≃ₗ[R] AugCot ε × AugCot εB,
        ∀ a b, e (d _ (a ⊗ₜ b)) = (εB b • d ε a, ε a • d εB b)) ∧

    (Algebra.Smooth R A → Module.Finite R (AugCot ε) ∧ Module.Projective R (AugCot ε) ∧
      (IsLocalRing R → Module.Free R (AugCot ε))) ∧
    (Algebra.IsStandardSmooth R A → Module.Free R (AugCot ε)) ∧
    (∀ n : ℕ, Algebra.IsStandardSmoothOfRelativeDimension n R A →
      Nonempty (Module.Basis (Fin n) R (AugCot ε))) ∧
    (∀ n : ℕ, AlgebraicGeometry.SmoothOfRelativeDimension n
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R A))) →
      Algebra.Smooth R A ∧ (∀ p : PrimeSpectrum R, Module.rankAtStalk (AugCot ε) p = n) ∧
      (IsLocalRing R → Nonempty (Module.Basis (Fin n) R (AugCot ε)))) := by
  refine ⟨fun a => rfl, ?_, fun N _ _ => ?_, fun N _ _ _ _ => ⟨sqZeroEquiv ε N, sqZeroEquiv_d ε⟩,
    fun R' _ _ => ⟨baseChangeAug_tmul, baseChangeEquiv R' ε, baseChangeEquiv_tmul_d⟩, map_id,
    fun B _ _ εB φ h => ⟨map_d φ h, fun C _ _ εC ψ h' h'' => map_comp φ ψ h h' h'',
      map_bijective_of_etale φ h,
      fun hφ => ⟨fun _ => rfl, exact_kerMap_map φ h hφ, map_surjective φ h hφ⟩⟩,
    fun f B _ _ _ _ _ => ⟨fun hf => ⟨awayAug B ε f hf, awayAug_comp f hf⟩,
      fun εB h => map_bijective_of_isLocalization (Submonoid.powers f) h⟩,
    fun B _ _ εB => ⟨tensorEquiv ε εB, tensorEquiv_d_tmul⟩,
    fun _ => ⟨inferInstance, inferInstance, fun _ => inferInstance⟩, fun _ => inferInstance,
    fun n _ => nonempty_basis_of_isStandardSmoothOfRelativeDimension ε n, fun n hn => ?_⟩
  · letI : Algebra A R := (ε : A →+* R).toAlgebra
    exact ⟨kaehlerEquiv ε fun _ => rfl, kaehlerEquiv_d ε _⟩
  · letI : Module A N := Module.compHom N (ε : A →+* R)
    haveI : IsScalarTower R A N := isScalarTower_of_smul_eq ε fun _ _ => rfl
    exact ⟨derivationEquiv ε fun _ _ => rfl, derivationEquiv_d ε _⟩
  · have h := locally_iff_smoothOfRelativeDimension.2 hn
    exact ⟨smooth_of_locally h, rankAtStalk_of_locally ε h,
      fun _ => nonempty_basis_of_locally ε h⟩
end augCot_properties
end GlobalTheory
