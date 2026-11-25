-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_length_eq_sum_of_isFiniteLength_31a97d0ec527
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:20.66481+00:00
-- url     : https://prove2.me/submissions/0ba02ec4-656b-4df2-9a08-cfe311886c71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LengthSumLocalizations
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_length_tensor_quot_434076816485

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open Module TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.FieldNumbers.LengthSumLocalizations
variable {B : Type*} [CommRing B]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (𝔪 : ι → Ideal B) [h𝔪 : ∀ i, (𝔪 i).IsMaximal]
  (C : ι → Type*) [∀ i, CommRing (C i)] [∀ i, Algebra B (C i)]
  [∀ i, IsLocalization.AtPrime (C i) (𝔪 i)]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.LengthSumLocalizations
theorem _root_.solution (hinj : Function.Injective 𝔪)
    (hall : ∀ M : Ideal B, M.IsMaximal → ∃ i, M = 𝔪 i) (A : Type*) [CommRing A] [Algebra A B]
    (N : Type*) [AddCommGroup N] [Module B N] [instA : Module A N] [instT : IsScalarTower A B N]
    (hN : IsFiniteLength B N) :
    Module.length A N = ∑ i, Module.length (C i) (C i ⊗[B] N) * Module.length A (B ⧸ 𝔪 i) := by
  revert instA instT
  induction hN with
  | of_subsingleton => intro _ _; simp [Module.length_eq_zero]
  | @of_simple_quotient M _ _ P hs hP ih =>
    intro _ _
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    obtain ⟨j, rfl⟩ := hall I hI
    let f : P →ₗ[B] M := P.subtype
    let g : M →ₗ[B] B ⧸ 𝔪 j := e.toLinearMap ∘ₗ P.mkQ
    have hf : Function.Injective f := P.subtype_injective
    have hg : Function.Surjective g := e.surjective.comp P.mkQ_surjective
    have hfg : Function.Exact f g := LinearMap.exact_iff.mpr (by
      rw [LinearEquiv.ker_comp, Submodule.ker_mkQ, Submodule.range_subtype])
    have key : ∀ i, Module.length (C i) (C i ⊗[B] M) =
        Module.length (C i) (C i ⊗[B] P) + if i = j then 1 else 0 := by
      intro i
      have : Module.Flat B (C i) := IsLocalization.flat (C i) (𝔪 i).primeCompl
      rw [Module.length_eq_add_of_exact (AlgebraTensorModule.lTensor (C i) (C i) f)
        (AlgebraTensorModule.lTensor (C i) (C i) g)
        (Module.Flat.lTensor_preserves_injective_linearMap f hf)
        (LinearMap.lTensor_surjective (C i) hg) (Module.Flat.lTensor_exact (C i) hfg),
        length_tensor_quot 𝔪 C hinj i j]
    rw [Module.length_eq_add_of_exact (f.restrictScalars A) (g.restrictScalars A) hf hg hfg, ih]
    simp only [key, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
end GroundTheory.Heights₂.Heights.FieldNumbers.LengthSumLocalizations
