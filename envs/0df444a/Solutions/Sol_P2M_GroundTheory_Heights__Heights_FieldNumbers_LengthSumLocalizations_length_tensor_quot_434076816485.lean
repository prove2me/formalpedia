-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_length_tensor_quot_434076816485
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:34.291735+00:00
-- url     : https://prove2.me/submissions/5d32a356-1b40-4841-bd37-7901812fac3c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LengthSumLocalizations

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
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.LengthSumLocalizations
theorem _root_.solution (hinj : Function.Injective 𝔪) (i j : ι) :
    Module.length (C i) (C i ⊗[B] (B ⧸ 𝔪 j)) = if i = j then 1 else 0 := by
  have : IsLocalRing (C i) := IsLocalization.AtPrime.isLocalRing (C i) (𝔪 i)
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (C i) (𝔪 j)).toLinearEquiv.length_eq]
  split_ifs with h
  · subst h
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal (𝔪 i) (C i)]
    have : IsSimpleModule (C i) (C i ⧸ IsLocalRing.maximalIdeal (C i)) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _
  · have hne : ¬ 𝔪 j ≤ 𝔪 i := fun hle =>
      h (hinj ((h𝔪 j).eq_of_le (h𝔪 i).ne_top hle)).symm
    obtain ⟨x, hxj, hxi⟩ := Set.not_subset.mp hne
    have htop : (𝔪 j).map (algebraMap B (C i)) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hxj)
        (IsLocalization.map_units (C i) (⟨x, hxi⟩ : (𝔪 i).primeCompl))
    rw [htop, Module.length_eq_zero_iff]
    exact Ideal.Quotient.subsingleton_iff.mpr rfl
end GroundTheory.Heights₂.Heights.FieldNumbers.LengthSumLocalizations
