-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_length_eq_sum_b684c5e7ef89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:21.304436+00:00
-- url     : https://prove2.me/submissions/15b15ec9-5dff-4f93-9a01-c8c9b2283e25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LengthSumLocalizations
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_isFiniteLength_of_atPrime_355534cb01cc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_pi_mk_injective_9e4e7064f707
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_length_eq_sum_of_isFiniteLength_31a97d0ec527

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
    (N : Type*) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N] :
    Module.length A N = ∑ i, Module.length (C i) (C i ⊗[B] N) * Module.length A (B ⧸ 𝔪 i) := by
  by_cases hN : IsFiniteLength B N
  · exact length_eq_sum_of_isFiniteLength 𝔪 C hinj hall A N hN
  have hA : Module.length A N = ⊤ := by
    by_contra hA
    apply hN
    have hA' := isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hA)
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact hA'.imp (isNoetherian_of_tower A) (isArtinian_of_tower A)
  obtain ⟨i, hi⟩ : ∃ i, ¬ IsFiniteLength (C i) (C i ⊗[B] N) := by
    by_contra! h
    apply hN
    have hpi : Module.length B (∀ i, C i ⊗[B] N) ≠ ⊤ := by
      rw [Module.length_pi_of_fintype, ENat.sum_ne_top]
      exact fun i _ => Module.length_ne_top_iff.mpr
        (isFiniteLength_of_atPrime (𝔪 i) (C i) _ (h i))
    rw [← Module.length_ne_top_iff]
    exact ne_top_of_le_ne_top hpi (Module.length_le_of_injective _ (pi_mk_injective 𝔪 C hall N))
  have : Nontrivial (B ⧸ 𝔪 i) := Ideal.Quotient.nontrivial_iff.mpr (h𝔪 i).ne_top
  have hd : Module.length A (B ⧸ 𝔪 i) ≠ 0 := (Module.length_pos (R := A)).ne'
  have hti : Module.length (C i) (C i ⊗[B] N) = ⊤ := by
    by_contra h'
    exact hi (Module.length_ne_top_iff.mp h')
  rw [hA, eq_comm, ← top_le_iff]
  calc (⊤ : ℕ∞) = Module.length (C i) (C i ⊗[B] N) * Module.length A (B ⧸ 𝔪 i) := by
        rw [hti, ENat.top_mul hd]
    _ ≤ _ := Finset.single_le_sum (f := fun i =>
        Module.length (C i) (C i ⊗[B] N) * Module.length A (B ⧸ 𝔪 i))
        (fun _ _ => zero_le) (Finset.mem_univ i)
end GroundTheory.Heights₂.Heights.FieldNumbers.LengthSumLocalizations
