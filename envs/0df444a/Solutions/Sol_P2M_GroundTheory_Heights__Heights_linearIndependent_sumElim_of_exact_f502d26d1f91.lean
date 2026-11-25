-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_linearIndependent_sumElim_of_exact_f502d26d1f91
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:34:47.018023+00:00
-- url     : https://prove2.me/submissions/8e2ec529-4f08-4f64-bac9-c52820e8ddc9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {A B C : Type*} [AddCommGroup A] [Module (𝓞 K) A] [AddCommGroup B] [Module (𝓞 K) B]
  [AddCommGroup C] [Module (𝓞 K) C] {i : A →ₗ[𝓞 K] B} {p : B →ₗ[𝓞 K] C}
variable {m n : Type*} [Fintype m] [Fintype n]
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (hi : Function.Injective i) (hex : Function.Exact i p)
    {s' : m → A} {s'' : n → C} {u : n → B} (hu : ∀ j, p (u j) = s'' j)
    (hs' : LinearIndependent (𝓞 K) s') (hs'' : LinearIndependent (𝓞 K) s'') :
    LinearIndependent (𝓞 K) (Sum.elim (fun k ↦ i (s' k)) u) := by
  rw [Fintype.linearIndependent_iff] at hs' hs'' ⊢
  intro g hg
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg
  have h2 : ∑ j, g (Sum.inr j) • s'' j = 0 := by
    have := congrArg p hg
    simpa [map_add, map_sum, map_smul, hex.apply_apply_eq_zero, hu] using this
  have hr := hs'' _ h2
  have h1 : ∑ k, g (Sum.inl k) • s' k = 0 := by
    apply hi
    simp only [hr, zero_smul, Finset.sum_const_zero, add_zero] at hg
    rw [map_sum, map_zero]
    simpa [map_smul] using hg
  have hl := hs' _ h1
  rintro (k | j)
  exacts [hl k, hr j]
end GroundTheory.Heights₂.Heights
