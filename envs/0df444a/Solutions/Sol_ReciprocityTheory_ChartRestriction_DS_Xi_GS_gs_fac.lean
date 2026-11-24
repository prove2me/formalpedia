-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.gs_fac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:19:18.218104+00:00
-- url     : https://prove2.me/submissions/73e58d2b-0e15-4f10-aaea-04ca8a89cc45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix InnerProductSpace
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {n m : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS
theorem _root_.solution (w : Fin m → EuclideanSpace ℂ (Fin n)) (hw : LinearIndependent ℂ w) :
    ∃ (u : Fin m → EuclideanSpace ℂ (Fin n)) (τ : Matrix (Fin m) (Fin m) ℂ), Orthonormal ℂ u ∧
      τ.BlockTriangular id ∧ (∀ j, τ j j ≠ 0) ∧ (∀ a, w a = ∑ b, τ b a • u b) ∧
      ∀ a, u a ∈ Submodule.span ℂ (Set.range w) := by
  set u := gramSchmidtNormed ℂ w with hudef
  have hu : Orthonormal ℂ u := gramSchmidtNormed_orthonormal hw
  have hspan : Submodule.span ℂ (Set.range u) = Submodule.span ℂ (Set.range w) := by
    rw [hudef, span_gramSchmidtNormed_range, span_gramSchmidt]
  refine ⟨u, fun b a => inner ℂ (u b) (w a), hu, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hij' : j < i := hij
    simp only [hudef, gramSchmidtNormed, inner_smul_left]
    rw [gramSchmidt_inv_triangular ℂ w hij', mul_zero]
  · intro j hj
    have hg := gramSchmidt_ne_zero j hw
    have h0 : inner ℂ (u j) (w j) = inner ℂ (u j) (gramSchmidt ℂ w j) := by
      conv_lhs => rw [gramSchmidt_def'' ℂ w j]
      rw [inner_add_right, inner_sum, Finset.sum_eq_zero, add_zero]
      intro i hi
      rw [inner_smul_right]
      simp only [hudef, gramSchmidtNormed, inner_smul_left,
        gramSchmidt_orthogonal ℂ w (Finset.mem_Iio.1 hi).ne', mul_zero]
    simp only at hj
    rw [h0] at hj
    simp only [hudef, gramSchmidtNormed, inner_smul_left, inner_self_eq_norm_sq_to_K] at hj
    simp [hg] at hj
  · intro a
    have : w a ∈ Submodule.span ℂ (Set.range u) := hspan ▸ Submodule.subset_span ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 this
    conv_lhs => rw [← hc]
    refine Finset.sum_congr rfl fun b _ => ?_
    show c b • u b = inner ℂ (u b) (w a) • u b
    rw [← hc, hu.inner_right_fintype]
  · intro a; rw [← hspan]; exact Submodule.subset_span ⟨a, rfl⟩
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
