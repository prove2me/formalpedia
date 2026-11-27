-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.deg_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:28:56.167629+00:00
-- url     : https://prove2.me/submissions/22d4387c-16d7-4db5-987f-9f8db5ba5e94

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ArakelovDegreeEqDegreeOfFamily
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_prod_norm_embeddings
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_arakelovDegree_eq_degreeOfFamily


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder
variable (K : Type*) [Field K] [NumberField K]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (a : K) (ha : a ≠ 0) :
    deg (stdHerm K 1) (Submodule.span (𝓞 K) {fun _ : Fin 1 => a}) =
      -Real.log |(Algebra.norm ℚ a : ℝ)| / finrank ℚ K := by
  classical
  set x : Fin 1 → K := fun _ => a with hx
  have hx0 : x ≠ 0 := fun h => ha (congrFun h 0)
  have hli : LinearIndependent K (fun _ : Fin 1 => x) := by
    rw [linearIndependent_unique_iff]
    exact hx0
  have hrange : Set.range (fun _ : Fin 1 => x) = {x} := Set.range_const
  have hfr : IsFrame K (Submodule.span (𝓞 K) {x}) (fun _ : Fin 1 => x) := by
    refine ⟨fun _ => Submodule.subset_span rfl, hli, ?_⟩
    intro y hy
    have hle : Submodule.span (𝓞 K) {x} ≤
        (Submodule.span K (Set.range fun _ : Fin 1 => x)).restrictScalars (𝓞 K) := by
      rw [Submodule.span_le]
      rintro _ rfl
      exact Submodule.subset_span ⟨0, rfl⟩
    exact hle hy
  rw [arakelovDegree_eq_degreeOfFamily _ (Submodule.fg_span_singleton x) hfr]
  have hg : ∀ σ : K →+* ℂ, ((stdHerm K 1).gram σ (fun _ : Fin 1 => x)).det.re = ‖σ a‖ ^ 2 := by
    intro σ
    simp only [Matrix.det_unique, HermFam.gram, stdHerm, Matrix.of_apply, hx,
      Finset.univ_unique, Finset.sum_singleton]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.conj_re, Complex.conj_im]
  have hpos : ∀ σ : K →+* ℂ, ‖σ a‖ ≠ 0 := fun σ => by
    simpa using ha
  have hsum : ∑ σ : K →+* ℂ, Real.log ((stdHerm K 1).gram σ (fun _ : Fin 1 => x)).det.re =
      2 * Real.log |(Algebra.norm ℚ a : ℝ)| := by
    simp only [hg, Real.log_pow, Nat.cast_ofNat]
    rw [← Finset.mul_sum, ← Real.log_prod (fun σ _ => hpos σ), prod_norm_embeddings]
  unfold degreeOfFamily
  rw [hsum, hrange, AddSubgroup.relIndex_self]
  simp
end ReciprocityTheory.GeometryOfNumbersTheory
