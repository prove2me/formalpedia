-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.gtD_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:30:29.406861+00:00
-- url     : https://prove2.me/submissions/e64440d9-cd78-41e5-a1c9-1bddbf8b1253

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Module Submodule
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {m : ℕ} (b : Basis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (y0 xu : EuclideanSpace ℝ (Fin (m + 1))) (hy0 : y0 ≠ 0) (hxu : xu ∈ span ℤ (Set.range b))
    (h1 : inner ℝ y0 xu = 1) (hint : ∀ j, ∃ k : ℤ, inner ℝ y0 (b j) = k) :
    ∃ bW : Basis (Fin m) ℝ (ℝ ∙ y0)ᗮ,
      (∀ x ∈ span ℤ (Set.range bW),
        ((x : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1))) ∈ span ℤ (Set.range b)) ∧
      (∀ v ∈ span ℤ (Set.range b), ∃ p ∈ span ℤ (Set.range bW),
        (p : EuclideanSpace ℝ (Fin (m + 1))) = v - inner ℝ y0 v • xu) := by
  classical
  have hintL : ∀ v ∈ span ℤ (Set.range b), ∃ k : ℤ, inner ℝ y0 v = k := by
    intro v hv
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hv
    choose k hk using hint
    refine ⟨∑ i, c i * k i, ?_⟩
    rw [inner_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hk]
  have hPW : ∀ v : EuclideanSpace ℝ (Fin (m + 1)), v - inner ℝ y0 v • xu ∈ (ℝ ∙ y0)ᗮ := by
    intro v
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, real_inner_smul_right, h1,
      mul_one, sub_self]
  have hPL : ∀ v ∈ span ℤ (Set.range b), v - inner ℝ y0 v • xu ∈ span ℤ (Set.range b) := by
    intro v hv
    obtain ⟨k, hk⟩ := hintL v hv
    rw [hk, Int.cast_smul_eq_zsmul]
    exact sub_mem hv (Submodule.smul_mem _ k hxu)
  let K : Submodule ℤ (ℝ ∙ y0)ᗮ :=
    (span ℤ (Set.range b)).comap (((ℝ ∙ y0)ᗮ).subtype.restrictScalars ℤ)
  have hKmem : ∀ x : (ℝ ∙ y0)ᗮ,
      x ∈ K ↔ (x : EuclideanSpace ℝ (Fin (m + 1))) ∈ span ℤ (Set.range b) := fun x => Iff.rfl
  have : DiscreteTopology K := by
    let f : K → span ℤ (Set.range b) := fun x =>
      ⟨((x : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1))), (hKmem x).1 x.2⟩
    refine DiscreteTopology.of_continuous_injective (f := f)
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) ?_
    intro x y hxy
    have hv := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext hv)
  have : IsZLattice ℝ K := by
    refine ⟨eq_top_iff.2 fun w _ => ?_⟩
    have hw0 : inner ℝ y0 (w : EuclideanSpace ℝ (Fin (m + 1))) = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 w.2
    have hw0' : ∑ j, b.repr (w : EuclideanSpace ℝ (Fin (m + 1))) j * inner ℝ y0 (b j) = 0 := by
      rw [← hw0]
      conv_rhs => rw [← b.sum_repr (w : EuclideanSpace ℝ (Fin (m + 1)))]
      rw [inner_sum]
      simp_rw [real_inner_smul_right]
    have hsum : w = ∑ j, b.repr (w : EuclideanSpace ℝ (Fin (m + 1))) j •
        (⟨b j - inner ℝ y0 (b j) • xu, hPW (b j)⟩ : (ℝ ∙ y0)ᗮ) := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, smul_sub, Finset.sum_sub_distrib]
      simp_rw [smul_smul]
      rw [← Finset.sum_smul, hw0', zero_smul, sub_zero, b.sum_repr]
    rw [hsum]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact (hKmem _).2 (hPL (b j) (Submodule.subset_span ⟨j, rfl⟩))
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hrank : Module.finrank ℤ K = m := by
    rw [ZLattice.rank ℝ K, Submodule.finrank_orthogonal_span_singleton (n := m) hy0]
  let bK : Basis (Fin m) ℤ K := Module.finBasisOfFinrankEq ℤ K hrank
  refine ⟨bK.ofZLatticeBasis ℝ K, ?_, ?_⟩
  · intro x hx
    rw [Basis.ofZLatticeBasis_span] at hx
    exact (hKmem x).1 hx
  · intro v hv
    refine ⟨⟨v - inner ℝ y0 v • xu, hPW v⟩, ?_, rfl⟩
    rw [Basis.ofZLatticeBasis_span]
    exact (hKmem _).2 (hPL v hv)
end ReciprocityTheory.ChartRestriction.G.T0
