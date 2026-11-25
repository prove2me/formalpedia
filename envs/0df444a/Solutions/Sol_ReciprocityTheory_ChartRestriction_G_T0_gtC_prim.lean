-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.gtC_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:30:29.13969+00:00
-- url     : https://prove2.me/submissions/223688ca-a271-4942-b515-dc152371521d

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (b : Basis (Fin n) ℝ E) (y1 : E) (hy1 : y1 ≠ 0)
    (hint : ∀ j, ∃ m : ℤ, inner ℝ y1 (b j) = m) :
    ∃ y0 : E, ∃ xu ∈ span ℤ (Set.range b), y0 ≠ 0 ∧ (∀ j, ∃ m : ℤ, inner ℝ y0 (b j) = m) ∧
      ‖y0‖ ≤ ‖y1‖ ∧ inner ℝ y0 xu = 1 := by
  classical
  choose m hm using hint
  have hPI := IsPrincipalIdealRing.principal (Ideal.span (Set.range m))
  obtain ⟨g, hg⟩ := Submodule.IsPrincipal.principal (Ideal.span (Set.range m))
  have hgI : g ∈ Ideal.span (Set.range m) := by
    rw [hg]
    exact Submodule.mem_span_singleton_self g
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hgI
  simp only [smul_eq_mul] at hc
  have hdiv : ∀ j, ∃ a : ℤ, a * g = m j := by
    intro j
    have hj : m j ∈ Ideal.span (Set.range m) := Ideal.subset_span ⟨j, rfl⟩
    rw [hg] at hj
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hj
    exact ⟨a, by simpa using ha⟩
  choose a ha using hdiv
  have hne : ∃ j, m j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hy1
    have h0 : ∀ x, inner ℝ y1 x = 0 := by
      intro x
      rw [← b.sum_repr x, inner_sum]
      simp [inner_smul_right, hm, hcon]
    exact inner_self_eq_zero.1 (h0 y1)
  have hg0 : g ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hne
    exact hj (by rw [← ha j, mul_zero])
  have hgR : (g : ℝ) ≠ 0 := Int.cast_ne_zero.2 hg0
  refine ⟨(g : ℝ)⁻¹ • y1, ∑ i, c i • b i,
    (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, rfl⟩,
    smul_ne_zero (inv_ne_zero hgR) hy1, fun j => ⟨a j, ?_⟩, ?_, ?_⟩
  · rw [real_inner_smul_left, hm, ← ha j]
    push_cast
    field_simp
  · rw [norm_smul, norm_inv, Real.norm_eq_abs]
    have h1 : (1 : ℝ) ≤ |(g : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hg0
    exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ h1)
  · rw [inner_sum]
    simp_rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, real_inner_smul_left, hm]
    have h2 : ∑ i, (c i : ℝ) * ((g : ℝ)⁻¹ * (m i : ℝ)) = (g : ℝ)⁻¹ * ((∑ i, c i * m i : ℤ) : ℝ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h2, hc]
    exact inv_mul_cancel₀ hgR
end ReciprocityTheory.ChartRestriction.G.T0
