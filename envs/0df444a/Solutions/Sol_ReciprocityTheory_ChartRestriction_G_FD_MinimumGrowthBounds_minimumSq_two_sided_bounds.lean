-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_two_sided_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:54:44.750064+00:00
-- url     : https://prove2.me/submissions/660b5e3f-af91-48a7-be0e-1593ab94ef38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TwoSidedBoostBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MinimumGrowthBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantConjugateTransfer_maj_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_c_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TwoSidedBoostBounds_c_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MajorantConjugateTransfer TwoSidedBoostBounds
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds
theorem _root_.solution {x y : Frame X.Ψ r} (hx : x ∈ X.dom) (hy : y ∈ X.dom) {k1 k2 : ℝ}
    (hk1 : 0 ≤ k1) (hk2 : 0 < k2) (hlow : ∀ τ w, k1 * X.maj x τ w ≤ X.maj y τ w)
    (hup : ∀ τ w, X.maj y τ w ≤ k2 * X.maj x τ w) :
    k1 * X.firstMinimumSq x ≤ X.firstMinimumSq y ∧ X.firstMinimumSq y ≤ k2 * X.firstMinimumSq x := by
  have hc : ∀ τ, 0 ≤ X.c τ := fun τ => (TwoSidedBoostBounds.c_pos (X := X) τ).le
  have e : ∀ g' : (Fin r → E) → ℝ, (¬ ∃ v ∈ X.Λ, v ≠ 0) → {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g' v} = ∅ := by
    intro g' hne
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨v, hv, hv', _⟩
    exact hne ⟨v, hv, hv'⟩
  have key1 : ∀ (g h : (Fin r → E) → ℝ) (a : ℝ), 0 ≤ a → (∀ v, 0 ≤ g v) → (∀ v, a * g v ≤ h v) →
      a * sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g v} ≤ sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = h v} := by
    intro g h a ha hg hgh
    by_cases hne : ∃ v ∈ X.Λ, v ≠ 0
    · obtain ⟨v0, hv0, hv0'⟩ := hne
      refine le_csInf ⟨_, v0, hv0, hv0', rfl⟩ ?_
      rintro t ⟨v, hv, hv', rfl⟩
      have hb : BddBelow {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g v} := ⟨0, by
        rintro s ⟨w, _, _, rfl⟩
        exact hg w⟩
      exact (mul_le_mul_of_nonneg_left (csInf_le hb ⟨v, hv, hv', rfl⟩) ha).trans (hgh v)
    · rw [e g hne, e h hne, Real.sInf_empty, mul_zero]
  have key2 : ∀ (g h : (Fin r → E) → ℝ) (a : ℝ), 0 < a → (∀ v, 0 ≤ g v) → (∀ v, g v ≤ a * h v) →
      sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g v} ≤ a * sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = h v} := by
    intro g h a ha hg hgh
    by_cases hne : ∃ v ∈ X.Λ, v ≠ 0
    · obtain ⟨v0, hv0, hv0'⟩ := hne
      rw [← div_le_iff₀' ha]
      refine le_csInf ⟨_, v0, hv0, hv0', rfl⟩ ?_
      rintro t ⟨v, hv, hv', rfl⟩
      rw [div_le_iff₀' ha]
      have hb : BddBelow {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g v} := ⟨0, by
        rintro s ⟨w, _, _, rfl⟩
        exact hg w⟩
      exact (csInf_le hb ⟨v, hv, hv', rfl⟩).trans (hgh v)
    · rw [e g hne, e h hne, Real.sInf_empty, mul_zero]
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
  refine ⟨key1 _ _ k1 hk1 ?_ ?_, key2 _ _ k2 hk2 ?_ ?_⟩
  · intro v
    exact Finset.sum_nonneg fun τ _ => mul_nonneg (hc τ) (MajorantConjugateTransfer.maj_nonneg (X := X) hx τ _)
  · intro v
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ _ =>
      (mul_left_comm _ _ _).trans_le (mul_le_mul_of_nonneg_left (hlow τ _) (hc τ))
  · intro v
    exact Finset.sum_nonneg fun τ _ => mul_nonneg (hc τ) (MajorantConjugateTransfer.maj_nonneg (X := X) hy τ _)
  · intro v
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ _ =>
      (mul_le_mul_of_nonneg_left (hup τ _) (hc τ)).trans_eq (mul_left_comm _ _ _)
end ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds
