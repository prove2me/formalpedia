-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartScalingIndep_coeff_eq_zero_674c17c17c2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:51:41.018703+00:00
-- url     : https://prove2.me/submissions/4407b786-7336-4404-aa7c-bbd1cd8e91c5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartScalingIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartScalingIndep
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartScalingIndep_isHomogeneous_mw_6c8ae1086a4a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_exists_homog_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_coordProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_of_mem_weighted
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_mem_weighted_of_isMultiHomog


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {K : Type} [Fintype K] [DecidableEq K]
  {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep
theorem _root_.solution (x : (Σ k, ι k) → Ω) (i : ∀ k, ι k) (hx : ∀ k, x ⟨k, i k⟩ ≠ 0)
    (hV : IsMultiHomogIdeal (RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω)))
    (s : Finset (K →₀ ℕ)) (g : (K →₀ ℕ) → MRingOver F ι)
    (hs : ∑ α ∈ s, aeval (fun q => x q / x ⟨q.1, i q.1⟩) (g α) * ∏ k, x ⟨k, i k⟩ ^ α k = 0) :
    ∀ β ∈ s, aeval (fun q => x q / x ⟨q.1, i q.1⟩) (g β) = 0 := by
  set y : (Σ k, ι k) → Ω := fun q => x q / x ⟨q.1, i q.1⟩ with hy
  have hxy : x = fun q => x ⟨q.1, i q.1⟩ * y q := by
    funext q
    show x q = x ⟨q.1, i q.1⟩ * (x q / x ⟨q.1, i q.1⟩)
    rw [mul_div_cancel₀ _ (hx q.1)]

  choose e₀ he₀ using fun α => exists_homog_chart (⊥ : Ideal (MRingOver F ι)) i (g α)
  set M : K → ℕ := s.sup e₀ with hM
  have hGex : ∀ α, ∃ G : MRingOver F ι, α ∈ s →
      G ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) M ∧
        Ideal.Quotient.mk (chartIdeal ⊥ i) G = Ideal.Quotient.mk (chartIdeal ⊥ i) (g α) := by
    intro α
    by_cases hα : α ∈ s
    · obtain ⟨G, h1, h2⟩ := he₀ α M (Finset.le_sup (f := e₀) hα)
      exact ⟨G, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hα⟩
  choose G hG using hGex
  have hker : chartIdeal (⊥ : Ideal (MRingOver F ι)) i ≤
      RingHom.ker (aeval y : MRingOver F ι →ₐ[F] Ω) := by
    unfold chartIdeal
    refine sup_le bot_le (Ideal.span_le.mpr ?_)
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, aeval_X, map_one]
    show x ⟨k, i k⟩ / x ⟨k, i k⟩ - 1 = 0
    rw [div_self (hx k), sub_self]
  have hGx : ∀ α ∈ s, aeval x (G α) = (∏ k, x ⟨k, i k⟩ ^ M k) * aeval y (g α) := by
    intro α hα
    have h0 := hker (Ideal.Quotient.eq.mp (hG α hα).2)
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h0
    rw [← h0]
    have h := aeval_blockScale (isMultiHomog_of_mem_weighted (hG α hα).1) (fun k => x ⟨k, i k⟩) y
    exact (congrArg (fun z => aeval z (G α)) hxy).trans h
  have hxc : ∀ α : K →₀ ℕ,
      aeval x (∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k) = ∏ k, x ⟨k, i k⟩ ^ α k := by
    intro α
    simp [map_prod]
  have hcM : (∏ k, x ⟨k, i k⟩ ^ M k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hx k)

  have hH : (∑ α ∈ s, G α * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k) ∈
      RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω) := by
    rw [RingHom.mem_ker, map_sum]
    calc ∑ α ∈ s, aeval x (G α * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k)
        = ∑ α ∈ s, (∏ k, x ⟨k, i k⟩ ^ M k) *
            (aeval y (g α) * ∏ k, x ⟨k, i k⟩ ^ α k) :=
          Finset.sum_congr rfl fun α hα => by rw [map_mul, hGx α hα, hxc, mul_assoc]
      _ = 0 := by rw [← Finset.mul_sum, hs, mul_zero]
  have hmem : ∀ α ∈ s, G α * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k ∈
      weightedHomogeneousSubmodule F (mw (ι := ι)) (M + ⇑α) := fun α hα =>
    SetLike.mul_mem_graded (hG α hα).1 (mem_weighted_of_isMultiHomog (isMultiHomog_coordProd i ⇑α))
  intro β hβ

  have hcomp : weightedHomogeneousComponent (mw (ι := ι)) (M + ⇑β)
      (∑ α ∈ s, G α * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k) =
        G β * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ β k := by
    rw [map_sum, Finset.sum_eq_single β]
    · rw [weightedHomogeneousComponent_of_mem (hmem β hβ), if_pos rfl]
    · intro α hα hne
      rw [weightedHomogeneousComponent_of_mem (hmem α hα), if_neg]
      intro h
      exact hne (DFunLike.coe_injective (add_left_cancel h)).symm
    · intro h
      exact absurd hβ h
  have hβV := weightedHomogeneousComponent_mem_of_mem F (mw (ι := ι)) (isHomogeneous_mw hV) hH (M + ⇑β)
  rw [hcomp, RingHom.mem_ker, map_mul, hGx β hβ, hxc] at hβV
  have hcβ : (∏ k, x ⟨k, i k⟩ ^ β k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hx k)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hβV).resolve_right hcβ)).resolve_left hcM
end GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep
