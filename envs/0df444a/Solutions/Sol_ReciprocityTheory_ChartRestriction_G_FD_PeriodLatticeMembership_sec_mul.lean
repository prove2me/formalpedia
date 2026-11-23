-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership.sec_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:09.27319+00:00
-- url     : https://prove2.me/submissions/6b4baacb-ec0f-4393-8fc6-39bc83aeab4b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientConvolutionOfSubCoefficients
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates.Y
  ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} (X : Data E r)
private lemma diag_ne_lemma {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (i : Fin r) :
    b τ i i ≠ 0 := by
  obtain ⟨hdet, htri⟩ := hb τ
  have ht : (mat b τ).BlockTriangular id := fun a c h => htri a c h
  rw [Matrix.det_of_upperTriangular ht] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)
section line
variable {X}
end line
end
end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates.Y
  ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
theorem _root_.solution {la la' : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) (hQ : X.IsSec la' Q) :
    X.IsSec (la + la') (P * Q) := by
  obtain ⟨hPd, hPb, hPg⟩ := hP
  obtain ⟨hQd, hQb, hQg⟩ := hQ
  refine ⟨hPd.mul hQd, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · have hbc : bchar (la + la') b = bchar la b * bchar la' b := by
      simp only [bchar, Pi.add_apply, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_
      exact zpow_add₀ (diag_ne_lemma X hb τ i) _ _
    simp only [Pi.mul_apply, hPb x hx b hb, hQb x hx b hb, hbc]
    ring
  · simp only [Pi.mul_apply, hPg γ hγ x hx, hQg γ hγ x hx, X.χ_add la la' γ hγ]
    ring
end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
