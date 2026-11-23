-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership.scale_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:09.424617+00:00
-- url     : https://prove2.me/submissions/67d92f6e-e706-4783-80ed-d3ae8d6db03e

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
theorem _root_.solution (la la2 : Wt X.Ψ r) (K K2 : ℕ) (hK : X.chiOrd la * K = X.chiOrd la2 * K2)
    {p : X.Ψ → ℝ} (hp : p ∈ X.periods la) : (K : ℝ) • p ∈ X.periods la2 := by
  have hK' : (X.chiOrd la : ℝ) * K = X.chiOrd la2 * K2 := by exact_mod_cast hK
  simp only [Nat.cast_smul_eq_nsmul]
  unfold Data.periods at hp
  refine AddSubgroup.closure_induction (fun q hq => ?_) ?_ (fun q q' _ _ h1 h2 => ?_)
    (fun q _ h => ?_) hp
  · obtain ⟨a, hca, hia, rfl⟩ := hq
    apply AddSubgroup.subset_closure
    refine ⟨(K2 : E) * a, ?_, ?_, ?_⟩
    · simp only [cc] at hca ⊢
      rw [map_mul, map_natCast, hca]
    · have h2 : IsIntegral ℤ (K2 : E) := by
        simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (K2 : ℤ)))
      exact h2.mul hia
    · funext τ
      simp only [Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast, Nat.cast_mul,
        Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
      linear_combination ((X.m : ℝ) * (τ.1 a).re) * hK'
  · rw [smul_zero]
    exact AddSubgroup.zero_mem _
  · rw [smul_add]
    exact AddSubgroup.add_mem _ h1 h2
  · rw [smul_neg]
    exact AddSubgroup.neg_mem _ h
end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
