-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients.freq_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:00.671511+00:00
-- url     : https://prove2.me/submissions/cc263a37-f4d5-4f15-adde-83e8ef3d5a5a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bExpHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SublatticeCoefficients

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients
open NumberField Complex MeasureTheory ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
  ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients
theorem _root_.solution {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {n : ℕ}
    (β : Module.Basis (Fin n) ℝ (X.Ψ → ℝ)) (hβ : Submodule.span ℤ (Set.range β) = perL X la)
    (ν : X.Ψ → ℝ) (k : Fin n → ℤ) (hk : ∀ i, 2 * ∑ τ, ν τ * β i τ = k i) :
    ∀ p ∈ X.periods la, ∃ z : ℤ, 2 * ∑ τ, ν τ * p τ = z := by
  intro p hp
  have hp' : p ∈ Submodule.span ℤ (Set.range β) := by rw [hβ]; exact hp
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℤ |>.mp hp'
  refine ⟨∑ j, c j * k j, ?_⟩
  rw [← hc]
  push_cast
  simp only [Finset.sum_apply, Pi.smul_apply]
  simp only [zsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hk j, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients
