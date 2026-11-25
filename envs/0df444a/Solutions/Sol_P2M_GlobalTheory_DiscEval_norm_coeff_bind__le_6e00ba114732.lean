-- Prove2me | solution 1 for P2M_GlobalTheory_DiscEval_norm_coeff_bind__le_6e00ba114732
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:05:52.217715+00:00
-- url     : https://prove2.me/submissions/f140415f-bb1b-410f-9c10-1442c6092008

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_BasisChangePf_cb_C_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_BasisChangePf_cb_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_BasisChangePf_cb_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_BasisChangePf_cb_sum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X



set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscEval
open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries
open MvPolynomial
variable {O : Type*} [CommRing O] {π : O}
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
namespace GlobalTheory.DiscEval
theorem _root_.solution {K : Type*} [NormedField K] [IsUltrametricDist K] {σ τ : Type*}
    {P : MvPolynomial σ K} {d : ℕ} (hP : P.IsHomogeneous d) (hP1 : ∀ μ, ‖coeff μ P‖ ≤ 1)
    {g : σ → MvPolynomial τ K} {c : ℝ} (hc : 0 ≤ c) (hg : ∀ k μ, ‖coeff μ (g k)‖ ≤ c)
    (μ : τ →₀ ℕ) : ‖coeff μ (bind₁ g P)‖ ≤ c ^ d := by
  open ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf in
  have hmain : CB (bind₁ g P) (c ^ d) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    refine cb_sum _ _ (pow_nonneg hc d) fun ν hν => ?_
    rw [bind₁_monomial]
    have hdeg : ∑ k ∈ ν.support, ν k = d := by
      have := hP (mem_support_iff.1 hν)
      simpa [Finsupp.weight_apply, Finsupp.sum] using this
    have h1 := cb_C_mul (coeff ν P) (cb_prod ν.support _ (fun k => c ^ ν k)
      (fun k => pow_nonneg hc _) (fun k _ => cb_pow hc (hg k) (ν k)))
    rw [Finset.prod_pow_eq_pow_sum, hdeg] at h1
    exact fun μ' => (h1 μ').trans (mul_le_of_le_one_left (pow_nonneg hc d) (hP1 ν))
  exact hmain μ
end GlobalTheory.DiscEval
