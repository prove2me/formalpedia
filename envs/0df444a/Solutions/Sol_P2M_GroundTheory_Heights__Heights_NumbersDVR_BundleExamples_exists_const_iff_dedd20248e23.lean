-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_exists_const_iff_dedd20248e23
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:06:00.843779+00:00
-- url     : https://prove2.me/submissions/5d53263e-deaa-490f-8bee-d1e6a42b2830

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomogIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Theorems.Thm_GroundTheory_Arith_Iwasawa_IsDistinguished_ne_zero


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
set_option linter.unusedSectionVars false
universe u
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
theorem _root_.solution {ϖ : O} (hϖ : Irreducible ϖ) {x : (Σ k, ι k) → Ω}
    (B : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V) (s : ∀ k, ι k) (v : V) :
    (∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ B.lat s) ↔
      ∃ n : ℕ, algebraMap O Ω ϖ ^ n • v ∈ B.lat s := by
  constructor
  · rintro ⟨c, hc, hv⟩
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    refine ⟨n, ?_⟩
    have h := B.stable s (algebraMap O Ω ↑u⁻¹) (Subalgebra.algebraMap_mem _ _) _ hv
    rwa [smul_smul, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul, map_pow] at h
  · rintro ⟨n, hn⟩
    exact ⟨ϖ ^ n, pow_ne_zero _ hϖ.ne_zero, by rwa [map_pow]⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
