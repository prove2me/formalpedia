-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_mul_6491c5235776
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:14.426632+00:00
-- url     : https://prove2.me/submissions/2eaf1745-c58a-4f27-ac25-6935881dabcd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialQuotDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorsCommute
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairCocycle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ratDiv_mul_655de8ec8838

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
universe u
variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {P : Ideal (MRing ι O)} [P.IsPrime] {ϖ : O} {b b' : K → ℤ}
    {f g f' g' : MRing ι O} (hD : IsVerticalDivisor P ϖ b f g)
    (hD' : IsVerticalDivisor P ϖ b' f' g') :
    IsVerticalDivisor P ϖ (b + b') (f * f') (g * g') where
  degrees := by
    obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
    obtain ⟨bf', bg', hf', hg', hb'⟩ := hD'.degrees
    refine ⟨bf + bf', bg + bg', IsWeightedHomogeneous.mul hf hf',
      IsWeightedHomogeneous.mul hg hg', ?_⟩
    rw [← hb, ← hb']
    funext k
    simp only [Pi.add_apply, Nat.cast_add]
    ring
  num_not_mem := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hD.num_not_mem hD'.num_not_mem
  den_not_mem := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hD.den_not_mem hD'.den_not_mem
  vertical := by
    intro W hW
    rw [ratDiv_mul hD.num_not_mem hD.den_not_mem hD'.num_not_mem hD'.den_not_mem,
      Pi.add_apply] at hW
    by_cases h1 : ratDiv P f g W = 0
    · rw [h1, zero_add] at hW
      exact hD'.vertical W hW
    · exact hD.vertical W h1
  unit_off_special := by
    intro W hW hPW hrel hϖ
    obtain ⟨u, v, hu, hv, h⟩ := hD.unit_off_special W hW hPW hrel hϖ
    obtain ⟨u', v', hu', hv', h'⟩ := hD'.unit_off_special W hW hPW hrel hϖ
    refine ⟨u * u', v * v', fun hm => (hW.mem_or_mem hm).elim hu hu',
      fun hm => (hW.mem_or_mem hm).elim hv hv', ?_⟩
    have e : u * u' * (f * f') - v * v' * (g * g') =
        (u' * f') * (u * f - v * g) + (v * g) * (u' * f' - v' * g') := by ring
    rw [e]
    exact P.add_mem (P.mul_mem_left _ h) (P.mul_mem_left _ h')
end GroundTheory.Heights₂.Heights.NumbersDVR
