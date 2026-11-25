-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.integral_re_double_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:12:48.952635+00:00
-- url     : https://prove2.me/submissions/06e4ac3a-464a-46eb-82c0-2ee1419f1078

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HalfSumNormSubSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_ImportsTer
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportOfVanish
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.E
theorem _root_.solution {M : Type*} [MeasurableSpace M] (μ : Measure M) (n : ℕ)
    (h : Fin n → Fin n → M → ℂ) (hi : ∀ j k, Integrable (h j k) μ) :
    ∫ x, (∑ j, ∑ k, h j k x).re ∂μ = (∑ j, ∑ k, ∫ x, h j k x ∂μ).re := by
  have hint : Integrable (fun x => ∑ j, ∑ k, h j k x) μ :=
    integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => hi j k
  have h1 := integral_re (𝕜 := ℂ) hint
  simp only [RCLike.re_to_complex] at h1
  rw [h1, integral_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => hi j k]
  congr 1
  exact Finset.sum_congr rfl fun j _ => integral_finset_sum _ fun k _ => hi j k
end ReciprocityTheory.L2DbarEstimates.E
