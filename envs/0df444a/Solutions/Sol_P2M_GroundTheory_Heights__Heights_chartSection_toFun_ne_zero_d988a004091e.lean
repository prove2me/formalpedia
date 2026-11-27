-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chartSection_toFun_ne_zero_d988a004091e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:10:59.283933+00:00
-- url     : https://prove2.me/submissions/7535ab84-7652-4968-adac-d45194c88918

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (c : (k : ι) → Fin (n k + 1)) :
    (IntegralSection.chartSection (ArithVariety.whole n) c).toFun ≠ 0 := by
  change (ArithVariety.whole n).mkF (chartMonomial c 1) / (ArithVariety.whole n).mkF 1 ≠ 0
  rw [map_one, div_one, Ne, ArithVariety.mkF_eq_zero_iff]
  change ¬ (_ ∈ (⊥ : Ideal (MvPolynomial (Coord n) ℤ)))
  rw [Submodule.mem_bot, chartMonomial]
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (X_ne_zero _)
end GroundTheory.Heights₂.Heights
