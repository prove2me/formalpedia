-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.fS_scl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:26:36.502661+00:00
-- url     : https://prove2.me/submissions/792c7d60-1148-41dd-b84b-261eed322724

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExponentConditionNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoMulStar
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_OscillatoryBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_de_ge_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_de_scl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution {p m : ℕ} (s : Fin (p + 2) → ℝ) (hs0 : ∀ l, 0 ≤ s l) (τ : ℝ) (hτ : τ ∈ Icc (1 : ℝ) 2)
    (x : Xp (p + 1) m) : fS s (scl τ x) ≤ ENNReal.ofReal (2 ^ ∑ l, s l) * fS s x := by
  unfold fS
  rw [Real.rpow_sum_of_pos (by norm_num), ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro l _
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h1 := de_scl τ hτ.1 hτ.2 x l
  have h2 := de_ge_one x l
  calc de (scl τ x) l ^ (-s l) ≤ (de x l / 2) ^ (-s l) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) h1 (by linarith [hs0 l])
    _ = 2 ^ s l * de x l ^ (-s l) := by
        rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
          div_inv_eq_mul, mul_comm]
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
