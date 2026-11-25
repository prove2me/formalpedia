-- Prove2me | solution 1 for P2M_ReciprocityTheory_Cheb_casimirPower_surjective_symmetric__d64ad7ac444a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:59.895688+00:00
-- url     : https://prove2.me/submissions/54a8e3ab-09e1-4999-b8f7-7ea3f998b02e

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeSum
import Theorems.Thm_ReciprocityTheory_Cheb_norm_neg_log_one_sub_sub_le
import Theorems.Thm_ReciprocityTheory_Cheb_psum_term_norm_le
import Theorems.Thm_ReciprocityTheory_Cheb_Nrm_rpow_neg_le_inv
import Theorems.Thm_ReciprocityTheory_Cheb_summable_prm_rpow
import Theorems.Thm_ReciprocityTheory_Cheb_two_le_Nrm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution : CasimirPowerSurjectiveSymmetric := by
  intro E _ _ l _ χ
  refine ⟨∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)), fun s hs => ?_⟩
  set z : Prm E → ℂ := fun q => χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)) with hzdef
  have hzb : ∀ q, ‖z q‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := fun q => psum_term_norm_le χ s q
  have hzs : Summable z := Summable.of_norm_bounded (summable_prm_rpow E hs) hzb
  have hls : Summable (fun q => -Complex.log (1 - z q)) := hzs.clog_one_sub.neg
  have hsq : ∀ q, ‖-Complex.log (1 - z q) - z q‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
    intro q
    have h2 : (2 : ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
    have hz1 : ‖z q‖ ≤ ((Nrm q : ℕ) : ℝ)⁻¹ := (hzb q).trans (Nrm_rpow_neg_le_inv hs q)
    have hz2 : ‖z q‖ ≤ 1 / 2 := hz1.trans (by rw [one_div]; exact inv_anti₀ (by norm_num) h2)
    refine (norm_neg_log_one_sub_sub_le hz2).trans ?_
    rw [Real.rpow_neg (by linarith), Real.rpow_two, ← inv_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hz1 2
  have e : abelian₂ E χ s - Psum E χ s = ∑' q, (-Complex.log (1 - z q) - z q) := by
    unfold abelian₂ Psum
    exact (hls.tsum_sub hzs).symm
  rw [e]
  exact tsum_of_norm_bounded (summable_prm_rpow E (by norm_num : (1 : ℝ) < 2)).hasSum hsq
end ReciprocityTheory.Cheb
