-- Prove2me | solution 1 for P2M_ReciprocityTheory_Cheb_smoothMap_seminorm_bound__39c12cba5872
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:41:45.919345+00:00
-- url     : https://prove2.me/submissions/e8d803f0-364c-4d9e-b7fa-754f26a62723

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeCont
import Theorems.Thm_ReciprocityTheory_Cheb_norm_chiNrm_cpow_le
import Theorems.Thm_ReciprocityTheory_Cheb_nrm_rpow_neg_le_half
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
theorem _root_.solution : SmoothMapSeminormBound := by
  intro E _ _ l _ χ s0 hs0
  have hs0' : (1:ℝ) < s0 := hs0
  set a : ℝ := (1 + s0) / 2 with ha_def
  have ha1 : 1 < a := by rw [ha_def]; linarith
  have has0 : a < s0 := by rw [ha_def]; linarith
  have hcont : ContinuousOn (fun s : ℝ => abelian₂ E χ s) (Set.Ioi a) := by
    unfold abelian₂
    refine continuousOn_tsum (u := fun q : Prm E => (3 / 2) * ((Nrm q : ℕ) : ℝ) ^ (-a)) ?_
      ((summable_prm_rpow E ha1).mul_left _) ?_
    · intro q
      have hN : (Nrm q : ℕ) ≠ 0 := by have := two_le_Nrm q; omega
      have hc : Continuous (fun s : ℝ => χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))) :=
        continuous_const.mul (Continuous.const_cpow (Complex.continuous_ofReal.neg)
          (Or.inl (by exact_mod_cast hN)))
      refine ContinuousOn.neg (ContinuousOn.clog (continuous_const.sub hc).continuousOn ?_)
      intro s hs
      have hs' : a < s := hs
      have hz := (norm_chiNrm_cpow_le χ q s).trans (nrm_rpow_neg_le_half q (by linarith))
      rw [Complex.mem_slitPlane_iff]
      left
      have hre := Complex.abs_re_le_norm (χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)))
      rw [Complex.sub_re, Complex.one_re]
      have := (abs_le.mp (hre.trans hz)).2
      linarith
    · intro q s hs
      have hs' : a < s := hs
      have hz1 := norm_chiNrm_cpow_le χ q s
      have hz := hz1.trans (nrm_rpow_neg_le_half q (by linarith))
      rw [norm_neg, sub_eq_add_neg]
      have hz' : ‖-(χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)))‖ ≤ 1 / 2 := by
        rw [norm_neg]; exact hz
      refine (Complex.norm_log_one_add_half_le_self hz').trans ?_
      rw [norm_neg]
      have hmono : ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ ((Nrm q : ℕ) : ℝ) ^ (-a) := by
        have h2 : (2:ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      nlinarith
  exact (hcont.continuousAt (Ioi_mem_nhds has0)).continuousWithinAt
end ReciprocityTheory.Cheb
