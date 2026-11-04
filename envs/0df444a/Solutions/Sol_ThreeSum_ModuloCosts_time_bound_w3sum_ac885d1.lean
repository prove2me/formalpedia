-- Prove2me | solution 1 for ThreeSum.ModuloCosts.time_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:52:53.309759+00:00
-- url     : https://prove2.me/submissions/ef710673-2303-4ab5-80ec-2571405372ff

import Definitions.Def_Submission_ThreeSum_ModuloRuntime
import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Definitions.Def_Submission_ThreeSum_ModuloCosts
import Theorems.Thm_ThreeSum_ModuloCosts_capacity_le_roundedPower
import Theorems.Thm_ThreeSum_ModuloCosts_log_le_roundedPower
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_KaratsubaInterface_le_capacity
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_time_le
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightKaratsuba.window_sub



set_option autoImplicit false
open ThreeSum ThreeSum.ModuloCosts
open KaratsubaInterface
namespace ThreeSum.ModuloCosts
theorem _root_.solution (p nA nB nC N U : ℕ)
    (ha : nA ≤ N) (hb : nB ≤ N) (hc : nC ≤ N) :
    LightModuloCounts.time p nA nB nC U ≤
      10000 * (roundedPower p + N*(Nat.log 2 (U+1)+1) + 1) := by
  have hcap := capacity_le_roundedPower p
  have hlog := log_le_roundedPower p
  have hp := (le_capacity p).trans hcap
  have hK : LightKaratsuba.time (Nat.clog 2 p) ≤ 2530*roundedPower p :=
    LightKaratsuba.time_le _
  have hNa := Nat.mul_le_mul_right (Nat.log 2 (U+1)+1) ha
  have hNb := Nat.mul_le_mul_right (Nat.log 2 (U+1)+1) hb
  have hNc := Nat.mul_le_mul_right (Nat.log 2 (U+1)+1) hc
  unfold LightModuloCounts.time LightCapacity.time LightResidueHistogram.time
    LightHistogram.histogramTime LightHistogram.countTime LightCyclic.combinedTime
    LightArray.linearTime LightResidues.residuesTime LightResidues.residueBudget
    LightLookupSum.time
  simp only [Light.fillTime]
  nlinarith
end ThreeSum.ModuloCosts
