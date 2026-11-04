-- Prove2me | solution 1 for ThreeSum.ArithmeticStageBounds.powerBound_of_fifth_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:49:25.971003+00:00
-- url     : https://prove2.me/submissions/f5b1854f-a9c5-449c-a7ad-e4f33da11a4f

import Definitions.Def_Submission_ThreeSum_ModuloCosts
import Definitions.Def_Submission_ThreeSum_BudgetTime
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
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
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_Switch_mem_candidates
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
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
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.ArithmeticStageBounds
open Filter Real Parameters Scales BandScales CostLedger HierarchyScales
  MassScales StageBounds UniformStageBounds ModuloCosts
open scoped Topology
set_option maxHeartbeats 1000000
noncomputable section
namespace ThreeSum.ArithmeticStageBounds
theorem _root_.solution {f g : ℕ → ℕ} {a : ℝ}
    (hg : PowerBound g a) (hfg : ∀ n, f n^5 ≤ 256*g n^8) :
    PowerBound f ((8/5)*a) := by
  intro d hd
  filter_upwards [hg (d/2) (by linarith), (PowerBound.const 256) (d/2) (by linarith),
    eventually_ge_atTop (1 : ℕ)] with n hn hconst hge
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hgeR : (1 : ℝ) ≤ n := by exact_mod_cast hge
  have hpow : (f n : ℝ)^5 ≤ ((n : ℝ)^((8/5)*a+d))^5 := by
    calc
      _ ≤ 256*(g n : ℝ)^8 := by exact_mod_cast hfg n
      _ ≤ (n : ℝ)^(d/2) * ((n : ℝ)^(a+d/2))^8 := by
        apply mul_le_mul
        · simpa only [zero_add, Nat.cast_ofNat] using hconst
        · exact pow_le_pow_left₀ (Nat.cast_nonneg _) hn 8
        · positivity
        · positivity
      _ = (n : ℝ)^(d/2+(a+d/2)*8) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le, ← Real.rpow_add hnR]
        norm_num
      _ ≤ (n : ℝ)^(((8/5)*a+d)*5) :=
        Real.rpow_le_rpow_of_exponent_le hgeR (by linarith)
      _ = _ := by rw [Real.rpow_mul hnR.le]; norm_num only [Real.rpow_ofNat]
  exact le_of_pow_le_pow_left₀ (by decide : (5 : ℕ) ≠ 0) (by positivity) hpow
end ThreeSum.ArithmeticStageBounds
