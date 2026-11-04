-- Prove2me | solution 1 for ThreeSum.ArithmeticStageBounds.combined_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:16:03.718832+00:00
-- url     : https://prove2.me/submissions/38f2159e-8ad2-456a-bf59-546d0102b6f6

import Definitions.Def_Submission_ThreeSum_ModuloCosts
import Definitions.Def_Submission_ThreeSum_BudgetTime
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Theorems.Thm_ThreeSum_ArithmeticStageBounds_arithmetic_powerBound
import Theorems.Thm_ThreeSum_ArithmeticStageBounds_offset_powerBound
import Theorems.Thm_ThreeSum_ArithmeticStageBounds_normalization_powerBound
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
import Theorems.Thm_ThreeSum_Parameters_all_costs_le_certificate
import Definitions.Def_WeightedCache3SUM_Alias_851b6603dbe122fe
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mono_exponent
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_UniformStageBounds_workBudget_powerBound
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
theorem _root_.solution (C k : ℕ) : PowerBound (combinedBudget C k) certificateExponent := by
  have ha := (arithmetic_powerBound C k).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have ho := (offset_powerBound C).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have hn := (normalization_powerBound C).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  exact (((workBudget_powerBound C k).add_same ha).add_same ho).add_same hn
end ThreeSum.ArithmeticStageBounds
