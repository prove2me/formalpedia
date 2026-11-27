-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PivotProductBound_proof_7097c93c80dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:07:39.177398+00:00
-- url     : https://prove2.me/submissions/74cde247-7e17-4ad8-ba29-c03c7146676f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPivotProductBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PivotProductBound_pivot_pos_e6bcb14ca110
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PivotProductBound_prod_range_pivot_67280104cdf8

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
open Matrix
noncomputable section
open PivotProductBound
namespace GroundTheory.Heights₂.Heights
namespace PivotProductBound
theorem _root_.solution (hLB : LeadMinorBasic.Statement) : PivotProductBound.Statement := by
  intro d r S hS hrd α ε hε hα hεp P hP
  have hpos : ∀ i ∈ P, 0 < pivot S i := fun i hi => pivot_pos hLB hS (hP i hi)
  set m := max 1 α with hm
  set c := min 1 ε with hc
  have hm1 : 1 ≤ m := le_max_left _ _
  have hm0 : 0 < m := lt_of_lt_of_le one_pos hm1
  have hc0 : 0 < c := lt_min one_pos hε
  have hc1 : c ≤ 1 := min_le_left _ _
  set A := P.filter (· < r) with hA
  set B := P.filter (fun i => ¬ i < r) with hB
  have hAr : A ⊆ Finset.range r := by
    intro i hi
    rw [Finset.mem_filter] at hi
    exact Finset.mem_range.2 hi.2

  have hQpos : ∀ i ∈ Finset.range r \ A, 0 < pivot S i := fun i hi =>
    pivot_pos hLB hS (lt_of_lt_of_le (Finset.mem_range.1 (Finset.mem_sdiff.1 hi).1) hrd)
  have hQ : ∏ i ∈ Finset.range r \ A, pivot S i ≤ m ^ r := by
    calc ∏ i ∈ Finset.range r \ A, pivot S i ≤ ∏ _i ∈ Finset.range r \ A, m :=
          Finset.prod_le_prod (fun i hi => (hQpos i hi).le) (fun i hi =>
            (hα i (Finset.mem_range.1 (Finset.mem_sdiff.1 hi).1)).trans (le_max_right _ _))
      _ = m ^ (Finset.range r \ A).card := Finset.prod_const _
      _ ≤ m ^ r := pow_le_pow_right₀ hm1
          ((Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_range r).le)
  have hL : leadMinor S r = (∏ i ∈ Finset.range r \ A, pivot S i) * ∏ i ∈ A, pivot S i := by
    rw [Finset.prod_sdiff hAr, prod_range_pivot hLB hS r hrd]
  have hApos : 0 < ∏ i ∈ A, pivot S i :=
    Finset.prod_pos fun i hi => hpos i (Finset.mem_filter.1 hi).1

  have h1 : m⁻¹ ^ r * leadMinor S r ≤ ∏ i ∈ A, pivot S i := by
    rw [hL, ← mul_assoc]
    have : m⁻¹ ^ r * ∏ i ∈ Finset.range r \ A, pivot S i ≤ 1 := by
      rw [inv_pow]
      exact inv_mul_le_one_of_le₀ hQ (pow_nonneg hm0.le r)
    calc m⁻¹ ^ r * (∏ i ∈ Finset.range r \ A, pivot S i) * ∏ i ∈ A, pivot S i
        ≤ 1 * ∏ i ∈ A, pivot S i := mul_le_mul_of_nonneg_right this hApos.le
      _ = _ := one_mul _

  have h2 : c ^ d ≤ ∏ i ∈ B, pivot S i := by
    have hBd : B.card ≤ d := by
      calc B.card ≤ (Finset.range d).card := Finset.card_le_card (fun i hi =>
            Finset.mem_range.2 (hP i (Finset.mem_filter.1 hi).1))
        _ = d := Finset.card_range d
    calc c ^ d ≤ c ^ B.card := pow_le_pow_of_le_one hc0.le hc1 hBd
      _ = ∏ _i ∈ B, c := (Finset.prod_const _).symm
      _ ≤ ∏ i ∈ B, pivot S i := Finset.prod_le_prod (fun _ _ => hc0.le) (fun i hi => by
          rw [Finset.mem_filter] at hi
          exact (min_le_right _ _).trans (hεp i (not_lt.1 hi.2) (hP i hi.1)))
  rw [← Finset.prod_filter_mul_prod_filter_not P (· < r), mul_assoc, mul_comm]
  exact mul_le_mul h1 h2 (pow_nonneg hc0.le d) hApos.le
end PivotProductBound
end GroundTheory.Heights₂.Heights
