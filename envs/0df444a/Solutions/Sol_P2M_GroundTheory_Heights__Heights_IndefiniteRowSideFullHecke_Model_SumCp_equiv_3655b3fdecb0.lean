-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_SumCp_equiv_3655b3fdecb0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:05:25.624462+00:00
-- url     : https://prove2.me/submissions/6b58f5d3-1bf2-4061-89e3-d91a38391323

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_CpEqPrimeWeight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_cp_eq_primeWeight_44895a727b2d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_sumCp_term_nonneg_37bed98ff91a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace SumCp
theorem _root_.solution :
    GroundTheory.Heights₂.Heights.Model.SumCp.Statement ↔ SumCp.Statement := by
  constructor
  · intro hA d hd
    obtain ⟨C, hC⟩ := hA d hd
    refine ⟨C, fun B hB S hS => ?_⟩
    have h := hC B hB S fun p hp => ⟨(hS p hp).1, Or.inl (hS p hp).2⟩
    simpa [cp_eq_primeWeight] using h
  · intro hB d hd
    obtain ⟨C, hC⟩ := hB d hd
    set T := d.natAbs.primeFactors
    set K : ℝ := ∑ p ∈ T, (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p
    have hK : 0 ≤ K := Finset.sum_nonneg fun p hp =>
      sumCp_term_nonneg d (Nat.mem_primeFactors.mp hp).1
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    refine ⟨C + K / Real.log 2, fun B hB2 S hS => ?_⟩
    have hlogB : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) hB2
    have hterm : ∀ p ∈ S, (GroundTheory.Heights₂.Heights.Model.primeWeight p +
        2 * (padicValInt p d : ℝ)) * Real.log p =
        (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p := fun p _ => by
      rw [cp_eq_primeWeight]
    have hsum : ∑ p ∈ S, (GroundTheory.Heights₂.Heights.Model.primeWeight p +
        2 * (padicValInt p d : ℝ)) * Real.log p =
        ∑ p ∈ S, (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p :=
      Finset.sum_congr rfl hterm

    have h1 : ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) ≤ B),
        (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p ≤ C * Real.log B :=
      hC B hB2 _ fun p hp => by
        obtain ⟨hpS, hpB⟩ := Finset.mem_filter.mp hp
        exact ⟨(hS p hpS).1, hpB⟩

    have h2 : ∑ p ∈ S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ B),
        (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p ≤ K := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p hp _ => ?_)
      · obtain ⟨hpS, hpB⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpp, hor⟩ := hS p hpS
        have hpd : (p : ℤ) ∣ d := hor.resolve_left hpB
        exact Nat.mem_primeFactors.mpr ⟨hpp, Int.natCast_dvd.mp hpd, Int.natAbs_ne_zero.mpr hd⟩
      · exact sumCp_term_nonneg d (Nat.mem_primeFactors.mp hp).1
    have h3 : K ≤ K / Real.log 2 * Real.log B := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hlogB hK
    have hsplit := Finset.sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) ≤ B)
      (fun p => (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p)
    have : ∑ p ∈ S, (GroundTheory.Heights₂.Heights.Model.primeWeight p +
        2 * (padicValInt p d : ℝ)) * Real.log p ≤ (C + K / Real.log 2) * Real.log B := by
      rw [hsum, ← hsplit, add_mul]
      linarith
    exact this
end SumCp
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
