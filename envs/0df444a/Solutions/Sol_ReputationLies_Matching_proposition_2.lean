-- Prove2me | solution 1 for ReputationLies.Matching.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:00:02.477841+00:00
-- url     : https://prove2.me/submissions/4eff2031-3ca9-49df-bae7-c071c26d6969

import Mathlib
import Definitions.Def_ReputationLies_Matching_Model
import Theorems.Thm_ReputationLies_Matching_proposition_1
import Theorems.Thm_ReputationLies_Matching_step_5_threshold

open Set MeasureTheory ReputationLies.Matching

namespace RepLiesProp2Aux

theorem lie_eq (P : Primitives) (hP : P.Standing) (r : ℝ) (hr : 0 < r) (σ : Profile)
    (hσ : IsEquilibrium P σ r) :
    ∃ bstar ∈ Ioc (0 : ℝ) 1, lieProb P σ = 1 - P.Z bstar ∧
      (bstar = 1 ↔ P.Bbar ≤ P.L r) ∧ (bstar < 1 → P.lieGain bstar = P.L r) := by
  obtain ⟨bstar, hb, -, hAf, -, -, -, -, hb1, hlg⟩ := (proposition_1 P hP r hr).2.2 σ hσ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hμB, hμB1, -⟩ := hP
  refine ⟨bstar, hb, ?_, hb1, hlg⟩
  unfold lieProb recProb
  have hcompl : P.μB (Icc (0:ℝ) 1)ᶜ = 0 := by
    rw [measure_compl measurableSet_Icc (measure_ne_top _ _), hμB1, measure_univ]; simp
  have hIic1 : P.μB (Iic 1) = 1 := by
    apply le_antisymm prob_le_one
    rw [← hμB1]; exact measure_mono Icc_subset_Iic_self
  have hSI : {b | σ.σA b false = true} ∩ Icc 0 1 = Ioc bstar 1 := by
    ext b
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨h, h0, h1⟩
      exact ⟨(hAf b ⟨h0, h1⟩).1 h, h1⟩
    · rintro ⟨h, h1⟩
      have h0 : 0 ≤ b := le_trans hb.1.le h.le
      exact ⟨(hAf b ⟨h0, h1⟩).2 h, h0, h1⟩
  have hset : Ioc bstar 1 = Iic 1 \ Iic bstar := by
    ext x; simp only [mem_Ioc, mem_sdiff, mem_Iic, not_le]; exact and_comm
  rw [← measure_inter_conull hcompl, hSI, hset, measure_sdiff (Iic_subset_Iic.mpr hb.2)
    measurableSet_Iic.nullMeasurableSet (measure_ne_top _ _), hIic1,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
  simp [Primitives.Z]

end RepLiesProp2Aux

open RepLiesProp2Aux in
theorem solution (P : Primitives) (hP : P.Standing) :
    ∀ (r r' : ℝ) (σ σ' : Profile), 0 < r → r ≤ r' →
      IsEquilibrium P σ r → IsEquilibrium P σ' r' →
        lieProb P σ' ≤ lieProb P σ ∧
        (r < r' → P.L r < P.Bbar → lieProb P σ' < lieProb P σ) := by
  intro r r' σ σ' hr hrr hσ hσ'
  have hr' : 0 < r' := lt_of_lt_of_le hr hrr
  obtain ⟨hlgM, -, -, -⟩ := step_5_threshold P hP
  obtain ⟨b, hb, hlie, hb1, hlg⟩ := lie_eq P hP r hr σ hσ
  obtain ⟨b', hb', hlie', hb1', hlg'⟩ := lie_eq P hP r' hr' σ' hσ'
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hL', -, -, -, hZ, -⟩ := hP'
  -- L is strictly increasing on (0, ∞)
  have hLmono : StrictMonoOn P.L (Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    · intro x hx
      have hd : DifferentiableAt ℝ P.L x := by
        by_contra h
        have := deriv_zero_of_not_differentiableAt h
        linarith [hL' x hx]
      exact hd.continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      exact hL' x hx
  have hLle : P.L r ≤ P.L r' := hLmono.monotoneOn hr hr' hrr
  have hbI : b ∈ Icc (0:ℝ) 1 := ⟨hb.1.le, hb.2⟩
  have hbI' : b' ∈ Icc (0:ℝ) 1 := ⟨hb'.1.le, hb'.2⟩
  have hweak : b ≤ b' := by
    rcases eq_or_lt_of_le hb'.2 with h | h
    · rw [h]; exact hb.2
    · have hL'B : P.L r' < P.Bbar := by
        by_contra hc; exact absurd (hb1'.2 (not_lt.mp hc)) h.ne
      have hb1lt : b < 1 := by
        rcases eq_or_lt_of_le hb.2 with h2 | h2
        · exact absurd (hb1.1 h2) (not_le.mpr (lt_of_le_of_lt hLle hL'B))
        · exact h2
      have : P.lieGain b ≤ P.lieGain b' := by rw [hlg hb1lt, hlg' h]; exact hLle
      exact (hlgM.le_iff_le hb hb').mp this
  refine ⟨?_, ?_⟩
  · rw [hlie, hlie']
    have := hZ.monotoneOn hbI hbI' hweak
    linarith
  · intro hlt hLB
    have hb1lt : b < 1 := by
      rcases eq_or_lt_of_le hb.2 with h2 | h2
      · exact absurd (hb1.1 h2) (not_le.mpr hLB)
      · exact h2
    have hstrict : b < b' := by
      rcases eq_or_lt_of_le hb'.2 with h | h
      · rw [h]; exact hb1lt
      · have hLlt : P.L r < P.L r' := hLmono hr hr' hlt
        have : P.lieGain b < P.lieGain b' := by rw [hlg hb1lt, hlg' h]; exact hLlt
        exact (hlgM.lt_iff_lt hb hb').mp this
    rw [hlie, hlie']
    have := hZ hbI hbI' hstrict
    linarith
