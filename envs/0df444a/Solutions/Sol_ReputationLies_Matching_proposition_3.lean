-- Prove2me | solution 1 for ReputationLies.Matching.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:54:20.235204+00:00
-- url     : https://prove2.me/submissions/616cef23-7ecf-450d-a955-6034358f4868

import Mathlib
import Definitions.Def_ReputationLies_Matching_Model
import Theorems.Thm_ReputationLies_Matching_proposition_1
import Theorems.Thm_ReputationLies_Matching_proposition_2
import Theorems.Thm_ReputationLies_Matching_step_4_bayes_belief
import Theorems.Thm_ReputationLies_Matching_eq_14_fair_gamble
import Theorems.Thm_ReputationLies_Matching_mps_step
import Theorems.Thm_ReputationLies_Matching_topHeavy_strictConvexOn

open Set MeasureTheory ReputationLies.Matching

namespace RepLiesProp3Aux

/-- In an equilibrium at `r > 0` with threshold `b∗`, the lying probability is `1 − Z(b∗)` and the
ex-ante hiring probability is the fair-gamble hiring probability at `sR(b∗)`. -/
theorem eq_data (P : Primitives) (hP : P.Standing) (r : ℝ) (hr : 0 < r) (σ : Profile)
    (hσ : IsEquilibrium P σ r) :
    ∃ bstar ∈ Ioc (0 : ℝ) 1, lieProb P σ = 1 - P.Z bstar ∧
      exAnteHireProb P σ = P.gambleHire (P.sRof bstar) ∧ P.sRof bstar ∈ Ioc P.sL 1 := by
  obtain ⟨bstar, hb, hA, hAf, hNR, -, hR, -, -, -⟩ := (proposition_1 P hP r hr).2.2 σ hσ
  have hP' := hP
  obtain ⟨hsL, hsLH, hsH1, hp0, hp1, -, -, -, -, -, -, -, hμB, hμB1, -, -, -⟩ := hP'
  obtain ⟨-, hmono, -, h0, h1⟩ := step_4_bayes_belief P hP
  refine ⟨bstar, hb, ?_, ?_, ?_⟩
  · -- lying probability
    unfold lieProb recProb
    set S := {b | σ.σA b false = true} with hS
    have hcompl : P.μB (Icc (0:ℝ) 1)ᶜ = 0 := by
      rw [measure_compl measurableSet_Icc (measure_ne_top _ _), hμB1, measure_univ]
      simp
    have hSI : S ∩ Icc 0 1 = Ioc bstar 1 := by
      ext b
      simp only [hS, mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_Ioc]
      constructor
      · rintro ⟨h, h0, h1⟩
        exact ⟨(hAf b ⟨h0, h1⟩).1 h, h1⟩
      · rintro ⟨h, h1⟩
        have h0 : 0 ≤ b := le_trans hb.1.le h.le
        exact ⟨(hAf b ⟨h0, h1⟩).2 h, h0, h1⟩
    have hSmeas : P.μB S = P.μB (Ioc bstar 1) := by
      rw [← hSI]
      apply le_antisymm
      · calc P.μB S ≤ P.μB (S ∩ Icc 0 1) + P.μB (S \ Icc 0 1) := by
              conv_lhs => rw [← inter_union_sdiff S (Icc 0 1)]
              exact measure_union_le _ _
          _ ≤ P.μB (S ∩ Icc 0 1) + P.μB (Icc 0 1)ᶜ := by
              gcongr
              exact sdiff_subset_compl _ _
          _ = P.μB (S ∩ Icc 0 1) := by rw [hcompl, add_zero]
      · exact measure_mono inter_subset_left
    have hIic1 : P.μB (Iic 1) = 1 := by
      apply le_antisymm prob_le_one
      rw [← hμB1]
      exact measure_mono Icc_subset_Iic_self
    have hset : Ioc bstar 1 = Iic 1 \ Iic bstar := by
      ext x; simp only [mem_Ioc, mem_sdiff, mem_Iic, not_le]; exact and_comm
    rw [hSmeas, hset, measure_sdiff (Iic_subset_Iic.mpr hb.2)
      measurableSet_Iic.nullMeasurableSet (measure_ne_top _ _), hIic1,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
    simp [Primitives.Z]
  · -- hiring probability
    obtain ⟨h14a, h14b, h14c⟩ := eq_14_fair_gamble P hP r hr σ hσ
    have hshat : P.sL < P.shat := by
      unfold Primitives.shat; nlinarith
    have hbm : P.sRof 0 < P.sRof bstar :=
      hmono ⟨le_refl 0, zero_le_one⟩ ⟨hb.1.le, hb.2⟩ hb.1
    rw [h0] at hbm
    rw [← hR] at hbm
    rw [hNR] at h14b
    have hne : σ.sR - P.sL ≠ 0 := by linarith
    have hq : msgProb P σ true = (P.shat - P.sL) / (σ.sR - P.sL) := by
      field_simp; linarith
    rw [h14c, hNR, hq, ← hR]
    rfl
  · have hshat : P.sL < P.shat := by
      unfold Primitives.shat; nlinarith
    have hbm : P.sRof 0 < P.sRof bstar :=
      hmono ⟨le_refl 0, zero_le_one⟩ ⟨hb.1.le, hb.2⟩ hb.1
    have hb1 : P.sRof bstar ≤ P.sRof 1 :=
      hmono.monotoneOn ⟨hb.1.le, hb.2⟩ ⟨zero_le_one, le_refl 1⟩ hb.2
    rw [h0] at hbm
    rw [h1] at hb1
    exact ⟨by linarith, by linarith⟩

end RepLiesProp3Aux

open RepLiesProp3Aux in
theorem solution (P : Primitives) (hP : P.Standing) :
    (P.TopHeavy →
      ∀ (r r' : ℝ) (σ σ' : Profile), 0 < r → r ≤ r' →
        IsEquilibrium P σ r → IsEquilibrium P σ' r' →
          exAnteHireProb P σ ≤ exAnteHireProb P σ' ∧
          (r < r' → P.L r < P.Bbar → exAnteHireProb P σ < exAnteHireProb P σ')) ∧
    (P.BottomHeavy →
      ∀ (r r' : ℝ) (σ σ' : Profile), 0 < r → r ≤ r' →
        IsEquilibrium P σ r → IsEquilibrium P σ' r' →
          exAnteHireProb P σ' ≤ exAnteHireProb P σ ∧
          (r < r' → P.L r < P.Bbar → exAnteHireProb P σ' < exAnteHireProb P σ)) := by
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hZ, -⟩ := hP'
  obtain ⟨-, hmono, -, -, -⟩ := step_4_bayes_belief P hP
  -- common comparison of the equilibrium beliefs
  have key : ∀ (r r' : ℝ) (σ σ' : Profile), 0 < r → r ≤ r' →
      IsEquilibrium P σ r → IsEquilibrium P σ' r' →
      ∃ s ∈ Ioc P.sL 1, ∃ s' ∈ Ioc P.sL 1,
        exAnteHireProb P σ = P.gambleHire s ∧ exAnteHireProb P σ' = P.gambleHire s' ∧
        s ≤ s' ∧ (r < r' → P.L r < P.Bbar → s < s') := by
    intro r r' σ σ' hr hrr hσ hσ'
    have hr' : 0 < r' := lt_of_lt_of_le hr hrr
    obtain ⟨b, hb, hlie, hhire, hs⟩ := eq_data P hP r hr σ hσ
    obtain ⟨b', hb', hlie', hhire', hs'⟩ := eq_data P hP r' hr' σ' hσ'
    obtain ⟨h2w, h2s⟩ := proposition_2 P hP r r' σ σ' hr hrr hσ hσ'
    have hbI : b ∈ Icc (0:ℝ) 1 := ⟨hb.1.le, hb.2⟩
    have hbI' : b' ∈ Icc (0:ℝ) 1 := ⟨hb'.1.le, hb'.2⟩
    refine ⟨_, hs, _, hs', hhire, hhire', ?_, ?_⟩
    · have : P.Z b ≤ P.Z b' := by linarith
      have hbb : b ≤ b' := (hZ.le_iff_le hbI hbI').mp this
      exact (hmono.le_iff_le hbI hbI').mpr hbb
    · intro hlt hL
      have : P.Z b < P.Z b' := by linarith [h2s hlt hL]
      have hbb : b < b' := (hZ.lt_iff_lt hbI hbI').mp this
      exact hmono hbI hbI' hbb
  obtain ⟨hconv, hconc⟩ := topHeavy_strictConvexOn P hP
  obtain ⟨hmps1, hmps2⟩ := mps_step P hP
  constructor
  · intro hT r r' σ σ' hr hrr hσ hσ'
    obtain ⟨s, hs, s', hs', he, he', hle, hlt⟩ := key r r' σ σ' hr hrr hσ hσ'
    have hG := hmps1 (hconv hT)
    rw [he, he']
    exact ⟨hG.monotoneOn hs hs' hle, fun h1 h2 => hG hs hs' (hlt h1 h2)⟩
  · intro hB r r' σ σ' hr hrr hσ hσ'
    obtain ⟨s, hs, s', hs', he, he', hle, hlt⟩ := key r r' σ σ' hr hrr hσ hσ'
    have hG := hmps2 (hconc hB)
    rw [he, he']
    exact ⟨hG.antitoneOn hs hs' hle, fun h1 h2 => hG hs hs' (hlt h1 h2)⟩
