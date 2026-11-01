-- Prove2me | solution 1 for TargetGranularity.SdVsMd.claim_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:02:09.645803+00:00
-- url     : https://prove2.me/submissions/57da0781-7039-4e70-a287-6b73b1495b15

import Mathlib
import Definitions.Def_TargetGranularity_SdVsMd_Model

open TargetGranularity.SdVsMd MeasureTheory Set

theorem solution (p cad ωlo ωhi : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hcad : 0 < cad)
    (hcadp : cad < p) (hlo : 0 ≤ ωlo) (hlohi : ωlo ≤ ωhi) (hhi : ωhi ≤ 1)
    (hcadlo : cad ≤ p * ωlo) (hcadhi : cad ≤ p * (1 - ωhi)) :
    {x ∈ unitSq | 0 ≤ mdAdValue p cad (Set.Icc 0 ωlo ∪ Set.Icc ωhi 1) x} =
      mdSet p (-(cad / (p - cad))) (-((p - cad) / cad)) := by
  set Ω : Set ℝ := Set.Icc 0 ωlo ∪ Set.Icc ωhi 1 with hΩ
  set c : ℝ := cad / p with hc
  have hcpos : 0 < c := div_pos hcad hp0
  have hclo : c ≤ ωlo := by rw [hc, div_le_iff₀ hp0]; linarith
  have hchi : c ≤ 1 - ωhi := by rw [hc, div_le_iff₀ hp0]; linarith
  have hΩsub : Ω ⊆ Icc 0 1 := by
    rintro ω (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, by linarith⟩
    · exact ⟨by linarith, h2⟩
  have hfin : ∀ B : Set ℝ, volume (Ω ∩ B) ≠ ⊤ := by
    intro B
    apply ne_top_of_le_ne_top (measure_Icc_lt_top (μ := (volume : Measure ℝ)) (a := (0:ℝ)) (b := 1)).ne
    exact measure_mono (fun ω hω => hΩsub hω.1)
  have hvolIcc : ∀ a b : ℝ, (volume (Icc a b)).toReal = max (b - a) 0 := by
    intro a b
    rw [Real.volume_Icc, ENNReal.toReal_ofReal']
  -- lower bound: Icc a (a+c) ⊆ Ω ∩ B gives c ≤ vol
  have hlow : ∀ (a : ℝ) (B : Set ℝ), Icc a (a + c) ⊆ Ω ∩ B →
      c ≤ (volume (Ω ∩ B)).toReal := by
    intro a B h
    have := ENNReal.toReal_mono (hfin B) (measure_mono h)
    rw [hvolIcc, show a + c - a = c by ring, max_eq_left hcpos.le] at this
    exact this
  -- upper bound
  have hup : ∀ (a b : ℝ) (B : Set ℝ), b - a < c → Ω ∩ B ⊆ Icc a b →
      (volume (Ω ∩ B)).toReal < c := by
    intro a b B hab h
    have := ENNReal.toReal_mono (by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (measure_mono h)
    rw [hvolIcc] at this
    exact lt_of_le_of_lt this (max_lt hab hcpos)
  have V1 : ∀ t : ℝ, c ≤ (volume (Ω ∩ Iic t)).toReal ↔ c ≤ t := by
    intro t
    constructor
    · intro h
      by_contra ht
      push Not at ht
      refine absurd h (not_le.mpr (hup 0 t _ (by linarith) ?_))
      rintro ω ⟨(⟨h1, h2⟩ | ⟨h1, h2⟩), h3⟩
      · exact ⟨h1, h3⟩
      · simp only [mem_Iic] at h3; linarith
    · intro ht
      apply hlow 0
      rintro ω ⟨h1, h2⟩
      exact ⟨Or.inl ⟨h1, by linarith⟩, by simp only [mem_Iic]; linarith⟩
  have V2 : ∀ s : ℝ, c ≤ (volume (Ω ∩ Ici s)).toReal ↔ s ≤ 1 - c := by
    intro s
    constructor
    · intro h
      by_contra hs
      push Not at hs
      refine absurd h (not_le.mpr (hup s 1 _ (by linarith) ?_))
      rintro ω ⟨(⟨h1, h2⟩ | ⟨h1, h2⟩), h3⟩
      · simp only [mem_Ici] at h3; linarith
      · exact ⟨h3, h2⟩
    · intro hs
      apply hlow (1 - c)
      rintro ω ⟨h1, h2⟩
      exact ⟨Or.inr ⟨by linarith, by linarith⟩, by simp only [mem_Ici]; linarith⟩
  have V3 : c ≤ (volume (Ω ∩ univ)).toReal := by
    apply hlow 0
    rintro ω ⟨h1, h2⟩
    exact ⟨Or.inl ⟨h1, by linarith⟩, mem_univ _⟩
  have V4 : (volume (Ω ∩ (∅ : Set ℝ))).toReal = 0 := by simp
  have hval : ∀ x : ℝ × ℝ, 0 ≤ mdAdValue p cad Ω x ↔
      c ≤ (volume (Ω ∩ {ω : ℝ | p ≤ util ω x.1 x.2})).toReal := by
    intro x
    simp only [mdAdValue, hc]
    rw [div_le_iff₀ hp0]
    constructor <;> intro h <;> linarith
  have hpc : 0 < p - cad := by linarith
  set k1 : ℝ := cad / (p - cad) with hk1d
  set k2 : ℝ := (p - cad) / cad with hk2d
  have hk1 : k1 * (p - cad) = cad := by rw [hk1d]; field_simp
  have hk2 : k2 * cad = p - cad := by rw [hk2d]; field_simp
  have hk1pos : 0 < k1 := div_pos hcad hpc
  have hk2pos : 0 < k2 := div_pos hpc hcad
  ext ⟨α, β⟩
  simp only [mdSet, mem_ofPred_eq, mem_inter_iff, mem_union]
  rw [hval]
  simp only
  refine and_congr_right fun hx => ?_
  rcases lt_trichotomy α β with hab | hab | hab
  · -- α < β
    have hA : {ω : ℝ | p ≤ util ω α β} = Iic ((β - p) / (β - α)) := by
      ext ω
      simp only [mem_ofPred_eq, mem_Iic, util]
      rw [le_div_iff₀ (by linarith)]
      constructor <;> intro h <;> nlinarith
    rw [hA, V1, hc, div_le_div_iff₀ hp0 (by linarith)]
    constructor
    · intro h
      by_cases hap : α ≤ p
      · left
        refine ⟨?_, hap⟩
        have e : -k1 * α + p * (1 - -k1) = p + k1 * (p - α) := by ring
        rw [e]
        have : k1 * (p - α) * (p - cad) = cad * (p - α) := by rw [mul_right_comm, hk1]
        by_contra hn
        push Not at hn
        have := mul_lt_mul_of_pos_right hn hpc
        nlinarith
      · right
        push Not at hap
        refine ⟨?_, hap⟩
        have e : -k2 * α + p * (1 - -k2) = p - k2 * (α - p) := by ring
        rw [e]
        nlinarith [mul_pos hk2pos (sub_pos.mpr hap)]
    · rintro (⟨h, hap⟩ | ⟨h, hap⟩)
      · have e : -k1 * α + p * (1 - -k1) = p + k1 * (p - α) := by ring
        rw [e] at h
        have : k1 * (p - α) * (p - cad) = cad * (p - α) := by rw [mul_right_comm, hk1]
        have := mul_le_mul_of_nonneg_right h hpc.le
        nlinarith
      · nlinarith
  · -- α = β
    subst hab
    have hA : {ω : ℝ | p ≤ util ω α α} = {_ω : ℝ | p ≤ α} := by
      ext ω; simp only [mem_ofPred_eq, util]; constructor <;> intro h <;> linarith
    rw [hA]
    by_cases hpa : p ≤ α
    · have : {_ω : ℝ | p ≤ α} = univ := by ext; simp [hpa]
      rw [this]
      refine iff_of_true V3 ?_
      rcases le_or_gt α p with h | h
      · left
        refine ⟨?_, h⟩
        have : α = p := le_antisymm h hpa
        subst this; nlinarith
      · right
        refine ⟨?_, h⟩
        nlinarith [mul_pos hk2pos (sub_pos.mpr h)]
    · have : {_ω : ℝ | p ≤ α} = ∅ := by ext; simp [hpa]
      rw [this, V4]
      push Not at hpa
      refine iff_of_false (not_le.mpr hcpos) ?_
      rintro (⟨h, _⟩ | ⟨_, h⟩)
      · nlinarith [mul_pos hk1pos (sub_pos.mpr hpa)]
      · linarith
  · -- α > β
    have hA : {ω : ℝ | p ≤ util ω α β} = Ici ((p - β) / (α - β)) := by
      ext ω
      simp only [mem_ofPred_eq, mem_Ici, util]
      rw [div_le_iff₀ (by linarith)]
      constructor <;> intro h <;> nlinarith
    rw [hA, V2, hc, div_le_iff₀ (by linarith)]
    have e1 : (1 - cad / p) * (α - β) = (p - cad) * (α - β) / p := by field_simp
    rw [e1, le_div_iff₀ hp0]
    constructor
    · intro h
      by_cases hap : α ≤ p
      · exfalso
        nlinarith [mul_pos hcad (sub_pos.mpr hab)]
      · right
        push Not at hap
        refine ⟨?_, hap⟩
        have e : -k2 * α + p * (1 - -k2) = p - k2 * (α - p) := by ring
        rw [e]
        have : k2 * (α - p) * cad = (p - cad) * (α - p) := by rw [mul_right_comm, hk2]
        by_contra hn
        push Not at hn
        have := mul_lt_mul_of_pos_right hn hcad
        nlinarith
    · rintro (⟨h, hap⟩ | ⟨h, hap⟩)
      · have e : -k1 * α + p * (1 - -k1) = p + k1 * (p - α) := by ring
        rw [e] at h
        nlinarith [mul_nonneg hk1pos.le (sub_nonneg.mpr hap)]
      · have e : -k2 * α + p * (1 - -k2) = p - k2 * (α - p) := by ring
        rw [e] at h
        have : k2 * (α - p) * cad = (p - cad) * (α - p) := by rw [mul_right_comm, hk2]
        have := mul_le_mul_of_nonneg_right h hcad.le
        nlinarith
