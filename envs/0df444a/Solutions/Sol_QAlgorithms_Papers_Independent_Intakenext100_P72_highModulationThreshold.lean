-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P72.highModulationThreshold
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T10:07:11.551611+00:00
-- url     : https://prove2.me/submissions/71b263b2-a653-4124-ac9a-e4a6875a1fca

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P72

noncomputable section

open Filter

open scoped Topology

namespace Aux_P72_highMod

open QAlgorithms.Papers.Independent.Intakenext100.P72

theorem thr_props (G s : ℝ) (hGs : 0 ≤ G * s) :
    0 < noiseThreshold G s ∧
    noiseThreshold G s ^ 2 + G * s * noiseThreshold G s = 1 ∧
    ∀ x : ℝ, 0 ≤ x → (x ^ 2 + G * s * x - 1 < 0 ↔ x < noiseThreshold G s) := by
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (G ^ 2 * s ^ 2 + 4) := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg _
  have hr2 : r ^ 2 = G ^ 2 * s ^ 2 + 4 := by rw [hr]; exact Real.sq_sqrt (by positivity)
  have hT : noiseThreshold G s = (r - G * s) / 2 := by unfold noiseThreshold; rw [hr]
  have hgt : G * s < r := by nlinarith
  refine ⟨by rw [hT]; linarith, by rw [hT]; linear_combination (1 / 4) * hr2, ?_⟩
  intro x hx
  rw [hT]
  have hfac : x ^ 2 + G * s * x - 1 = (x - (r - G * s) / 2) * (x + (r + G * s) / 2) := by
    linear_combination (1 / 4) * hr2
  have hpos : 0 < x + (r + G * s) / 2 := by linarith
  rw [hfac]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have := mul_nonneg (sub_nonneg.mpr hc) hpos.le
    linarith
  · intro h
    exact mul_neg_of_neg_of_pos (by linarith) hpos

end Aux_P72_highMod

open QAlgorithms.Papers.Independent.Intakenext100.P72 in
theorem solution
    (G chi s : ℝ) (hG : 0 < G) (hchi : |1 - G| ≤ G * chi) (hs : 0 < s) :
    Tendsto (fun V : ℝ => varianceProduct G chi V s) atTop
      (nhds (G * chi * (G * chi + G * s))) ∧
    ((G * chi * (G * chi + G * s) < 1) ↔
      ((G * chi) ^ 2 + G * s * (G * chi) - 1 < 0)) ∧
    ((G * chi * (G * chi + G * s) < 1) ↔ G * chi < noiseThreshold G s) ∧
    (∀ s1 s2 : ℝ, 0 < s1 → s1 ≤ s2 →
      noiseThreshold G s2 ≤ noiseThreshold G s1) := by
  have hx0 : 0 ≤ G * chi := le_trans (abs_nonneg _) hchi
  have hGs : 0 ≤ G * s := by positivity
  have e2 : (G * chi * (G * chi + G * s) < 1) ↔ ((G * chi) ^ 2 + G * s * (G * chi) - 1 < 0) := by
    have : G * chi * (G * chi + G * s) = (G * chi) ^ 2 + G * s * (G * chi) := by ring
    rw [this]
    constructor <;> intro h <;> linarith
  refine ⟨?_, e2, ?_, ?_⟩
  · have h1 : Tendsto (fun V : ℝ => G / V) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 := (tendsto_const_nhds (x := G * chi)).add h1
    have h3 := h2.const_mul (G * chi + G * s)
    rw [add_zero] at h3
    have e : (G * chi + G * s) * (G * chi) = G * chi * (G * chi + G * s) := by ring
    rw [e] at h3
    exact h3
  · rw [e2]
    exact (Aux_P72_highMod.thr_props G s hGs).2.2 (G * chi) hx0
  · intro s1 s2 hs1 hs12
    have p1 := Aux_P72_highMod.thr_props G s1 (by positivity)
    have p2 := Aux_P72_highMod.thr_props G s2 (by nlinarith)
    by_contra hc
    push_neg at hc
    obtain ⟨t1pos, q1, -⟩ := p1
    obtain ⟨t2pos, q2, -⟩ := p2
    have h1 : noiseThreshold G s1 ^ 2 < noiseThreshold G s2 ^ 2 := by nlinarith
    have h2 : s1 * noiseThreshold G s1 ≤ s2 * noiseThreshold G s2 :=
      mul_le_mul hs12 hc.le t1pos.le (by linarith)
    have h3 : G * (s1 * noiseThreshold G s1) ≤ G * (s2 * noiseThreshold G s2) :=
      mul_le_mul_of_nonneg_left h2 hG.le
    nlinarith
