-- Prove2me | solution 1 for SennottDP.SEN.prop_7_2_4_sen_any_state
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:50:56.973028+00:00
-- url     : https://prove2.me/submissions/c1e72190-0c73-48e6-a41a-c2cf76ff3ac8

import Mathlib
import Definitions.Def_SennottDP_SEN_Assumptions



namespace SennottDP.SEN

open scoped ENNReal NNReal

lemma s724_ereal_sub {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a : EReal) - (b : EReal) = ((a.toReal - b.toReal : ℝ) : EReal) := by
  rw [EReal.coe_sub, EReal.coe_ennreal_toReal ha, EReal.coe_ennreal_toReal hb]

lemma s724_fin_of_le {a b : ℝ≥0∞} (hb : b ≠ ⊤) (m : ℝ) (h : (a : EReal) - (b : EReal) ≤ (m : EReal)) :
    a ≠ ⊤ := by
  intro ha
  subst ha
  rw [← EReal.coe_ennreal_toReal hb] at h
  simp at h

lemma s724_core {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act) (z : S)
    (Mf : S → ℝ) (L : ℝ) (hSEN : SENAssumptions M z Mf L) (x : S) :
    ∃ (Mx : S → ℝ) (Lx : ℝ), SENAssumptions M x Mx Lx := by
  obtain ⟨⟨B, hB⟩, ⟨hM0, hM⟩, ⟨hL0, hL⟩⟩ := hSEN
  have hz : ∀ α ∈ Set.Ioo (0:ℝ) 1, discValue M α z ≠ ⊤ := by
    intro α hα htop
    have := hB α hα
    rw [htop, ENNReal.mul_top (by simp [hα.2])] at this
    exact ENNReal.coe_ne_top (top_le_iff.mp this)
  have hi : ∀ α ∈ Set.Ioo (0:ℝ) 1, ∀ i, discValue M α i ≠ ⊤ := fun α hα i =>
    s724_fin_of_le (hz α hα) (Mf i) (hM α hα i)
  have hMr : ∀ α ∈ Set.Ioo (0:ℝ) 1, ∀ i,
      (discValue M α i).toReal - (discValue M α z).toReal ≤ Mf i := by
    intro α hα i
    have := hM α hα i
    unfold hRel at this
    rw [s724_ereal_sub (hi α hα i) (hz α hα)] at this
    exact_mod_cast this
  have hLr : ∀ α ∈ Set.Ioo (0:ℝ) 1, ∀ i,
      -L ≤ (discValue M α i).toReal - (discValue M α z).toReal := by
    intro α hα i
    have := hL α hα i
    unfold hRel at this
    rw [s724_ereal_sub (hi α hα i) (hz α hα)] at this
    exact_mod_cast this
  refine ⟨fun i => Mf i + L, L + Mf x, ?_, ⟨fun i => by linarith [hM0 i], ?_⟩,
    ⟨by linarith [hM0 x], ?_⟩⟩
  · refine ⟨B + (Mf x).toNNReal, fun α hα => ?_⟩
    have hle : discValue M α x ≤ discValue M α z + ENNReal.ofReal (Mf x) := by
      rw [← ENNReal.ofReal_toReal (hi α hα x), ← ENNReal.ofReal_toReal (hz α hα)]
      rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg (hM0 x)]
      apply ENNReal.ofReal_le_ofReal
      linarith [hMr α hα x]
    calc ENNReal.ofReal (1 - α) * discValue M α x
        ≤ ENNReal.ofReal (1 - α) * (discValue M α z + ENNReal.ofReal (Mf x)) := by gcongr
      _ = ENNReal.ofReal (1 - α) * discValue M α z + ENNReal.ofReal (1 - α) * ENNReal.ofReal (Mf x) := by
          rw [mul_add]
      _ ≤ (B : ℝ≥0∞) + 1 * ENNReal.ofReal (Mf x) := by
          gcongr
          · exact hB α hα
          · rw [← ENNReal.ofReal_one]; apply ENNReal.ofReal_le_ofReal; linarith [hα.1]
      _ = ((B + (Mf x).toNNReal : ℝ≥0) : ℝ≥0∞) := by
          rw [one_mul, ENNReal.coe_add]; rfl
  · intro α hα i
    unfold hRel
    rw [s724_ereal_sub (hi α hα i) (hi α hα x)]
    have h1 := hMr α hα i
    have h2 := hLr α hα x
    exact_mod_cast (by linarith : (discValue M α i).toReal - (discValue M α x).toReal ≤ Mf i + L)
  · intro α hα i
    unfold hRel
    rw [s724_ereal_sub (hi α hα i) (hi α hα x)]
    have h1 := hLr α hα i
    have h2 := hMr α hα x
    exact_mod_cast (by linarith : -(L + Mf x) ≤ (discValue M α i).toReal - (discValue M α x).toReal)

end SennottDP.SEN

open SennottDP.SEN


theorem solution {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act) (z : S)
    (Mf : S → ℝ) (L : ℝ) (hSEN : SENAssumptions M z Mf L) (x : S) :
    ∃ (Mx : S → ℝ) (Lx : ℝ), SENAssumptions M x Mx Lx := by
  exact s724_core M z Mf L hSEN x
