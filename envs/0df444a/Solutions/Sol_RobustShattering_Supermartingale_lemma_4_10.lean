-- Prove2me | solution 1 for RobustShattering.Supermartingale.lemma_4_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:35:58.48384+00:00
-- url     : https://prove2.me/submissions/a8e30aa6-7b6b-40bf-90a8-3411ffb3de84

import Mathlib
import Definitions.Def_LocalLLL_Main_GraphModel
import Definitions.Def_RobustShattering_Supermartingale_Shatterable
import Theorems.Thm_RobustShattering_Supermartingale_lemma_4_9

section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace RobustShattering.Supermartingale

theorem chk_lemma_4_10 {V : Type} [Fintype V] (G : SimpleGraph V) {T : ℕ}
    {Ω : V → Fin T → Type} [∀ u k, MeasurableSpace (Ω u k)]
    (μ : ∀ u k, Measure (Ω u k)) [∀ u k, IsProbabilityMeasure (μ u k)]
    (c : ℕ) (X Y : ℝ≥0) (hY : 0 < Y) (B : Randomness Ω → Set V)
    (hP : Shatterable G c X Y μ B)
    (S : Finset V) (hS : LocalLLL.Main.separated G (2 * c) (S : Set V)) :
    processMeasure μ {ω | (S : Set V) ⊆ B ω} ≤ (((X / Y) ^ S.card : ℝ≥0) : ℝ≥0∞) := by
  classical
  obtain ⟨γ, hγ⟩ := hP
  have h9 := lemma_4_9 G μ c X Y hY B γ hγ S hS T le_rfl
  have hF : Measurable (fun ω : Randomness Ω => ∏ v ∈ S, (γ v T ω : ℝ≥0∞)) :=
    Finset.measurable_prod _ (fun v _ =>
      measurable_coe_nnreal_ennreal.comp (hγ.measurable v T le_rfl))
  have hm := mul_meas_ge_le_lintegral₀ (μ := processMeasure μ) hF.aemeasurable
    ((Y : ℝ≥0∞) ^ S.card)
  have hsub : {ω | (S : Set V) ⊆ B ω} ⊆
      {ω | (Y : ℝ≥0∞) ^ S.card ≤ ∏ v ∈ S, (γ v T ω : ℝ≥0∞)} := by
    intro ω hω
    calc (Y : ℝ≥0∞) ^ S.card = ∏ v ∈ S, (Y : ℝ≥0∞) := (Finset.prod_const _).symm
      _ ≤ _ := Finset.prod_le_prod' (fun v hv =>
          by exact_mod_cast hγ.high_post_shattering_cost v ω (hω hv))
  have hYn : (Y : ℝ≥0) ^ S.card ≠ 0 := pow_ne_zero _ hY.ne'
  rw [div_pow, ENNReal.coe_div hYn, ENNReal.coe_pow, ENNReal.coe_pow,
    ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hYn)) (Or.inl (by simp))]
  calc processMeasure μ {ω | (S : Set V) ⊆ B ω} * (Y : ℝ≥0∞) ^ S.card
      ≤ processMeasure μ {ω | (Y : ℝ≥0∞) ^ S.card ≤ ∏ v ∈ S, (γ v T ω : ℝ≥0∞)}
          * (Y : ℝ≥0∞) ^ S.card := by gcongr
    _ = _ := mul_comm _ _
    _ ≤ _ := hm.trans h9

end RobustShattering.Supermartingale
end

theorem solution : type_of% @RobustShattering.Supermartingale.chk_lemma_4_10 := @RobustShattering.Supermartingale.chk_lemma_4_10
