-- Prove2me | solution 1 for SeatInventory.Gaussian.protection_level_eq_mean_add
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T13:12:14.274172+00:00
-- url     : https://prove2.me/submissions/29d64998-38bc-44ce-8ac6-91bab9be27e8

import Mathlib
import Definitions.Def_SeatInventory_Gaussian_Model

open MeasureTheory ProbabilityTheory

open SeatInventory.Gaussian in
lemma f1ff_tail_strict {a b : ℝ} (h : a < b) :
    tailProb stdNormal b < tailProb stdNormal a := by
  unfold tailProb stdNormal
  have hpos : 0 < gaussianReal 0 1 (Set.Ico a b) := by
    rw [pos_iff_ne_zero]
    intro h0
    have h1 := gaussianReal_absolutelyContinuous' 0 one_ne_zero h0
    rw [Real.volume_Ico, ENNReal.ofReal_eq_zero] at h1
    linarith
  have hU : Set.Ici a = Set.Ico a b ∪ Set.Ici b := (Set.Ico_union_Ici_eq_Ici h.le).symm
  have hd : Disjoint (Set.Ico a b) (Set.Ici b) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_lt.2 hx')
  rw [hU, measure_union hd measurableSet_Ici,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  linarith

open SeatInventory.Gaussian in
lemma f1ff_tail_inj {a b : ℝ} (h : tailProb stdNormal a = tailProb stdNormal b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have := f1ff_tail_strict hab; linarith
  · exact hab
  · have := f1ff_tail_strict hab; linarith

open SeatInventory.Gaussian in
theorem solution (rbar σ f₁ f₂ S Z : ℝ) (hσ : 0 < σ) (hf₂ : 0 < f₂)
    (hf : f₂ < f₁) (hS : IsProtectionLevel rbar σ f₁ f₂ S) (hZ : IsStdNormalLevel f₁ f₂ Z) :
    S = rbar + Z * σ := by
  have hmap : gaussianLaw rbar σ = stdNormal.map (fun x => σ * x + rbar) := by
    unfold gaussianLaw stdNormal
    have : (fun x : ℝ => σ * x + rbar) = (· + rbar) ∘ (σ * ·) := rfl
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_add_const]
    congr 1
    · ring
    · ext; simp <;> rfl
  have hpre : (fun x => σ * x + rbar) ⁻¹' Set.Ici S = Set.Ici ((S - rbar) / σ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ici, div_le_iff₀ hσ]
    constructor <;> intro h <;> linarith
  have hT : tailProb (gaussianLaw rbar σ) S = tailProb stdNormal ((S - rbar) / σ) := by
    unfold tailProb
    rw [hmap, Measure.map_apply (by fun_prop) measurableSet_Ici, hpre]
  have hS' : tailProb (gaussianLaw rbar σ) S = f₂ / f₁ := hS
  have hZ' : tailProb stdNormal Z = f₂ / f₁ := hZ
  have heq : (S - rbar) / σ = Z := f1ff_tail_inj (by rw [← hT, hS', hZ'])
  rw [div_eq_iff hσ.ne'] at heq
  linarith
