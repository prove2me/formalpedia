-- Prove2me | solution 1 for SinglePointPricing.Det.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:39:55.234754+00:00
-- url     : https://prove2.me/submissions/87b78bac-48fb-45da-8d5a-b663ade5b74a

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting

open SinglePointPricing.Det

theorem solution (α β s : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : 0 < β) (hs : 0 ≤ s) :
    ∀ v : ℝ, s ≤ v →
      (1 - α) * v - GammaA α (β * (v - s)) / (-deriv (fun x => GammaA α (β * (x - s))) v)
        = (1 - α) * s - 1 / β := by
  intro v hv
  by_cases h1 : α = 1
  · subst h1
    have hd : HasDerivAt (fun x => GammaA 1 (β * (x - s))) (-β * Real.exp (-(β * (v - s)))) v := by
      have : (fun x => GammaA 1 (β * (x - s))) = fun x => Real.exp ((-β) * (x - s)) := by
        funext x; simp only [GammaA, if_true]; ring_nf
      rw [this]
      have h2 : HasDerivAt (fun x => (-β) * (x - s)) (-β) v := by
        have := ((hasDerivAt_id v).sub_const s).const_mul (-β)
        simpa using this
      have := h2.exp
      convert this using 1; ring_nf
    rw [hd.deriv]
    simp only [GammaA, if_true]
    have hpos := Real.exp_pos (-(β * (v - s)))
    field_simp
    ring
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h⟩; exact sub_pos.mpr (lt_of_le_of_ne h h1)
    set a := 1 - α with ha_def
    have hbase : ∀ x, s ≤ x → 0 < 1 + a * (β * (x - s)) := by
      intro x hx; have : 0 ≤ a * (β * (x - s)) := by
        apply mul_nonneg ha.le; exact mul_nonneg hβ.le (by linarith)
      linarith
    have hfun : (fun x => GammaA α (β * (x - s))) = fun x => (1 + a * (β * (x - s))) ^ (-(1 / a)) := by
      funext x; simp [GammaA, h1, ha_def]
    have hb : HasDerivAt (fun x => 1 + a * (β * (x - s))) (a * β) v := by
      have := (((hasDerivAt_id v).sub_const s).const_mul β).const_mul a
      have := this.const_add 1
      simpa using this
    have hd := hb.rpow_const (p := -(1 / a)) (Or.inl (hbase v hv).ne')
    rw [hfun, hd.deriv]
    simp only [GammaA, h1, if_false]
    rw [← ha_def]
    have hB := hbase v hv
    set B := 1 + a * (β * (v - s)) with hB_def
    have hrp : B ^ (-(1 / a) - 1) = B ^ (-(1 / a)) / B := by
      rw [Real.rpow_sub hB, Real.rpow_one]
    rw [hrp]
    have hpos : 0 < B ^ (-(1 / a)) := Real.rpow_pos_of_pos hB _
    field_simp
    rw [hB_def]
    ring
