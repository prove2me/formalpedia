-- Prove2me | solution 1 for PerishablePricing.Backlog.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:42:56.364259+00:00
-- url     : https://prove2.me/submissions/fc83de93-b282-46af-887d-070d49377870

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_LNatConvex

set_option autoImplicit false
open PerishablePricing.Backlog

theorem solution {ι : Type*} [Fintype ι] (S : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ)
    (hf : LNatConvexOn S f) :
    LNatConvexOn {w : Option ι → ℝ | (fun i => w (some i) - w none) ∈ S}
      (fun w => f (fun i => w (some i) - w none)) := by
  obtain ⟨hset, hineq⟩ := hf
  have key : ∀ (u v : Option ι → ℝ) (α : ℝ), 0 ≤ α →
      (fun i => u (some i) - u none) ∈ S → (fun i => v (some i) - v none) ∈ S →
      ((fun i => ((u + α • (1 : Option ι → ℝ)) ⊓ v) (some i) - ((u + α • (1 : Option ι → ℝ)) ⊓ v) none) ∈ S ∧
       (fun i => (u ⊔ (v - α • (1 : Option ι → ℝ))) (some i) - (u ⊔ (v - α • (1 : Option ι → ℝ))) none) ∈ S) ∧
      f (fun i => ((u + α • (1 : Option ι → ℝ)) ⊓ v) (some i) - ((u + α • (1 : Option ι → ℝ)) ⊓ v) none)
        + f (fun i => (u ⊔ (v - α • (1 : Option ι → ℝ))) (some i) - (u ⊔ (v - α • (1 : Option ι → ℝ))) none)
        ≤ f (fun i => u (some i) - u none) + f (fun i => v (some i) - v none) := by
    intro u v α hα hu hv
    set yu : ι → ℝ := fun i => u (some i) - u none with hyu
    set yv : ι → ℝ := fun i => v (some i) - v none with hyv
    by_cases hc : u none + α ≤ v none
    · set β : ℝ := v none - u none - α with hβdef
      have hβ : 0 ≤ β := by rw [hβdef]; linarith
      have e1 : (fun i => ((u + α • (1 : Option ι → ℝ)) ⊓ v) (some i) - ((u + α • (1 : Option ι → ℝ)) ⊓ v) none)
          = (yv + β • (1 : ι → ℝ)) ⊓ yu := by
        funext i
        simp only [hyu, hyv, hβdef, Pi.inf_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one,
          min_def]
        split_ifs <;> linarith
      have e2 : (fun i => (u ⊔ (v - α • (1 : Option ι → ℝ))) (some i) - (u ⊔ (v - α • (1 : Option ι → ℝ))) none)
          = yv ⊔ (yu - β • (1 : ι → ℝ)) := by
        funext i
        simp only [hyu, hyv, hβdef, Pi.sup_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one,
          max_def]
        split_ifs <;> linarith
      rw [e1, e2]
      obtain ⟨h1, h2⟩ := hset yv hv yu hu β hβ
      exact ⟨⟨h1, h2⟩, by linarith [hineq yv hv yu hu β hβ]⟩
    · push Not at hc
      set γ : ℝ := u none + α - v none with hγdef
      have hγ : 0 ≤ γ := by rw [hγdef]; linarith
      have e1 : (fun i => ((u + α • (1 : Option ι → ℝ)) ⊓ v) (some i) - ((u + α • (1 : Option ι → ℝ)) ⊓ v) none)
          = (yu + γ • (1 : ι → ℝ)) ⊓ yv := by
        funext i
        simp only [hyu, hyv, hγdef, Pi.inf_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one,
          min_def]
        split_ifs <;> linarith
      have e2 : (fun i => (u ⊔ (v - α • (1 : Option ι → ℝ))) (some i) - (u ⊔ (v - α • (1 : Option ι → ℝ))) none)
          = yu ⊔ (yv - γ • (1 : ι → ℝ)) := by
        funext i
        simp only [hyu, hyv, hγdef, Pi.sup_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one,
          max_def]
        split_ifs <;> linarith
      rw [e1, e2]
      obtain ⟨h1, h2⟩ := hset yu hu yv hv γ hγ
      exact ⟨⟨h1, h2⟩, by linarith [hineq yu hu yv hv γ hγ]⟩
  refine ⟨?_, ?_⟩
  · intro u hu v hv α hα
    exact (key u v α hα hu hv).1
  · intro u hu v hv α hα
    exact (key u v α hα hu hv).2
