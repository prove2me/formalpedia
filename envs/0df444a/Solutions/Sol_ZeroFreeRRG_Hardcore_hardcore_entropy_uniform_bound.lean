-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_entropy_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:50:03.574682+00:00
-- url     : https://prove2.me/submissions/8cd87bb1-aded-4e76-b694-3824912d101b

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators
open Set

theorem solution (d : ℕ) (T : ℝ) (hT : T < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (t : ℝ) (h : Fin d → ℝ),
      0 ≤ t → t ≤ T → (∀ i, -1 ≤ h i ∧ h i ≤ 1) →
      let V := ((∏ i, (1+t*h i)) + t*(∏ i, (1-h i)))/(1+t)
      let D := ((1+t)*(∑ i, (∏ j ∈ Finset.univ.erase i, (1+t*h j))*h i) +
        (∏ i, (1-h i)) - ∏ i, (1+t*h i)) / (1+t)^2
      ‖V * Real.log V‖ ≤ B ∧ ‖D * (Real.log V + 1)‖ ≤ B := by
  let S : Set (ℝ × (Fin d → ℝ)) := Icc 0 T ×ˢ Set.pi univ (fun _ => Icc (-1:ℝ) 1)
  have hS : IsCompact S := (isCompact_Icc).prod (isCompact_univ_pi fun _ : Fin d => isCompact_Icc)
  let V := fun p : ℝ × (Fin d → ℝ) =>
    ((∏ i, (1+p.1*p.2 i)) + p.1*(∏ i, (1-p.2 i)))/(1+p.1)
  let D := fun p : ℝ × (Fin d → ℝ) =>
    ((1+p.1)*(∑ i, (∏ j ∈ Finset.univ.erase i, (1+p.1*p.2 j))*p.2 i) +
      (∏ i, (1-p.2 i)) - ∏ i, (1+p.1*p.2 i)) / (1+p.1)^2
  have hden : ∀ p ∈ S, 1+p.1 ≠ 0 := by
    intro p hp
    have hp0 : 0 ≤ p.1 := hp.1.1
    linarith
  have hVpos : ∀ p ∈ S, 0 < V p := by
    intro p hp
    have ht0 : 0 ≤ p.1 := hp.1.1
    have ht1 : p.1 < 1 := lt_of_le_of_lt hp.1.2 hT
    have hh (i : Fin d) : -1 ≤ p.2 i ∧ p.2 i ≤ 1 := hp.2 i (mem_univ i)
    have hpterm (i : Fin d) : 0 < 1+p.1*p.2 i := by
      nlinarith [mul_nonneg ht0 (show 1+p.2 i ≥ 0 by linarith [(hh i).1])]
    have hprod : 0 < ∏ i, (1+p.1*p.2 i) := Finset.prod_pos (fun i _ => hpterm i)
    have hQ : 0 ≤ ∏ i, (1-p.2 i) := Finset.prod_nonneg (fun i _ => by linarith [(hh i).2])
    dsimp [V]
    apply div_pos _ (by linarith)
    exact add_pos_of_pos_of_nonneg hprod (mul_nonneg ht0 hQ)
  have hVc : ContinuousOn V S := by
    dsimp [V]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact hden
  have hDc : ContinuousOn D S := by
    dsimp [D]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro p hp
    exact pow_ne_zero _ (hden p hp)
  have hlogc : ContinuousOn (fun p => Real.log (V p)) S :=
    hVc.log (fun p hp => ne_of_gt (hVpos p hp))
  have hFc : ContinuousOn (fun p => V p * Real.log (V p)) S := hVc.mul hlogc
  have hGc : ContinuousOn (fun p => D p * (Real.log (V p)+1)) S :=
    hDc.mul (hlogc.add continuousOn_const)
  obtain ⟨B₁,hB₁⟩ := hS.exists_bound_of_continuousOn hFc
  obtain ⟨B₂,hB₂⟩ := hS.exists_bound_of_continuousOn hGc
  refine ⟨max 0 (max B₁ B₂), le_max_left _ _, ?_⟩
  intro t h ht0 htT hh
  have hp : (t,h) ∈ S := by
    constructor
    · exact ⟨ht0,htT⟩
    · intro i hi
      exact hh i
  constructor
  · exact (hB₁ (t,h) hp).trans ((le_max_left B₁ B₂).trans (le_max_right 0 _))
  · exact (hB₂ (t,h) hp).trans ((le_max_right B₁ B₂).trans (le_max_right 0 _))
