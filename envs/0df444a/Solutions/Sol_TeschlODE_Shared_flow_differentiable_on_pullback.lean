-- Prove2me | solution 1 for TeschlODE.Shared.flow_differentiable_on_pullback
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:40:13.683511+00:00
-- url     : https://prove2.me/submissions/b098601a-7f5b-4f03-afef-e3cd8785fd50

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow

section Helpers385f
open TeschlODE.Shared

/-- A flow map that is discontinuous at the origin. -/
noncomputable def cexG385f (y : Fin 1 → ℝ) : Fin 1 → ℝ := if y = 0 then 0 else 1

theorem cexG385f_not_cont : ¬ ContinuousAt cexG385f 0 := by
  intro hc
  have hseq : Filter.Tendsto (fun m : ℕ => (fun _ : Fin 1 => (1 : ℝ) / ((m : ℝ) + 1)))
      Filter.atTop (nhds (0 : Fin 1 → ℝ)) := by
    rw [tendsto_pi_nhds]
    intro _
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 := hc.tendsto.comp hseq
  have hval : (cexG385f ∘ fun m : ℕ => (fun _ : Fin 1 => (1 : ℝ) / ((m : ℝ) + 1)))
      = fun _ => (1 : Fin 1 → ℝ) := by
    funext m
    have hne : (fun _ : Fin 1 => (1 : ℝ) / ((m : ℝ) + 1)) ≠ 0 := by
      intro h
      have := congrFun h 0
      simp only [Pi.zero_apply] at this
      have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      linarith
    simp only [Function.comp_apply, cexG385f]
    rw [if_neg hne]
  rw [hval] at h1
  have h2 := tendsto_nhds_unique h1 tendsto_const_nhds
  have h3 : cexG385f 0 = 0 := by simp [cexG385f]
  rw [h3] at h2
  have := congrFun h2 0
  simp at this

theorem cex385f_flow : IsMaximalFlow (n := 1) (fun _ => 0) (∅ : Set (Fin 1 → ℝ))
    (fun _ => Set.univ) (fun _ y => cexG385f y) := by
  intro x hx
  exact absurd hx (Set.notMem_empty x)

end Helpers385f

open TeschlODE.Shared in
theorem solution : ¬ (∀ {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (hM : IsOpen M) (k : ℕ) (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ k f M) (I : (Fin n → ℝ) → Set ℝ)
    (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (hΦ : IsMaximalFlow f M I Φ)
    (x : Fin n → ℝ) (s t : ℝ) (hs : s ∈ I x) (ht : t ∈ I x),
    DifferentiableAt ℝ (Φ t) (Φ s x)) := by
  intro h
  have hd := h (n := 1) (fun _ => 0) ∅ isOpen_empty 1 le_rfl contDiff_const.contDiffOn
    (fun _ => Set.univ) (fun _ y => cexG385f y) cex385f_flow 0 0 0 (Set.mem_univ _)
    (Set.mem_univ _)
  have h0 : cexG385f 0 = 0 := by simp [cexG385f]
  simp only [h0] at hd
  exact cexG385f_not_cont hd.continuousAt
