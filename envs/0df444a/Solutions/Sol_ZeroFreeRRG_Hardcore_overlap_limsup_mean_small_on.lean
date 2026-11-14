-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.overlap_limsup_mean_small_on
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:42:34.72305+00:00
-- url     : https://prove2.me/submissions/2db3a2bf-defa-44fd-82e1-4c46082e5dff

import Theorems.Thm_ZeroFreeRRG_Hardcore_unique_maximum_small_perturbation_on
import Mathlib
set_option autoImplicit false
open Set Filter ZeroFreeRRG.Hardcore

theorem solution {α : Type} [TopologicalSpace α] (K : Set α) (hK : IsCompact K)
    (f g : α → ℝ) (hf : ContinuousOn f K) (hg : ContinuousOn g K) (x₀ : α) (hx₀ : x₀ ∈ K)
    (hfnonpos : ∀ x ∈ K, f x ≤ 0) (hfzero : f x₀ = 0)
    (hunique : ∀ x ∈ K, f x = 0 → x = x₀) (hgzero : g x₀ = 0)
    (E : ℝ → ℕ → ℝ) (admissible : Set ℕ)
    (hlimsup : ∀ s : ℝ, 0 < s → s < 1 → ∃ x ∈ K,
      limsup (fun n => (E s n : EReal)) (atTop ⊓ 𝓟 admissible) ≤ (f x + s*g x : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      ∃ N : ℕ, ∀ n ≥ N, n ∈ admissible → E s n ≤ ε*s := by
  intro ε hε
  obtain ⟨s₀,hs₀,huni⟩ := unique_maximum_small_perturbation_on K hK f g hf hg x₀ hx₀
    hfnonpos hfzero hunique hgzero (ε/2) (by linarith)
  let s := min s₀ 1 / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hs1 : s < 1 := by dsimp [s]; have h := min_le_right s₀ (1:ℝ); linarith
  have hs0 : s < s₀ := by dsimp [s]; have h := min_le_left s₀ (1:ℝ); linarith
  obtain ⟨x,hx,hlim⟩ := hlimsup s hs hs1
  have hxuni := huni s hs hs0 x hx
  have hxlt : f x + s*g x < ε*s := by nlinarith
  have hlt : limsup (fun n => (E s n : EReal)) (atTop ⊓ 𝓟 admissible) < (ε*s : ℝ) :=
    hlim.trans_lt (EReal.coe_lt_coe_iff.mpr hxlt)
  have hevent := Filter.eventually_lt_of_limsup_lt hlt
  rw [Filter.eventually_inf_principal,Filter.eventually_atTop] at hevent
  obtain ⟨N,hN⟩ := hevent
  refine ⟨s,hs,hs1,N,?_⟩
  intro n hn hadm
  exact le_of_lt (EReal.coe_lt_coe_iff.mp (hN n hn hadm))
