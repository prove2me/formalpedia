-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.lemma_4_20_first_limsup_from_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:00:14.431541+00:00
-- url     : https://prove2.me/submissions/80b232a9-decc-4d30-b489-004be62f0ec9

import Theorems.Thm_ZeroFreeRRG_Hardcore_planted_log_partition_jensen
import Theorems.Thm_ZeroFreeRRG_Hardcore_limsup_vanishing_lower
import Theorems.Thm_ZeroFreeRRG_Hardcore_log_n_over_n
import Theorems.Thm_ZeroFreeRRG_Hardcore_matching_nonempty_even
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter Topology MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (d : ℕ) (t s : ℝ) (ht : m.PosParam t)
    (hlog : ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, Even (n*d) →
      |Real.log (an m d n t)| ≤ C*Real.log (n+1)) :
    limsup (fun n : ℕ => (((1 : ℝ) / n *
        plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U) : ℝ) : EReal))
        (atTop ⊓ 𝓟 {n : ℕ | Even (n*d)}) ≤
      limsup (fun n : ℕ => (((1 : ℝ) / n *
        plantedPinnedE m t s d n (fun M σ U => Real.log (normZ m t M) + pinnedLL m t M σ U) : ℝ) : EReal))
        (atTop ⊓ 𝓟 {n : ℕ | Even (n*d)}) := by
  classical
  let F : Filter ℕ := atTop ⊓ 𝓟 {n : ℕ | Even (n*d)}
  haveI : F.NeBot := by
    apply inf_principal_neBot_iff.mpr
    intro U hU
    obtain ⟨N,hN⟩ := mem_atTop_sets.mp hU
    refine ⟨2*N, hN _ (by omega),?_⟩
    change Even ((2*N)*d)
    exact ⟨N*d,by ring⟩
  obtain ⟨C,N,hN⟩ := hlog
  let A := fun n : ℕ => (1:ℝ)/n * plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U)
  let B := fun n : ℕ => (1:ℝ)/n * plantedPinnedE m t s d n
    (fun M σ U => Real.log (normZ m t M) + pinnedLL m t M σ U)
  let g := fun n : ℕ => -C * Real.log ((n:ℝ)+1) / n
  have hg : Tendsto g F (𝓝 0) := (log_n_over_n C).mono_left inf_le_left
  have hb : ∀ᶠ n in F, A n + g n ≤ B n := by
    rw [eventually_inf_principal,eventually_atTop]
    refine ⟨N,?_⟩
    intro n hn heven
    letI : Nonempty (Matching n d) := matching_nonempty_even n d heven
    have hj := planted_log_partition_jensen m hm t s ht d n
    have hl := hN n hn heven
    have hlow : -C*Real.log ((n:ℝ)+1) ≤ Real.log (an m d n t) := by
      have hh := neg_abs_le (Real.log (an m d n t))
      linarith
    have hscale : 0 ≤ (1:ℝ)/n := by positivity
    have hmul := mul_le_mul_of_nonneg_left (hlow.trans hj) hscale
    have hlin : plantedPinnedE m t s d n
        (fun M σ U => Real.log (normZ m t M) + pinnedLL m t M σ U) =
      plantedPinnedE m t s d n (fun M σ U => Real.log (normZ m t M)) +
      plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U) := by
      simp only [plantedPinnedE,mul_add,Finset.sum_add_distrib]
    change (1:ℝ)/n * plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U) +
      (-C*Real.log ((n:ℝ)+1)/n) ≤ (1:ℝ)/n * plantedPinnedE m t s d n
        (fun M σ U => Real.log (normZ m t M) + pinnedLL m t M σ U)
    rw [hlin]
    calc
      _ = (1:ℝ)/n * plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U) +
          (1:ℝ)/n * (-C*Real.log ((n:ℝ)+1)) := by ring
      _ ≤ (1:ℝ)/n * plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U) +
          (1:ℝ)/n * plantedPinnedE m t s d n (fun M _ _ => Real.log (normZ m t M)) :=
        add_le_add (le_refl _) hmul
      _ = _ := by ring
  exact limsup_vanishing_lower F A B g hg hb
