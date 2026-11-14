-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_one_edge_phase_change
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:28:58.581285+00:00
-- url     : https://prove2.me/submissions/03cfe49e-61b3-4cb7-853c-279a5c505338

import Theorems.Thm_ZeroFreeRRG_Hardcore_scaled_phase_perturbation
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_discrete_phase_budget
import Theorems.Thm_ZeroFreeRRG_Hardcore_weighted_sector_perturbation
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_segment_metric
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution {ι : Type} (S : Finset ι) (z a b : ι → ℂ) (d : ℕ) (hd : 3 ≤ d)
    (β : ℂ) (hβ : ‖β-1‖ < 0.35/(d:ℝ))
    (ha : ∀ i ∈ S, ∃ t : ℝ, t ∈ Icc 0 1 ∧ a i = 1+(t:ℂ)*(β-1))
    (hb : ∀ i ∈ S, ∃ t : ℝ, t ∈ Icc 0 1 ∧ b i = 1+(t:ℂ)*(β-1))
    (hsum : (7/8:ℝ)*(∑ i ∈ S, ‖z i‖) ≤ ‖∑ i ∈ S, z i‖)
    (hne : (∑ i ∈ S, z i) ≠ 0) :
    let Z := ∑ i ∈ S, z i
    let Z' := ∑ i ∈ S, (b i/a i)*z i
    Z' ≠ 0 ∧ ‖Z/(‖Z‖:ℂ)-Z'/(‖Z'‖:ℂ)‖ ≤
      (25/23)*(‖β-1‖/((7/8:ℝ)*(1-‖β-1‖))) := by
  classical
  dsimp only
  let δ := ‖β-1‖
  let r := δ/((7/8:ℝ)*(1-δ))
  have hδ : 0 ≤ δ := norm_nonneg _
  have hbudget := potts_discrete_phase_budget d hd δ hδ hβ
  have hδ1 : δ < 1 := by
    have hd' : (3:ℝ) ≤ d := by exact_mod_cast hd
    have hdp : (0:ℝ) < d := by linarith
    have hh : (0.35:ℝ)/(d:ℝ) < 1 := by apply (div_lt_one₀ hdp).2; linarith
    exact hβ.trans hh
  have hnorm (i : ι) (hi : i ∈ S) : 1-δ ≤ ‖a i‖ := by
    obtain ⟨s,hs,has⟩ := ha i hi
    obtain ⟨t,ht,hbt⟩ := hb i hi
    rw [has]
    exact (potts_segment_metric β s t hs ht).2
  have hdiff (i : ι) (hi : i ∈ S) : ‖b i-a i‖ ≤ δ := by
    obtain ⟨s,hs,has⟩ := ha i hi
    obtain ⟨t,ht,hbt⟩ := hb i hi
    rw [has,hbt]
    exact (potts_segment_metric β s t hs ht).1
  have hbound := weighted_sector_perturbation S z a b δ (7/8) hδ hδ1 (by norm_num) hnorm hdiff hsum
  apply scaled_phase_perturbation (∑ i ∈ S, z i) (∑ i ∈ S, (b i/a i)*z i) r hne hbudget.1 hbudget.2.1
  rw [norm_sub_rev]
  exact hbound
