-- Prove2me | solution 1 for SuttonBartoRL.OffPolicy.return_error_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:48:30.190982+00:00
-- url     : https://prove2.me/submissions/b2aee689-8b09-44a3-937f-e6287f50ad42

import Mathlib
import Definitions.Def_SuttonBartoRL_OffPolicy_ReturnError

open MeasureTheory

lemma p7163839c_state (ν : Measure ℝ) [IsProbabilityMeasure ν] (h2 : MemLp id 2 ν)
    (v a : ℝ) (hm : ∫ g, g ∂ν = v) :
    ∫ g, (g - a) ^ 2 ∂ν = (v - a) ^ 2 + ∫ g, (g - v) ^ 2 ∂ν := by
  have hi : Integrable (fun g : ℝ => g) ν := h2.integrable one_le_two
  have hsq : Integrable (fun g : ℝ => (g - v) ^ 2) ν :=
    (h2.sub (memLp_const v)).integrable_sq
  have e : (fun g : ℝ => (g - a) ^ 2) =
      fun g => (g - v) ^ 2 + (2 * (v - a) * g + ((v - a) ^ 2 - 2 * (v - a) * v)) := by
    funext g; ring
  rw [e]
  have hl : Integrable (fun g : ℝ => 2 * (v - a) * g) ν := hi.const_mul _
  have hc : Integrable (fun _ : ℝ => (v - a) ^ 2 - 2 * (v - a) * v) ν := integrable_const _
  have hlc : Integrable (fun g : ℝ => 2 * (v - a) * g + ((v - a) ^ 2 - 2 * (v - a) * v)) ν :=
    hl.add hc
  have h1 := integral_add hsq hlc
  have h2' := integral_add hl hc
  have h3 : ∫ g, 2 * (v - a) * g ∂ν = 2 * (v - a) * v := by
    rw [integral_const_mul, hm]
  have h4 : ∫ _ : ℝ, ((v - a) ^ 2 - 2 * (v - a) * v) ∂ν = (v - a) ^ 2 - 2 * (v - a) * v := by
    simp
  rw [h1, h2', h3, h4]
  ring

open SuttonBartoRL.OffPolicy MeasureTheory in
theorem solution {S W : Type} [Fintype S]
    (μ : S → ℝ) (hμ0 : ∀ s, 0 ≤ μ s) (hμ1 : ∑ s, μ s = 1)
    (ν : S → Measure ℝ) (hprob : ∀ s, IsProbabilityMeasure (ν s))
    (hL2 : ∀ s, MemLp id 2 (ν s))
    (vπ : S → ℝ) (hmean : ∀ s, ∫ g, g ∂(ν s) = vπ s)
    (vhat : W → S → ℝ) (w : W) :
    RE μ ν (vhat w) = VE μ vπ (vhat w) + RE μ ν vπ := by
  unfold RE VE
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have := hprob s
  rw [p7163839c_state (ν s) (hL2 s) (vπ s) (vhat w s) (hmean s)]
  ring
