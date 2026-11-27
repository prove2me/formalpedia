-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.leib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:23:45.251034+00:00
-- url     : https://prove2.me/submissions/d27d432b-969f-4d2e-8802-c885cdd0bc7b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_IteratedDerivEqOfEventuallyEq
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_iteratedDeriv_eq_of_eventuallyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology Set
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt
namespace PositivityTheory.Rg.Sw.HSt
theorem _root_.solution {U : Set ℂ} (hU : IsOpen U) : ∀ (j : ℕ) (h₁ h₂ : ℂ → ℂ), DifferentiableOn ℂ h₁ U → DifferentiableOn ℂ h₂ U →
    ∀ s ∈ U, iteratedDeriv j (fun z => h₁ z * h₂ z) s =
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * iteratedDeriv i h₁ s * iteratedDeriv (j - i) h₂ s := by
  intro j
  induction j with
  | zero => intro h₁ h₂ _ _ s _; simp
  | succ j ih =>
    intro h₁ h₂ hd₁ hd₂ s hs
    have hd₁' : DifferentiableOn ℂ (deriv h₁) U := hd₁.deriv hU
    have hd₂' : DifferentiableOn ℂ (deriv h₂) U := hd₂.deriv hU
    have hev : deriv (fun z => h₁ z * h₂ z) =ᶠ[𝓝 s] fun z => deriv h₁ z * h₂ z + h₁ z * deriv h₂ z := by
      filter_upwards [hU.mem_nhds hs] with z hz
      exact deriv_mul ((hd₁.differentiableAt (hU.mem_nhds hz))) ((hd₂.differentiableAt (hU.mem_nhds hz)))
    rw [iteratedDeriv_succ', iteratedDeriv_eq_of_eventuallyEq hev]
    have hc₁ : ContDiffAt ℂ j (fun z => deriv h₁ z * h₂ z) s :=
      ((hd₁'.mul hd₂).contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top
    have hc₂ : ContDiffAt ℂ j (fun z => h₁ z * deriv h₂ z) s :=
      ((hd₁.mul hd₂').contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top
    have hsplit : (fun z => deriv h₁ z * h₂ z + h₁ z * deriv h₂ z) =
        (fun z => deriv h₁ z * h₂ z) + (fun z => h₁ z * deriv h₂ z) := rfl
    rw [hsplit, iteratedDeriv_add hc₁ hc₂, ih _ _ hd₁' hd₂ s hs, ih _ _ hd₁ hd₂' s hs]
    have key := Finset.sum_choose_succ_mul (R := ℂ) (fun a b => iteratedDeriv a h₁ s * iteratedDeriv b h₂ s) j
    simp only [mul_assoc] at key ⊢
    rw [key, add_comm]
    congr 1
    all_goals
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      (try rw [← iteratedDeriv_succ']); (try rw [show j + 1 - i = j - i + 1 by omega])
end PositivityTheory.Rg.Sw.HSt
