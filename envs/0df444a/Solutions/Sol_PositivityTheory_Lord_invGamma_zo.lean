-- Prove2me | solution 1 for PositivityTheory.Lord.invGamma_zo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:48.803236+00:00
-- url     : https://prove2.me/submissions/e85b6220-d009-4522-bb03-fdd86c5f3c1d

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_InvGammaRZo
import Theorems.Thm_PositivityTheory_Lord_PO_mul
import Theorems.Thm_PositivityTheory_Lord_ZO_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Complex
open scoped Real
open PositivityTheory PositivityTheory.Lord
namespace PositivityTheory.Lord
theorem _root_.solution (n : ℕ) : ZO (fun z => (Complex.Gamma z)⁻¹) (-(n : ℂ)) 1 := by
  induction n with
  | zero =>
    refine ⟨fun z => (Complex.Gamma (z + 1))⁻¹, ?_, ?_, ?_⟩
    · have hd : Differentiable ℂ fun z : ℂ => (Complex.Gamma (z + 1))⁻¹ := by
        intro z
        have h := (Complex.differentiable_one_div_Gamma (z + 1)).comp z (differentiableAt_id.add_const (1 : ℂ))
        exact h.congr_of_eventuallyEq (Eventually.of_forall fun w => by simp)
      exact hd.analyticAt _
    · simp
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hz0 : z ≠ 0 := by simpa using hz
      rw [Complex.Gamma_add_one z hz0, mul_inv, ← mul_assoc]
      simp [hz0]
  | succ n ih =>
    obtain ⟨u, hu, hu0, he⟩ := ih
    have hx : (-((n + 1 : ℕ) : ℂ)) + 1 = -(n : ℂ) := by push_cast; ring
    refine ⟨fun z => z * u (z + 1), ?_, ?_, ?_⟩
    · have h1 : AnalyticAt ℂ (fun z : ℂ => z + 1) (-((n + 1 : ℕ) : ℂ)) :=
        analyticAt_id.add analyticAt_const
      exact analyticAt_id.mul (hu.comp_of_eq h1 hx)
    · simp only [hx]
      refine mul_ne_zero ?_ hu0
      rw [neg_ne_zero]
      exact_mod_cast Nat.succ_ne_zero n
    · have ht : Tendsto (fun z : ℂ => z + 1) (𝓝[≠] (-((n + 1 : ℕ) : ℂ))) (𝓝[≠] (-(n : ℂ))) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have hc : Continuous fun z : ℂ => z + 1 := continuous_id.add continuous_const
          have := (hc.tendsto (-((n + 1 : ℕ) : ℂ))).mono_left (nhdsWithin_le_nhds (s := {(-((n + 1 : ℕ) : ℂ))}ᶜ))
          simpa only [hx] using this
        · filter_upwards [self_mem_nhdsWithin] with z hz
          intro h
          apply hz
          have : z = -(n : ℂ) - 1 := by rw [← h]; ring
          rw [Set.mem_singleton_iff, this]; push_cast; ring
      have h0 : ∀ᶠ z in 𝓝[≠] (-((n + 1 : ℕ) : ℂ)), z ≠ 0 := by
        refine eventually_nhdsWithin_of_eventually_nhds (isOpen_compl_singleton.mem_nhds ?_)
        rw [Set.mem_compl_singleton_iff, neg_ne_zero]
        exact_mod_cast Nat.succ_ne_zero n
      filter_upwards [ht.eventually he, h0] with z h1 h2
      have hg : (Complex.Gamma z)⁻¹ = z * (Complex.Gamma (z + 1))⁻¹ := by
        rw [Complex.Gamma_add_one z h2, mul_inv, ← mul_assoc, mul_inv_cancel₀ h2, one_mul]
      rw [hg, h1]
      push_cast
      ring
end PositivityTheory.Lord
