-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.d4l4_diff_flow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:47.209512+00:00
-- url     : https://prove2.me/submissions/8d740ee0-a3b0-48d2-b693-93f04a0fb134

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Complex Filter Topology
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution {r : ℕ} (X : Data E r) (e : X.Ψ → Fin r → ℂ) (x : Frame X.Ψ r)
    (s : X.Ψ → ℂ) (τ0 : X.Ψ) :
    Differentiable ℂ (fun z : ℂ => X.flowV e (Function.update s τ0 z) x) := by
  rw [differentiable_pi]
  intro τ
  rw [differentiable_pi]
  intro a
  rw [differentiable_pi]
  intro b
  have hu : Differentiable ℂ (fun z : ℂ => Function.update s τ0 z τ) := by
    by_cases h : τ = τ0
    · subst h
      simpa using differentiable_id
    · simpa [Function.update_of_ne h] using differentiable_const (s τ)
  intro z
  simp only [Data.flowV, Matrix.mul_apply, Data.flowMatV, Matrix.of_apply, mat]
  refine DifferentiableAt.fun_sum fun k _ => ?_
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.const_sub
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.const_mul
  exact hu z
end ReciprocityTheory.ChartRestriction.G.FD
