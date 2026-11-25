-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.emb_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:10:54.345887+00:00
-- url     : https://prove2.me/submissions/c61da07e-9605-4a88-862c-a2ef9e62494f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (g : (E →+* ℂ) → ℂ) (h : ∀ β : 𝓞 E, ∑ σ, σ (β : E) * g σ = 0) : g = 0 := by
  have hb : ∀ i, ∑ σ : E →+* ℂ, σ (integralBasis E i) * g σ = 0 := fun i => by
    rw [integralBasis_apply]
    exact h _
  have hE : ∀ x : E, ∑ σ : E →+* ℂ, σ x * g σ = 0 := by
    intro x
    rw [← (integralBasis E).sum_repr x]
    simp only [map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have e : ∀ σ : E →+* ℂ, σ ((integralBasis E).repr x i • integralBasis E i) * g σ =
        ((integralBasis E).repr x i : ℂ) * (σ (integralBasis E i) * g σ) := fun σ => by
      rw [map_rat_smul, Rat.smul_def, mul_assoc]
    rw [Finset.sum_congr rfl fun σ _ => e σ, ← Finset.mul_sum, hb i, mul_zero]
  have hli : LinearIndependent ℂ (fun σ : E →+* ℂ => ((σ : E →* ℂ) : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp (fun σ : E →+* ℂ => (σ : E →* ℂ))
      (fun a b hab => RingHom.ext fun x => DFunLike.congr_fun hab x)
  rw [Fintype.linearIndependent_iff] at hli
  funext σ
  refine hli g ?_ σ
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [← hE x]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [mul_comm]
end ReciprocityTheory.ChartRestriction.G.I2
