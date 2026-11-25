-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_form_mem_of_smulIdeal_c736a6e4c699
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:07:37.046412+00:00
-- url     : https://prove2.me/submissions/07aeab5a-88ca-4675-9aea-60b2910d030e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadicalPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearFormEqZeroOfIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.UnitaryReduction
open GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace NumberField.InfinitePlace
open scoped InnerProductSpace nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E]
variable {V V' : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
  [AddCommGroup V'] [Module E V'] [Module (𝓞 E) V'] [IsScalarTower (𝓞 E) E V']
namespace GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
theorem _root_.solution (aa : FractionalIdeal (𝓞 E)⁰ E) (B : Submodule (𝓞 E) V)
    (ρ : V →ₗ[E] E) (hρ : ∀ b ∈ B, ρ b ∈ Set.range (algebraMap (𝓞 E) E)) {x : V}
    (hx : x ∈ smulIdeal aa B) : ρ x ∈ (aa : Submodule (𝓞 E) E) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, b, hb, rfl⟩ := hy
    obtain ⟨o, ho⟩ := hρ b hb
    rw [LinearMap.map_smul, smul_eq_mul, ← ho, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ o hc
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ hy
end GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
