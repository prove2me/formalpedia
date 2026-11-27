-- Prove2me | solution 1 for UpperTheory.homology_finite_short_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:35:22.04248+00:00
-- url     : https://prove2.me/submissions/a59a659e-b815-4aef-8e88-def3be39b4cd

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomologyFiniteShortExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory
namespace UpperTheory
universe v u w
private lemma finite_middle {R : Type u} [Ring R] {M₁ M₂ M₃ : Type v}
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (h : Function.Exact f g)
    [IsNoetherianRing R] [Module.Finite R M₁] [Module.Finite R M₃] :
    Module.Finite R M₂ := by
  have hk : Module.Finite R (LinearMap.ker g) := by
    rw [LinearMap.exact_iff.1 h]
    exact Module.Finite.range f
  have : IsNoetherian R M₃ := isNoetherian_of_isNoetherianRing_of_finite R M₃
  have hq : Module.Finite R (M₂ ⧸ LinearMap.ker g) :=
    Module.Finite.equiv g.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)
end UpperTheory
end

set_option autoImplicit false
open CategoryTheory
open UpperTheory
universe v u w
namespace UpperTheory
theorem _root_.solution {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) c)} (hS : S.ShortExact) (i : ι) :
    (Finite (S.X₁.homology i) → Finite (S.X₃.homology i) → Finite (S.X₂.homology i)) ∧
    (IsNoetherianRing R → Module.Finite R (S.X₁.homology i) →
      Module.Finite R (S.X₃.homology i) → Module.Finite R (S.X₂.homology i)) := by
  have hE := hS.homology_exact₂ i
  refine ⟨fun h₁ h₃ ↦ ?_, fun _ h₁ h₃ ↦ ?_⟩
  · exact AddCommGrpCat.isFinite.prop_X₂_of_exact
      (hE.map (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})) h₁ h₃
  · exact finite_middle _ _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hE)
end UpperTheory
