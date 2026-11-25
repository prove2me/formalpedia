-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.classFinite_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:44:11.31109+00:00
-- url     : https://prove2.me/submissions/be80f52e-656b-46ae-acfe-b5a1725b5c6b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_HermLatFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_ClassFiniteOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (hS : SigPos) (hA : AdelBounds) (hB : LatFin) : ClassFinite := by
  intro F E _ _ _ _ _ _ σ M J L hst hτ hsig hL1 hL2
  obtain ⟨D, T, c0, hD, hT, hc0, hbd⟩ := hA F E σ M J L hst hτ hsig hL1 hL2
  have hσ : ∀ (τ : E →+* ℂ) (a : E), τ ((σ : E →+* E) a) = starRingEnd ℂ (τ a) := by
    intro τ a
    change τ (σ a) = _
    rw [hst a]
    exact hτ τ a
  obtain ⟨S, hSf, hS'⟩ := hB E (σ : E →+* E) M J D T c0 hσ (fun τ => hS M _ (hsig τ)) hD hT hc0
  refine ⟨S, hSf, fun h => ?_⟩
  obtain ⟨b1, b2, b3, b4⟩ := hbd h
  obtain ⟨s, hs, g, hg⟩ := hS' (LamG σ J L h) b1 b2 b3 b4
  exact ⟨s, hs, g, hg⟩
end PI.UnitaryGroupMassFormula.UJClassFin
