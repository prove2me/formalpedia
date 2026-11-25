-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdAbs.isCompact_dual_integral_module
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:33.878037+00:00
-- url     : https://prove2.me/submissions/759953ca-5d5e-4fa8-bcdf-e6a50f79b4c0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SmulMemHermR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExAbs
import Theorems.Thm_PI_OmFibreUniq_W_SdAbs_isOpen_dual_integral_module

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.SdAbs
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter NumberField IsDedekindDomain
open PI.VolStabSW.SdUniqW PI.OmFibreUniq.W.SdCore PI.OmFibreUniq.W.SdChar
open scoped ENNReal
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  {V : Type} [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul (Fv F v) V] [T2Space V] [LocallyCompactSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (B : V → V → Fv F v)
namespace PI.OmFibreUniq.W.SdAbs
theorem _root_.solution (hBa : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hBs : ∀ (c : Fv F v) x y, B (c • x) y = c * B x y) (hBsym : ∀ x y, B x y = B y x)
    (hBc : ∀ x, Continuous (B x)) {ι : Type} [Fintype ι] (β β' : ι → V)
    (h1 : ∀ x, x = ∑ j, B x (β' j) • β j) :
    IsCompact (M0 v B hBa hBs β' : Set V) := by
  have hO : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) :=
    PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  have hK : IsCompact ((fun c : ι → Fv F v => ∑ j, c j • β j) ''
      Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
    (isCompact_univ_pi fun _ => hO).image
      (continuous_finset_sum _ fun j _ => (continuous_apply j).smul continuous_const)
  have hcl : IsClosed (M0 v B hBa hBs β' : Set V) :=
    AddSubgroup.isClosed_of_isOpen _ (isOpen_dual_integral_module v B hBa hBs hBsym hBc β')
  refine hK.of_isClosed_subset hcl fun x hx => ⟨fun j => B x (β' j), fun j _ => hx j, ?_⟩
  exact (h1 x).symm
end PI.OmFibreUniq.W.SdAbs
