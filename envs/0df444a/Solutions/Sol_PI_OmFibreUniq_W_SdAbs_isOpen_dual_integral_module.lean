-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdAbs.isOpen_dual_integral_module
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:21:50.707218+00:00
-- url     : https://prove2.me/submissions/ec6755af-1fac-41da-9cfa-247a16f60b12

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SmulMemHermR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExAbs
import Theorems.Thm_PI_OmFibreUniq_W_SdAbs_mem_dual_integral_module

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
    (hBc : ∀ x, Continuous (B x)) {ι : Type} [Fintype ι] (β' : ι → V) :
    IsOpen (M0 v B hBa hBs β' : Set V) := by
  have e : (M0 v B hBa hBs β' : Set V) =
      ⋂ j, (fun x => B x (β' j)) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext x; simp [mem_dual_integral_module]
  rw [e]
  exact isOpen_iInter_of_finite fun j =>
    (Valued.isOpen_valuationSubring _).preimage ((hBc (β' j)).congr fun x => hBsym _ _)
end PI.OmFibreUniq.W.SdAbs
