-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdAbs.B_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:13:33.018717+00:00
-- url     : https://prove2.me/submissions/4717b7de-aa16-42f0-8fdf-a61b29070000

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SmulMemHermR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExAbs

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
    (hBs : ∀ (c : Fv F v) x y, B (c • x) y = c * B x y) {ι : Type} (s : Finset ι) (f : ι → V)
    (y : V) : B (∑ i ∈ s, f i) y = ∑ i ∈ s, B (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [B_zero_left v B hBs]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hBa, ih]
end PI.OmFibreUniq.W.SdAbs
