-- Prove2me | solution 1 for PI.VolStabW.RestrProdA.latCofin_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:16:45.192992+00:00
-- url     : https://prove2.me/submissions/6582fbc4-be00-4c06-a64a-a076497845d1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdA
import Theorems.Thm_PI_VolStabW_RestrProdA_repr_change

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.RestrProdA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
namespace PI.VolStabW.RestrProdA
theorem _root_.solution : LatCofin := by
  intro F E _ _ _ _ a M d d' b b'
  have key : ∀ x : F, ∀ᶠ v in Filter.cofinite,
      algebraMap F (Fv F v) x ∈ (v.adicCompletionIntegers F : Set (Fv F v)) := fun x =>
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) x).2
  have h1 : ∀ᶠ v in Filter.cofinite, ∀ k k', algebraMap F (Fv F v) (b'.repr (b k) k') ∈
      (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun k' => key _
  have h2 : ∀ᶠ v in Filter.cofinite, ∀ k' k, algebraMap F (Fv F v) (b.repr (b' k') k) ∈
      (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Filter.eventually_all.2 fun k' => Filter.eventually_all.2 fun k => key _
  filter_upwards [h1, h2] with v hv1 hv2
  ext Y
  simp only [latV, Set.mem_setOf_eq]
  constructor
  · intro hY x i k'
    rw [repr_change (Fv F v) b b']
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hY x i k) (hv1 k k')
  · intro hY x i k
    rw [repr_change (Fv F v) b' b]
    exact Subring.sum_mem _ fun k' _ => Subring.mul_mem _ (hY x i k') (hv2 k' k)
end PI.VolStabW.RestrProdA
