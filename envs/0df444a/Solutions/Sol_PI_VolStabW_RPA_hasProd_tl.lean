-- Prove2me | solution 1 for PI.VolStabW.RPA.hasProd_tl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:57:11.560454+00:00
-- url     : https://prove2.me/submissions/20c8e030-7f76-429e-96c8-bbb12023fe9a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ESSymmApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.RPA
open MeasureTheory Filter Finset
open scoped NNReal ENNReal
variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable (m : ∀ i, Measure (W i)) (L : ∀ i, Set (W i))
variable {m L}
namespace PI.VolStabW.RPA
theorem _root_.solution (hT : TailH m L) (S : Finset ι) :
    HasProd (fun i : {i // i ∉ S} => am m L i.1) (tl m L S) := by
  obtain ⟨c, hc, h⟩ := hT S
  have h2 : HasProd (fun i : {i // i ∉ S} => am m L i.1) c.toNNReal := by
    have h3 := (ENNReal.tendsto_toNNReal hc).comp h
    refine h3.congr ?_
    intro s
    simp [Function.comp_def, am, ENNReal.toNNReal_prod]
  unfold tl
  rw [h2.tprod_eq]
  exact h2
end PI.VolStabW.RPA
