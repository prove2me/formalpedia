-- Prove2me | solution 1 for PI.VolStabW.RPA.eS_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:32.233583+00:00
-- url     : https://prove2.me/submissions/1e8efd4f-55e1-49de-a326-9670b5070c20

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
variable (m L)
open Classical
namespace PI.VolStabW.RPA
theorem _root_.solution (S : Finset ι) (p : (∀ i : {i // i ∈ S}, W i) × (∀ i : {i // i ∉ S}, W i))
    (i : ι) : (eS S).symm p i = if h : i ∈ S then p.1 ⟨i, h⟩ else p.2 ⟨i, h⟩ := by
  simp only [eS, MeasurableEquiv.piEquivPiSubtypeProd]
  rfl
end PI.VolStabW.RPA
