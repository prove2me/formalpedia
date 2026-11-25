-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.volume_null_of_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:34:29.549796+00:00
-- url     : https://prove2.me/submissions/ef159eb2-d353-4f97-ad21-0036caf7dd05

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution {I : Type*} [Fintype I] [DecidableEq I] (i0 : I) {S : Set (I → ℂ)}
    (hS : MeasurableSet S) (huniq : ∀ v ∈ S, ∀ v' ∈ S, (∀ j, j ≠ i0 → v j = v' j) → v = v') :
    volume S = 0 := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => ℂ) (fun j => j ≠ i0)
  have hmp : MeasurePreserving e (volume : Measure (I → ℂ))
      ((Measure.pi fun _ : {j // j ≠ i0} => (volume : Measure ℂ)).prod
        (Measure.pi fun _ : {j // ¬ j ≠ i0} => (volume : Measure ℂ))) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : I => (volume : Measure ℂ)) (fun j => j ≠ i0)
  have hS' : MeasurableSet (e.symm ⁻¹' S) := e.symm.measurable hS
  rw [← hmp.symm.measure_preimage_equiv S, Measure.measure_prod_null hS']
  refine Filter.Eventually.of_forall fun x => ?_
  haveI : Nonempty {j // ¬ j ≠ i0} := ⟨⟨i0, not_not.2 rfl⟩⟩
  show (Measure.pi fun _ : {j // ¬ j ≠ i0} => (volume : Measure ℂ)) _ = 0
  refine Set.Subsingleton.measure_zero ?_ _
  intro y hy y' hy'
  have hxy : e.symm (x, y) = e.symm (x, y') := by
    refine huniq _ hy _ hy' fun j hj => ?_
    simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hj]
  have := e.symm.injective hxy
  exact (Prod.ext_iff.1 this).2
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
