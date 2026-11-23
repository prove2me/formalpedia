-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.dofD_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:06.930434+00:00
-- url     : https://prove2.me/submissions/f5b2b92c-c876-4da6-a405-a0113ab8b644

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GE
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
theorem _root_.solution (F : Fin d → PS k 2 d) (v : Fin d → k) (f : PS k 1 d) :
    dofD F v f = Dof F v f := by
  have h : ∀ (s : Finset (Fin d)) (D : Fin d → Derivation k (PS k 1 d) (PS k 1 d)),
      (∑ j ∈ s, D j) f = ∑ j ∈ s, D j f := by
    intro s D
    refine Finset.induction_on s (by simp) ?_
    intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]
  rw [dofD, h]
  simp only [Derivation.smul_apply, smul_eq_mul, Dof, dofCoef]
end ReciprocityTheory.ChartRestriction.G.TB.GE
