-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_rescale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:08.625619+00:00
-- url     : https://prove2.me/submissions/58f849be-da16-4971-8ae4-cabc846fc4bb

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution (G : LogFGL v d) (x : C) {ga : Fin d → PowerSeries C}
    (h0 : ∀ b, PowerSeries.constantCoeff (ga b) = 0) (a : Fin d) :
    G.lgCurve (rescaleCurve x ga) a = PowerSeries.rescale x (G.lgCurve ga a) := by
  have hX : HasSubst (fun _ : Unit => (x • PowerSeries.X : PowerSeries C)) :=
    (PowerSeries.HasSubst.smul_X' x).const
  show subst (fun b => PowerSeries.rescale x (ga b)) (G.lg a) = PowerSeries.rescale x (subst ga (G.lg a))
  simp only [PowerSeries.rescale_eq_subst, PowerSeries.subst_def]
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h0) hX]
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
