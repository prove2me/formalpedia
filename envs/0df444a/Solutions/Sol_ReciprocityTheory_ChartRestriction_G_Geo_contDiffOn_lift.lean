-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.contDiffOn_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:04:58.031629+00:00
-- url     : https://prove2.me/submissions/50d394db-277a-4b3d-a6bb-d49440b2b00a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology MeasureTheory
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {P J : Ideal (MRing ι)} {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (R : AnLogRes P J e) (x : R.X) (j : Fin R.A.n) :
    ContDiffOn ℝ ∞ (fun y => R.lift x ((R.A.chart j).symm y))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) := by
  have hopen : IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :=
    (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)
  rw [contDiffOn_pi]
  intro p
  exact ((R.holo x p j).contDiffOn hopen.uniqueDiffOn).restrict_scalars ℝ
end ReciprocityTheory.ChartRestriction.G.Geo
