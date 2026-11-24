-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.segMono_homog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:54.225131+00:00
-- url     : https://prove2.me/submissions/8ff75966-bdc2-4adf-a5a3-867aa2e36373

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib

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
open MvPolynomial
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  [∀ k, DecidableEq (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (i : (k : K) → ι k) :
    IsWeightedHomogeneous (blkW ι) (segMono ι i) (fun _ => 1) := by
  have := IsWeightedHomogeneous.prod (w := blkW ι) Finset.univ (fun k => (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℂ))
    (fun k => blkW ι ⟨k, i k⟩) (fun k _ => isWeightedHomogeneous_X ℂ _ _)
  unfold segMono
  convert this using 1
  funext k'
  simp [blkW, Finset.sum_apply, Pi.single_apply]
end ReciprocityTheory.ChartRestriction.G.Geo
