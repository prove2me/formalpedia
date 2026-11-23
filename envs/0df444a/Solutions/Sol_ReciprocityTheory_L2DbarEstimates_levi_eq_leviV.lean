-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.levi_eq_leviV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:39.600066+00:00
-- url     : https://prove2.me/submissions/e181f837-993d-438d-a679-75987c751fb0

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology Set
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (ph : M → ℝ) (x : M)
    (hx : x ∈ e.source) (ξ : Fin n → ℂ) :
    Levi n z ph x ξ = leviV n (fun y => (ph (e.symm y) : ℂ)) (z x) ξ := by
  unfold Levi leviV
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [d_eq_wd n z e he j _ x hx]
  have hT : e.target ∈ 𝓝 (z x) := by
    rw [he hx]; exact e.open_target.mem_nhds (e.map_source hx)
  have key : wd n j (db n z k (fun y => (ph y : ℂ)) ∘ e.symm) (z x) =
      wd n j (wdb n k (fun y => (ph (e.symm y) : ℂ))) (z x) := by
    apply wd_congr
    filter_upwards [hT] with y hy
    exact db_comp_symm n z e he k _ y hy
  rw [key]
end ReciprocityTheory.L2DbarEstimates
