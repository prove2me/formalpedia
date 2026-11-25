-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.geoNum_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:46.244922+00:00
-- url     : https://prove2.me/submissions/92195717-4c63-4f25-91c5-e8edae8b01d4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupportSubsetMonoBox
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AbsProdSubProdSubLinLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (n : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt n V) (v : Fin n → K → ℤ) :
    geoNum n V v = ∑ r : Fin n → K, (∏ i, v i (r i)) * geoNum n V (fun i => uv (r i)) := by
  have h1 : v = fun i => ∑ k, v i k • uv k := by
    funext i
    ext k'
    simp [Finset.sum_apply, Pi.single_apply]
  have := (geoML n V hS).map_sum (fun i k => v i k • uv k)
  conv_lhs => rw [h1]
  change geoML n V hS _ = _
  rw [this]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
