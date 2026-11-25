-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.geoNum_expand_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:39.292072+00:00
-- url     : https://prove2.me/submissions/cc2d4c6d-4fb5-4d3a-9b63-4bcbe1579a54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupportSubsetMonoBox
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AbsProdSubProdSubLinLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_geoNum_expand

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
    (geoNum n V v : ℝ) =
      ∑ r : Fin n → K, (∏ i, (v i (r i) : ℝ)) * (geoNum n V (fun i => uv (r i)) : ℝ) := by
  rw [geoNum_expand n V hS v]
  push_cast
  rfl
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
