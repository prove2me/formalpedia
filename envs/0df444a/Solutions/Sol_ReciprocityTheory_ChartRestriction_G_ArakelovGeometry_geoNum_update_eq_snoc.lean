-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.geoNum_update_eq_snoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:44:19.07271+00:00
-- url     : https://prove2.me/submissions/514a1584-3d64-41a5-9857-74272ad50062

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
theorem _root_.solution (m : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt (m + 1) V) (x e : K → ℤ)
    (i : Fin (m + 1)) :
    geoNum (m + 1) V (Function.update (fun _ => x) i e) = geoNum (m + 1) V (Fin.snoc (fun _ => x) e) := by
  rw [← hS _ (Equiv.swap i (Fin.last m)), Function.update_comp_equiv]
  rw [show (Equiv.swap i (Fin.last m)).symm i = Fin.last m by simp]
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · simp [Fin.snoc_castSucc]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
