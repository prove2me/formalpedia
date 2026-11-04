-- Prove2me | solution 1 for ThreeSum.TernaryPairedMinorReindex.rowWeight_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:05.863175+00:00
-- url     : https://prove2.me/submissions/d27ee661-2525-4fa7-8089-0ec26bfb0a17

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedMinorReindex
import Theorems.Thm_ThreeSum_TernaryPairedMinorReindex_minorWeight_rows
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedMinorReindex
open Matrix Finset TernaryPairedPotential
open scoped BigOperators
namespace ThreeSum.TernaryPairedMinorReindex
theorem _root_.solution {ι : Type*} [Fintype ι] {Λ d : ℕ}
    (A : ι→Fin Λ→ℤ) (e : Fin d≃ι) :
    rowWeight A=minorWeight (fun i => A (e i)) := by
  have hd : Fintype.card ι=d := (Fintype.card_congr e).symm.trans (Fintype.card_fin d)
  subst d
  let t : Equiv.Perm (Fin (Fintype.card ι)) := e.trans (Fintype.equivFin ι)
  have he : (fun i => A (e i))=(fun i => A ((Fintype.equivFin ι).symm (t i))) := by
    funext i
    simp [t]
  rw [he]
  exact (minorWeight_rows (fun i j => A ((Fintype.equivFin ι).symm i) j) t).symm
end ThreeSum.TernaryPairedMinorReindex
