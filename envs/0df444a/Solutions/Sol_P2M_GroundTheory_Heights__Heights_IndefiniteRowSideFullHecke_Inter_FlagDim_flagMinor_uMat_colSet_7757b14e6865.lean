-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_flagMinor_uMat_colSet_7757b14e6865
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:51:33.066113+00:00
-- url     : https://prove2.me/submissions/d350fb2e-b1c9-4f23-90a3-618148226fcf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_uMat_of_lt_2beb305303e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_orderEmbOfFin_colSet_2a78ac479b4f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
theorem _root_.solution (F : Type) [Field F] {n : ℕ} (j : Fin (n - 1)) (c : Fin n) (hc : j.val ≤ c.val) :
    flagMinor (uMat F n) j ⟨colSet j.val c, colSet_card j.val c hc⟩ =
      (∏ k : Fin j.val, uMat F n ⟨k.val, by omega⟩ ⟨k.val, by omega⟩) * uMat F n ⟨j.val, by omega⟩ c := by
  have hj := j.2
  simp only [flagMinor]
  rw [orderEmbOfFin_colSet j.val c hc, Matrix.det_of_isUpperTriangular, Fin.prod_univ_castSucc]
  · congr 1
    · refine Finset.prod_congr rfl fun k _ => ?_
      simp only [Matrix.submatrix_apply, rowCols, Fin.val_castSucc, dif_pos (And.intro k.2 (by omega : k.val < c.val))]
      rfl
    · simp only [Matrix.submatrix_apply, rowCols, Fin.val_last, lt_irrefl, false_and, dif_neg, not_false_eq_true]
      rfl
  · intro a b hab
    simp only [Matrix.submatrix_apply]
    apply uMat_of_lt
    simp only [rowCols]
    have hb : b.val < j.val := by simp only [id, Fin.lt_def] at hab; omega
    rw [dif_pos ⟨hb, by omega⟩]
    simp only [Fin.lt_def, Fin.val_castLE] at hab ⊢
    exact hab
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
