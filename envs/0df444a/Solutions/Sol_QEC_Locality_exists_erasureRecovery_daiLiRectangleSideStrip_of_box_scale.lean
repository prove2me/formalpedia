-- Prove2me | solution 1 for QEC.Locality.exists_erasureRecovery_daiLiRectangleSideStrip_of_box_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:20:08.337145+00:00
-- url     : https://prove2.me/submissions/0ab50ca7-b924-439b-a85d-274ffe0eb237

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_card_daiLiRectangleSideStrip_lt_distance_of_box_scale
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiRectangleSideStrip_of_card_lt


set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableCorrectable
namespace QEC.Locality
theorem _root_.solution
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (ell w : ℝ) (lower upper : ℝ × ℝ) (hEll : 1 ≤ ell)
    (hCellWidth : 5 * ell ≤ w) (hSpan : upper.1 - lower.1 = w)
    (hMinimumHeight : 5 * ell ≤ upper.2 - lower.2)
    (hMaximumHeight : upper.2 - lower.2 ≤ w)
    (hSideScale : 12 * ell * w < d) (side : Fin 4) :
    ∃ recovery : QuantumChannel
        (daiLiRectangleSideStripSubsystem embedding ell lower upper side).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiRectangleSideStripSubsystem embedding ell lower upper side).complementSystem
        P.semanticCode
        (daiLiRectangleSideStripSubsystem embedding ell lower upper side).erasureChannelFromRegister
          recovery := by
  have hCardReal := card_daiLiRectangleSideStrip_lt_distance_of_box_scale
    embedding d ell w lower upper hEll hCellWidth hSpan hMinimumHeight hMaximumHeight
      hSideScale side
  have hCard : (daiLiRectangleSideStripQubits embedding ell lower upper side).card < d := by
    exact_mod_cast hCardReal
  exact exists_erasureRecovery_daiLiRectangleSideStrip_of_card_lt P embedding d hDistance ell
    lower upper side hCard
end QEC.Locality
