-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_famI_eq_diff_5bf2b43907d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:58:25.541358+00:00
-- url     : https://prove2.me/submissions/be666ea9-592b-4f04-8caa-11399a0fc137

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_tensor_right_comm_a627b498d6de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_smooth_tensor_f6b0ee1175f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSmoothHerm_segreLine_1e1d36fff7ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_sec_mul_1c4c584656fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_sec_congr_ab81be1c66e7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSectionOn_up_95943556fabe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSectionOn_segre_f966ae4bfd55
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_famI_snoc_56c5b29ec694

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (hMul : RMulStatement) {n : ℕ} (hwd : WDAt (famI (ι := ι)) n)
include hMul hwd
namespace GroundTheory.Heights₂.Heights.Inter.ThmIExists
theorem _root_.solution {P : Ideal (MRing ι)} (hP : IsArithVar P (n + 1)) {L : Fin n → HermLine ι}
    (hL : ∀ j, IsSmoothHerm (L j)) {A C : HermLine ι} (hA : IsSmoothHerm A) (hC : IsSmoothHerm C)
    {t c : MRing ι} (ht : IsSectionOn P (A.tensor C) t) (hc : IsSectionOn P C c) :
    famI P (n + 1) (Fin.snoc L A) = recR famI P L (A.tensor C) t - recR famI P L C c := by
  have hpr : P.IsPrime := hP.2.1.1
  set H : HermLine ι := segreLine (shift A)
  have hH : IsSmoothHerm H := isSmoothHerm_segreLine _
  have hu := isSectionOn_segre hP (shift A)
  have ht0 := isSectionOn_up hP A
  have e1 := hMul K ι famI P n L (A.tensor H) C _ _ hP hL (smooth_tensor hA hH) hC ht0 hc
  have e2 := hMul K ι famI P n L (A.tensor C) H _ _ hP hL (smooth_tensor hA hC) hH ht hu
  have e3 : recR famI P L ((A.tensor H).tensor C) (secOf P (upDeg A) * c) =
      recR famI P L ((A.tensor C).tensor H) (t * secOf P fun _ => shift A) := by
    rw [tensor_right_comm A H C]
    exact hwd P L _ _ _ hP hL (smooth_tensor (smooth_tensor hA hC) hH)
      (sec_congr (tensor_right_comm A H C) (sec_mul hpr ht0 hc)) (sec_mul hpr ht hu)
  rw [famI_snoc]
  linarith
end GroundTheory.Heights₂.Heights.Inter.ThmIExists
