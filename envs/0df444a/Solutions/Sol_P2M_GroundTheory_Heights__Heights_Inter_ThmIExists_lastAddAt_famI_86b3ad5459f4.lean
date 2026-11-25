-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_lastAddAt_famI_86b3ad5459f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:17.791872+00:00
-- url     : https://prove2.me/submissions/39a32b78-6402-42e7-a23a-c8484496c0ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_tensor_tensor_comm_cc0e4bf9cb6b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_smooth_tensor_f6b0ee1175f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSmoothHerm_segreLine_1e1d36fff7ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_sec_mul_1c4c584656fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_sec_congr_ab81be1c66e7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSectionOn_up_95943556fabe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSectionOn_segre_f966ae4bfd55
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_famI_eq_diff_5bf2b43907d8

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
theorem _root_.solution : LastAddAt (famI (ι := ι)) n := by
  intro P L A B hP hL hA hB
  have hpr : P.IsPrime := hP.2.1.1
  set Ha : HermLine ι := segreLine (shift A)
  set Hb : HermLine ι := segreLine (shift B)
  have hHa : IsSmoothHerm Ha := isSmoothHerm_segreLine _
  have hHb : IsSmoothHerm Hb := isSmoothHerm_segreLine _
  have hua := isSectionOn_segre hP (shift A)
  have hub := isSectionOn_segre hP (shift B)
  have hta := isSectionOn_up hP A
  have htb := isSectionOn_up hP B
  have htab : IsSectionOn P ((A.tensor B).tensor (Ha.tensor Hb))
      (secOf P (upDeg A) * secOf P (upDeg B)) :=
    sec_congr (tensor_tensor_comm A Ha B Hb) (sec_mul hpr hta htb)
  rw [famI_eq_diff hMul hwd hP hL (smooth_tensor hA hB) (smooth_tensor hHa hHb) htab (sec_mul hpr hua hub),
    famI_eq_diff hMul hwd hP hL hA hHa hta hua, famI_eq_diff hMul hwd hP hL hB hHb htb hub,
    tensor_tensor_comm A B Ha Hb,
    hMul K ι famI P n L _ _ _ _ hP hL (smooth_tensor hA hHa) (smooth_tensor hB hHb) hta htb,
    hMul K ι famI P n L _ _ _ _ hP hL hHa hHb hua hub]
  ring
end GroundTheory.Heights₂.Heights.Inter.ThmIExists
