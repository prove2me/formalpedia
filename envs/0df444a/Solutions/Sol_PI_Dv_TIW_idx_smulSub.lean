-- Prove2me | solution 1 for PI.Dv.TIW.idx_smulSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:18.746682+00:00
-- url     : https://prove2.me/submissions/bdadda79-a798-450c-b184-2ddf6ceb651b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
import Theorems.Thm_PI_Dv_TIW_vAdd_mul
import Theorems.Thm_PI_Dv_TIW_span_smulSub
import Theorems.Thm_PI_Dv_TIW_smulSub_smulSub
import Theorems.Thm_PI_Dv_TIW_fg_smulSub
import Theorems.Thm_PI_Dv_TIW_idx_smulSub_map
import Theorems.Thm_PI_Dv_TIW_idx_smulSub_int
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_TIW_idx_chain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.TIW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (d : K) (hd : d ≠ 0)
    (M : Submodule (𝓞 K) V) (hM : M.FG) :
    idxAt w M (smulSub d M) = (Formalism.HN.rkK M : ℤ) * vAdd w d := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) d
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := by simpa using hb0
  have haK : algebraMap (𝓞 K) K a ≠ 0 := by
    intro h; apply hd; rw [h, zero_div]
  have ha0 : a ≠ 0 := by intro h; apply haK; rw [h, map_zero]
  set d := algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b with hd'
  have hda : d * algebraMap (𝓞 K) K b = algebraMap (𝓞 K) K a := by
    rw [hd', div_mul_cancel₀ _ hbK]
  have e1 := idx_chain hI w M (smulSub d M) (smulSub (algebraMap (𝓞 K) K a) M) hM
    (fg_smulSub _ M hM) (fg_smulSub _ M hM) (span_smulSub _ hd M).symm
    (by rw [span_smulSub _ haK, span_smulSub _ hd])
  have e2 : idxAt w (smulSub d M) (smulSub (algebraMap (𝓞 K) K a) M) =
      idxAt w M (smulSub (algebraMap (𝓞 K) K b) M) := by
    rw [← hda, ← smulSub_smulSub]
    exact idx_smulSub_map hI w _ hd M _ hM (fg_smulSub _ M hM) (span_smulSub _ hbK M).symm
  rw [e2, idx_smulSub_int hI w a ha0 M hM, idx_smulSub_int hI w b hb0 M hM] at e1
  have hv : vAdd w (algebraMap (𝓞 K) K a) = vAdd w d + vAdd w (algebraMap (𝓞 K) K b) := by
    rw [← hda, vAdd_mul w _ _ hd hbK]
  rw [hv] at e1
  linarith
end PI.Dv.TIW
