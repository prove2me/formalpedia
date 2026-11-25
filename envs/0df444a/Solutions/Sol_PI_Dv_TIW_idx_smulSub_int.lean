-- Prove2me | solution 1 for PI.Dv.TIW.idx_smulSub_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:06:36.514695+00:00
-- url     : https://prove2.me/submissions/5d20bd2c-d205-423b-a787-a19df8d438a8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
import Theorems.Thm_PI_Dv_TIW_vAdd_mul
import Theorems.Thm_PI_Dv_TIW_span_smulSub
import Theorems.Thm_PI_Dv_TIW_smulSub_smulSub
import Theorems.Thm_PI_Dv_TIW_fg_smulSub
import Theorems.Thm_PI_Dv_TIW_idx_smulSub_map
import Theorems.Thm_PI_Dv_TIW_idx_ge_int
import Theorems.Thm_PI_Dv_TIW_idx_le_natSub
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
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0)
    (M : Submodule (𝓞 K) V) (hM : M.FG) :
    idxAt w M (smulSub (algebraMap (𝓞 K) K a) M) = (Formalism.HN.rkK M : ℤ) * vAdd w (algebraMap (𝓞 K) K a) := by
  have haK : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha
  have hspan : Ideal.span {a} ≠ ⊥ := by simpa using ha
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {a}))
  set m := Ideal.absNorm (Ideal.span {a}) with hm
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rw [hm, Ne, Ideal.absNorm_eq_zero_iff]; exact hspan)
  have ha'0 : a' ≠ 0 := by
    rintro rfl
    rw [zero_mul] at ha'
    exact hm0.ne' (by exact_mod_cast ha'.symm)
  have ha'K : algebraMap (𝓞 K) K a' ≠ 0 := by simpa using ha'0
  have hmK : ((m : ℕ) : K) = algebraMap (𝓞 K) K a * algebraMap (𝓞 K) K a' := by
    rw [← map_mul, mul_comm, ha', map_natCast]
  have e1 := idx_chain hI w M (smulSub (algebraMap (𝓞 K) K a) M) (smulSub ((m : ℕ) : K) M) hM
    (fg_smulSub _ M hM) (fg_smulSub _ M hM) (span_smulSub _ haK M).symm
    (by rw [span_smulSub _ (by rw [hmK]; exact mul_ne_zero haK ha'K), span_smulSub _ haK])
  have e2 : idxAt w (smulSub (algebraMap (𝓞 K) K a) M) (smulSub ((m : ℕ) : K) M) =
      idxAt w M (smulSub (algebraMap (𝓞 K) K a') M) := by
    rw [hmK, ← smulSub_smulSub]
    exact idx_smulSub_map hI w _ haK M _ hM (fg_smulSub _ M hM) (span_smulSub _ ha'K M).symm
  have u := idx_le_natSub hI w m hm0 M hM
  have l1 := idx_ge_int hI w a ha M hM
  have l2 := idx_ge_int hI w a' ha'0 M hM
  rw [e1, e2, hmK, vAdd_mul w _ _ haK ha'K] at u
  nlinarith
end PI.Dv.TIW
