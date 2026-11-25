-- Prove2me | solution 1 for PI.Dv.TIW.idx_ge_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:33.574134+00:00
-- url     : https://prove2.me/submissions/20f05535-00aa-401c-8d54-24c3a8db178c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
import Theorems.Thm_PI_Dv_TIW_mem_pow_of_vAdd
import Theorems.Thm_PI_Dv_TIW_mem_smulSub
import Theorems.Thm_PI_Dv_TIW_span_smulSub
import Theorems.Thm_PI_Dv_TIW_fg_smulSub
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_TIW_one_notMem_w
import Theorems.Thm_PI_Dv_TIW_volume_nonneg
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
    vAdd w (algebraMap (𝓞 K) K a) * (Formalism.HN.rkK M : ℤ) ≤ idxAt w M (smulSub (algebraMap (𝓞 K) K a) M) := by
  have haK : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha
  have hsp := (span_smulSub (algebraMap (𝓞 K) K a) haK M).symm
  have := (hI K V w M _ hM (fg_smulSub _ M hM) hsp).2.2.2.1 (vAdd w (algebraMap (𝓞 K) K a)).toNat
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := (mem_smulSub _ M x).mp hx
      refine ⟨1, one_notMem_w w, ?_⟩
      rw [one_smul, algebraMap_smul]
      exact Submodule.smul_mem_smul (mem_pow_of_vAdd w a ha) hy)
  rwa [Int.toNat_of_nonneg (volume_nonneg K w a)] at this
end PI.Dv.TIW
