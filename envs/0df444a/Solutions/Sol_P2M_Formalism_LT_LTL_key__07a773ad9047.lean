-- Prove2me | solution 1 for P2M_Formalism_LT_LTL_key__07a773ad9047
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:08:31.544716+00:00
-- url     : https://prove2.me/submissions/709154dc-ae07-42ce-be85-9aa08bfee2bf

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_Near_mul
import Theorems.Thm_P2M_Formalism_LT_LTL_subst_eq__d02f90c570e8
import Theorems.Thm_Formalism_G_LogCR_Agree_mono
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_LT_InvIntP_Low_add
import Theorems.Thm_Formalism_LT_InvIntP_Low_mono
import Theorems.Thm_Formalism_LT_InvIntP_Low_mul
import Theorems.Thm_Formalism_LT_InvIntP_agree_psubst
import Theorems.Thm_Formalism_LT_InvIntP_low_of_agree
import Theorems.Thm_Formalism_LT_InvIntP_low_one
import Theorems.Thm_Formalism_LT_InvIntP_low_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] {ι : Type*}
namespace Formalism.LT.LTL
theorem _root_.solution [Finite ι] (f : PowerSeries K) (h0 : constantCoeff f = 0)
    {N : ℕ} {a b : MvPowerSeries ι K}
    (ha0 : MvPowerSeries.constantCoeff a = 0) (hb0 : MvPowerSeries.constantCoeff b = 0)
    (hab : Agree N a b) : Low (N + 1) (f.subst a - f.subst b - coeff 1 f • (a - b)) := by
  rw [subst_eq' f h0 ha0, subst_eq' f h0 hb0]
  have e : coeff 1 f • a + a ^ 2 * (tail2 f).subst a - (coeff 1 f • b + b ^ 2 * (tail2 f).subst b)
      - coeff 1 f • (a - b) =
      a ^ 2 * ((tail2 f).subst a - (tail2 f).subst b) + (a - b) * (a + b) * (tail2 f).subst b := by
    rw [smul_sub]; ring
  rw [e]
  refine Low.add ?_ ?_
  · have h2 : Low 2 (a ^ 2) := by
      rw [pow_two]; exact (low_one ha0).mul (low_one ha0)
    exact (h2.mul (low_of_agree (agree_psubst _ ha0 hb0 hab))).mono (by omega)
  · have hs : Low 1 (a + b) := (low_one ha0).add (low_one hb0)
    simpa using ((low_of_agree hab).mul hs).mul (low_zero ((tail2 f).subst b))
end Formalism.LT.LTL
