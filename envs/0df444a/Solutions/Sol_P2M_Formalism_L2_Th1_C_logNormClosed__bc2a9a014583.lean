-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_logNormClosed__bc2a9a014583
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:28:04.546266+00:00
-- url     : https://prove2.me/submissions/e0dc54d4-0a3b-458d-81e5-9bb417b4ea72

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_const
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_sub
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_mul
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_smul
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_Clo_isClosed_LG
import Theorems.Thm_Formalism_L2_Th1_C_Clo_cc_smul
import Theorems.Thm_Formalism_L2_Th1_C_Clo_coeffCont_fmul
import Theorems.Thm_Formalism_L2_Th1_C_Clo_cc_fmul
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_subst
import Theorems.Thm_Formalism_L2_Th1_C_Pts_mulBy_eq_fmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Clo
namespace Formalism.L2.Th1.C
theorem _root_.solution : PhNormClosed := by
  intro K _ _ _ _ R hR l linv ph hl hli hph
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 :=
    PowerSeries.constantCoeff_X
  have hc : CoeffCont fun p : K × K => fmul l linv p.1 (PowerSeries.X : MvPowerSeries Unit K) :=
    coeffCont_fmul hl linv continuous_fst hX
  have h0 : ∀ p : K × K, MvPowerSeries.constantCoeff
      (fmul l linv p.1 (PowerSeries.X : MvPowerSeries Unit K)) = 0 :=
    fun p => cc_fmul hl hli p.1 hX
  simp only [PhNormAt, Cong, Pts.mulBy_eq_fmul]
  refine isClosed_LG hR ((hc.subst h0 ph).sub
    (CoeffCont.smul (continuous_fst.mul continuous_snd) (CoeffCont.const _))) fun p => ?_
  rw [map_sub, Pts.constantCoeff_subst (h0 p) hph, cc_smul hph, sub_zero]
end Formalism.L2.Th1.C
