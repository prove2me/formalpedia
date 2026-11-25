-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_TwoBlockPoint_cornU_mul_up__9d33fb3090fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:16.042037+00:00
-- url     : https://prove2.me/submissions/50e9a483-c4f2-4add-a762-8d270701be88

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
variable {K : Type} [CommRing K] (R : Subring K)
variable {a s : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution {u : Matrix (Fin s) (Fin s) K} (hu : IsUpUni u) (Y : Matrix (Fin a) (Fin s) K) :
    cornU (Y * u) = cornU Y := by
  unfold cornU
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hc : (j : ℕ) = 0 ∧ (i : ℕ) + 1 = a
  · rw [if_pos hc, if_pos hc, Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hu.2 j, mul_one]
    · intro k _ hk
      have hk' : (k : ℕ) ≠ j := fun e => hk (Fin.ext e)
      have hjk : j < k := by
        rw [Fin.lt_iff_val_lt_val]
        omega
      rw [hu.1 hjk, mul_zero]
    · simp
  · rw [if_neg hc, if_neg hc]
end Formalism.FourierDecayAlt.P.TwoBlockPoint
