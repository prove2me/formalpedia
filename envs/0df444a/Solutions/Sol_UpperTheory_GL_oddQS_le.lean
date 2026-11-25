-- Prove2me | solution 1 for UpperTheory.GL.oddQS_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:46:54.281201+00:00
-- url     : https://prove2.me/submissions/e9696a43-639a-4d26-9963-838ea6d3c9de

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_OddQSLe
import Theorems.Thm_Formalism_HC_Frame_ord_le_o_mul_two_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal
namespace UpperTheory.GL
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostRaw φ) (C : ℝ), (φ.o : ℝ) ≤ C → (H.QS : ℝ) ≤ C * φ.ord → ((ordCompl[2] H.QS : ℕ) : ℝ) ≤ C ^ 2 := by
  intro φ H C ho hQ
  have h0 : H.QS ≠ 0 := H.QS_pos.ne'
  have hC : (0 : ℝ) ≤ C := (Nat.cast_nonneg _).trans ho
  have h1 : φ.e + 2 ≤ H.QS.factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization h0).1 H.tower_dvd
  have h2 : 2 ^ φ.e * ordCompl[2] H.QS ≤ H.QS := by
    conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self H.QS 2]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos (by omega))
  have h3 : (φ.ord : ℝ) ≤ φ.o * 2 ^ φ.e := by exact_mod_cast φ.ord_le_o_mul_two_pow
  have h4 : (2 : ℝ) ^ φ.e * ((ordCompl[2] H.QS : ℕ) : ℝ) ≤ H.QS := by exact_mod_cast h2
  have hp : (0 : ℝ) < 2 ^ φ.e := by positivity
  have h5 : (φ.ord : ℝ) ≤ C * 2 ^ φ.e := h3.trans (mul_le_mul_of_nonneg_right ho hp.le)
  refine le_of_mul_le_mul_left ?_ hp
  calc (2 : ℝ) ^ φ.e * ((ordCompl[2] H.QS : ℕ) : ℝ) ≤ C * φ.ord := h4.trans hQ
    _ ≤ C * (C * 2 ^ φ.e) := mul_le_mul_of_nonneg_left h5 hC
    _ = 2 ^ φ.e * C ^ 2 := by ring
end UpperTheory.GL
