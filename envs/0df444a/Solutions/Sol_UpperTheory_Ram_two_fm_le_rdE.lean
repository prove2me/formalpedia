-- Prove2me | solution 1 for UpperTheory.Ram.two_fm_le_rdE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:58:43.022937+00:00
-- url     : https://prove2.me/submissions/02eb764e-982f-4c26-b941-3fd40e525727

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_LogQdLeRd
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_TwoFmLeRdE
import Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_rdE
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_UpperTheory_KR_log_qd_le_rd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Formalism.BasicNotions
namespace UpperTheory.Ram
theorem _root_.solution :
    ∀ (R : Ranks) (H : Host R), 2 * (R.f : ℝ) * R.m ≤ H.rdE ∧ 4 * (R.t : ℝ) * R.r + 1 ≤ H.rdE := by
  intro R H
  obtain ⟨hq, hd⟩ := H.qd_big
  obtain ⟨-, -, hsq, -⟩ := UpperTheory.KR.log_qd_le_rd H.toHostAx H.flPS
  have hrd : H.toHostAx.rd = H.rdE := rfl
  have hq' : H.toHostAx.q = H.q := rfl
  have hd' : H.toHostAx.d = H.d := rfl
  rw [hrd, hq', hd'] at hsq
  set X : ℝ := 4 * (R.t : ℝ) * R.r + 1 with hX
  have hX0 : 0 ≤ X := by positivity
  have hqX : X < (H.q : ℝ) := by
    have : ((4 * R.t * R.r + 1 : ℕ) : ℝ) < (H.q : ℝ) := by exact_mod_cast hq
    simpa [hX] using this
  have hdX : X < (H.d : ℝ) := by
    have : ((4 * R.t * R.r + 1 : ℕ) : ℝ) < (H.d : ℝ) := by exact_mod_cast hd
    simpa [hX] using this
  have hprod : X * X < (H.q : ℝ) * H.d := mul_lt_mul'' hqX hdX hX0 hX0
  have hsqrt : X < √((H.q : ℝ) * H.d) := by
    rw [show X = √(X * X) from (Real.sqrt_mul_self hX0).symm]
    exact Real.sqrt_lt_sqrt (by positivity) hprod
  have hmain : X ≤ H.rdE := le_trans hsqrt.le hsq
  refine ⟨?_, hmain⟩
  have hf : R.f ≤ R.k := by
    have := R.f_le_k
    simp only [Ranks.f, Ranks.n]
    omega
  have hm := R.two_le_m
  have hr : R.k + 1 ≤ R.r := by
    simp only [Ranks.r]
    omega
  have hmt : R.m ≤ R.t := by
    have := R.three_m_lt_t
    omega
  have hnat : 2 * R.f * R.m ≤ 4 * R.t * R.r + 1 := by
    have h1 : R.f ≤ R.r := by omega
    calc 2 * R.f * R.m ≤ 2 * R.r * R.t := by
          apply Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) hmt
      _ ≤ 4 * R.t * R.r + 1 := by nlinarith
  have : (2 * (R.f : ℝ) * R.m) ≤ X := by
    rw [hX]
    exact_mod_cast hnat
  linarith
end UpperTheory.Ram
