-- Prove2me | solution 1 for UpperTheory.GL.realClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:38:09.292636+00:00
-- url     : https://prove2.me/submissions/49050afa-8378-447a-87db-104960bde554

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_realCond
import Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_realClass
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_isPrimOf_iff
import Theorems.Thm_QH_real_cond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal
private theorem realClass_sq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hreal : ∀ a : ZMod N, (χ a).im = 0) : χ ^ 2 = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply' χ two_ne_zero, MulChar.one_apply u.isUnit]
  have hn : ‖χ (u : ZMod N)‖ = 1 := DirichletCharacter.unit_norm_eq_one χ u
  have him : (χ (u : ZMod N)).im = 0 := hreal _
  set z := χ (u : ZMod N) with hz
  have h1 : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
  have h2 : z.re ^ 2 = 1 := by
    have := Complex.sq_norm z
    rw [hn, Complex.normSq_apply, him] at this
    nlinarith
  rw [h1]; exact_mod_cast h2
private theorem realClass_level_dvd {φ : Frame} (H : HostRaw φ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : H.IsCharE χ) : N ∣ H.condN := by
  obtain ⟨θ, hθ⟩ := h
  have e := (H.isPrimOf_iff θ ⟨N, χ, hθ.1⟩).1 hθ
  have e2 : N = (H.dir θ).conductor := congrArg Formalism.HC.PChar.N e
  rw [e2]
  exact DirichletCharacter.conductor_dvd_level _
end

set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal
namespace UpperTheory.GL
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostRaw φ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsCharE χ →
      N ∣ H.condN ∧ ((∀ a : ZMod N, (χ a).im = 0) → N ∣ 8 * ordCompl[2] H.QS ∨ H.q ∣ N ∨ H.d ∣ N) := by
  intro φ H N _ χ hχ
  have hdvd := realClass_level_dvd H χ hχ
  refine ⟨hdvd, fun hreal => ?_⟩
  have hp : χ.IsPrimitive := by
    obtain ⟨θ, hθ⟩ := hχ
    exact hθ.1
  have h2 := realClass_sq χ hreal
  by_cases hqd : H.q ∣ N ∨ H.d ∣ N
  · exact Or.inr hqd
  · left
    have hq : H.q.Prime := H.hyp.1
    have hd : H.d.Prime := H.hyp.2.1
    rw [not_or] at hqd
    have hN : N ∣ 8 * ordCompl[2] H.QS * H.q * H.d := by
      refine QH.real_cond _ H.q H.d N χ hp h2 (dvd_mul_right _ _) hq hd fun p hpp hpN => ?_
      have h3 : p ∣ H.QS * H.q * H.d := hpN.trans hdvd
      rcases hpp.dvd_mul.1 h3 with h4 | h4
      · rcases hpp.dvd_mul.1 h4 with h5 | h5
        · left
          rw [← Nat.ordProj_mul_ordCompl_eq_self H.QS 2] at h5
          rcases hpp.dvd_mul.1 h5 with h6 | h6
          · exact ((hpp.dvd_of_dvd_pow h6).trans (by norm_num)).mul_right _
          · exact h6.mul_left _
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp hq).1 h5))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hpp hd).1 h4))
    have cq : N.Coprime H.q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hqd.1).symm
    have cd : N.Coprime H.d := ((Nat.Prime.coprime_iff_not_dvd hd).2 hqd.2).symm
    exact cq.dvd_of_dvd_mul_right (cd.dvd_of_dvd_mul_right hN)
end UpperTheory.GL
