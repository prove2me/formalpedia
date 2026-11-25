-- Prove2me | solution 1 for UpperTheory.HF.norm_diff_EK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:51:21.042465+00:00
-- url     : https://prove2.me/submissions/b921c531-dbc5-4028-8388-90616196579c

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiscrK
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LogRdSum
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_NormDiffEK
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_finrank_cmField
import Theorems.Thm_Formalism_HC_HostAx_finrank_EK
import Theorems.Thm_Formalism_HC_HostAx_finrank_cmField
import Theorems.Thm_UpperTheory_HF_discr_K

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
private theorem absNorm_smul_gal {K : Type} [Field K] [NumberField K] (σ : K ≃ₐ[ℚ] K) (I : Ideal (𝓞 K)) :
    Ideal.absNorm (σ • I) = Ideal.absNorm I := by
  have e : (𝓞 K ⧸ I) ≃+* (𝓞 K ⧸ (σ • I)) :=
    Ideal.quotientEquiv I (σ • I) (MulSemiringAction.toRingEquiv (K ≃ₐ[ℚ] K) (𝓞 K) σ) rfl
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr e.toEquiv).symm
end

set_option autoImplicit false
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ), absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E)) * H.d ^ (2 * φ.ord) = (discr H.E).natAbs ∧ Real.log (absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E))) = 2 * (2 * φ.ord) * (Real.log H.rd - 1 / 2 * Real.log H.d) ∧ ∀ 𝔟 : Ideal (𝓞 H.E), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) → absNorm 𝔟 ^ 2 = absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E)) ∧ Real.log (absNorm 𝔟) = (2 * φ.ord) * (Real.log H.rd - 1 / 2 * Real.log H.d) := by
  intro φ H
  have h1 : absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E)) * H.d ^ (2 * φ.ord) = (discr H.E).natAbs := by
    have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow H.K (𝓞 H.K) H.E (𝓞 H.E)
    rw [H.finrank_EK, (UpperTheory.HF.discr_K H).1] at h
    exact h.symm
  have hd : discr H.E ≠ 0 := discr_ne_zero H.E
  have hd' : (discr H.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 hd
  have habs : |(discr H.E : ℝ)| = ((discr H.E).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hpos : 0 < |(discr H.E : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hd)
  have hn : absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact hd' h1.symm
  have hord : (φ.ord : ℝ) ≠ 0 := Nat.cast_ne_zero.2 φ.ord_pos.ne'
  have hrd : Real.log ((discr H.E).natAbs : ℝ) = 4 * φ.ord * Real.log H.rd := by
    unfold HostRaw.rd
    rw [Real.log_rpow hpos, habs, H.finrank_cmField]
    push_cast
    field_simp
  have h2 : Real.log (absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E))) =
      2 * (2 * φ.ord) * (Real.log H.rd - 1 / 2 * Real.log H.d) := by
    rw [← h1, Nat.cast_mul, Nat.cast_pow,
      Real.log_mul (Nat.cast_ne_zero.2 hn) (pow_ne_zero _ (Nat.cast_ne_zero.2 H.d_prime.ne_zero)),
      Real.log_pow] at hrd
    push_cast at hrd
    linarith
  refine ⟨h1, h2, fun 𝔟 h𝔟 => ?_⟩
  have h3 : absNorm 𝔟 ^ 2 = absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E)) := by
    rw [h𝔟, map_mul, absNorm_smul_gal, sq]
  refine ⟨h3, ?_⟩
  rw [← h3, Nat.cast_pow, Real.log_pow] at h2
  push_cast at h2
  linarith
end UpperTheory.HF
