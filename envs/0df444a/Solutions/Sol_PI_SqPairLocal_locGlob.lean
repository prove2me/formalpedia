-- Prove2me | solution 1 for PI.SqPairLocal.locGlob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:49.044243+00:00
-- url     : https://prove2.me/submissions/22ab3fcf-2aff-4a30-afcd-1c640d07526c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Lemmata_GeneralBFactLeftBis_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_ExistsDenFg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
namespace PI.SqPairLocal
theorem _root_.solution : LocGlob := by
  intro E _ _ W _ _ X x p hp hloc
  let J : Ideal (𝓞 E) := X.comap (LinearMap.toSpanSingleton (𝓞 E) W x)
  have hJ : ∀ a, a ∈ J ↔ a • x ∈ X := fun a => by
    simp [J, LinearMap.toSpanSingleton_apply]
  have htop : J ⊔ Ideal.span {(p : 𝓞 E)} = ⊤ := by
    by_contra h
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨s, hs, hsx⟩ := hloc Q hQ (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    exact hs (hle (Ideal.mem_sup_left ((hJ s).mpr hsx)))
  have hpnu : Ideal.span {(p : 𝓞 E)} ≠ ⊤ := by
    intro h
    have h2 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_singleton, Algebra.norm_natCast, Ideal.absNorm_top, Int.natAbs_pow,
      Int.natAbs_natCast] at h2
    have hd : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
    rcases Nat.pow_eq_one.mp h2 with h1 | h1
    · exact hp.one_lt.ne' h1
    · omega
  have hJ0 : J ≠ ⊥ := by
    rintro h
    rw [h, bot_sup_eq] at htop
    exact hpnu htop
  have : Finite (𝓞 E ⧸ J) :=
    (Ideal.absNorm_ne_zero_iff J).mp (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have h1 : (1 : 𝓞 E) ∈ J ⊔ Ideal.span {(p : 𝓞 E)} := by rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  have hunit : Ideal.Quotient.mk J r * Ideal.Quotient.mk J (p : 𝓞 E) = 1 := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk J), ← hab, Ideal.Quotient.eq]
    have : r * (p : 𝓞 E) - (a + r * (p : 𝓞 E)) = -a := by ring
    rw [this]
    exact J.neg_mem ha
  have hndvd : ¬ p ∣ Ideal.absNorm J := by
    intro hdvd
    have := Fact.mk hp
    let := Fintype.ofFinite (𝓞 E ⧸ J)
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] at hdvd
    obtain ⟨z, hz⟩ := exists_prime_addOrderOf_dvd_card p hdvd
    have hpz : Ideal.Quotient.mk J (p : 𝓞 E) * z = 0 := by
      rw [map_natCast, ← nsmul_eq_mul, ← hz, addOrderOf_nsmul_eq_zero]
    have hz0 : z = 0 := by
      calc z = (Ideal.Quotient.mk J r * Ideal.Quotient.mk J (p : 𝓞 E)) * z := by rw [hunit, one_mul]
        _ = 0 := by rw [mul_assoc, hpz, mul_zero]
    rw [hz0, addOrderOf_zero] at hz
    exact hp.one_lt.ne hz
  refine ⟨Ideal.absNorm J, ?_, ?_⟩
  · exact_mod_cast hndvd
  · rw [Int.cast_natCast, ← hJ]
    exact Ideal.absNorm_mem J
end PI.SqPairLocal
