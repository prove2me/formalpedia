-- Prove2me | solution 1 for UpperTheory.Mu.tame_ext_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:30:19.969832+00:00
-- url     : https://prove2.me/submissions/b5e2078e-5210-4c25-bd1e-331791dd9b07

import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_TorsionReduceInjective
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_ResidueEisenstein
import Theorems.Thm_UpperTheory_Mu_tame_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open UpperTheory UpperTheory.Mu
variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))
namespace UpperTheory.Mu
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hw : Units.torsionOrder L + 1 < p) (hv : (p : 𝓞 L) ∈ v.asIdeal)
    (ε : (𝓞 L)ˣ →* ℂˣ) :
    ∃ θ : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ, θ ≠ 1 ∧ ∀ ζ : (𝓞 L)ˣ, (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 L) : L) ^ m = 1) →
      θ (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom ζ) = ε ζ := by
  have hv' : v.asIdeal ≠ ⊤ := v.isPrime.ne_top
  have hpos := Units.torsionOrder_pos L
  have hn : ((Units.torsionOrder L : ℕ) : 𝓞 L) ∉ v.asIdeal := by
    intro hn
    have hcop : Nat.Coprime (Units.torsionOrder L) p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hd
      have := Nat.le_of_dvd hpos hd
      omega
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : (1 : 𝓞 L) = (a : 𝓞 L) * ((Units.torsionOrder L : ℕ) : 𝓞 L) + (b : 𝓞 L) * ((p : ℕ) : 𝓞 L) := by
      have := congrArg (Int.cast : ℤ → 𝓞 L) hab
      push_cast at this
      exact this.symm
    apply hv'
    rw [Ideal.eq_top_iff_one, h1]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hn) (v.asIdeal.mul_mem_left _ hv)
  have hN : Units.torsionOrder L + 1 < Ideal.absNorm v.asIdeal := by
    have hd : Ideal.absNorm v.asIdeal ∣ p ^ Module.finrank ℤ (𝓞 L) := by
      have h1 := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hv)
      rwa [Ideal.absNorm_span_singleton, show ((p : ℕ) : 𝓞 L) = algebraMap ℤ (𝓞 L) (p : ℤ) by simp,
        Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hd
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hv' (Ideal.absNorm_eq_one_iff.1 (by simpa using hk))
    rw [hk]
    exact lt_of_lt_of_le hw (Nat.le_self_pow hk0 p)
  obtain ⟨θ, hθ, hθε⟩ := tame_ext L v hn hN (ε.comp (Units.torsion L).subtype)
  refine ⟨θ, hθ, fun ζ hζ => ?_⟩
  obtain ⟨m, hm, hζm⟩ := hζ
  have hmem : ζ ∈ Units.torsion L := by
    rw [Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    refine ⟨m, hm, ?_⟩
    apply Units.ext
    apply RingOfIntegers.ext
    simpa using hζm
  exact hθε ⟨ζ, hmem⟩
end UpperTheory.Mu
