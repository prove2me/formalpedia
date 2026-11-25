-- Prove2me | solution 1 for UpperTheory.Mu.splitNotDvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:51:24.625906+00:00
-- url     : https://prove2.me/submissions/806a234c-66fb-43ef-acd4-932066ffc613

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_SplitNotDvd
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_QS_dvd_condN
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
open NumberField IsDedekindDomain Formalism.HC
open Ideal
namespace UpperTheory.Mu
theorem _root_.solution :
    ∀ (φ : Frame) (H : HostAx φ), H.toHostRaw.Exact → ∀ p : ℕ, p.Prime → {v : HeightOneSpectrum (𝓞 H.E) | ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.E → ¬ p ∣ H.QS := by
  intro φ H hex p hp hcard hdvd
  haveI hpf : Fact p.Prime := ⟨hp⟩
  haveI hgal : IsGalois ℚ H.E := H.galois
  obtain ⟨u, hu, hne⟩ := hex p hp hdvd
  set pZ : Ideal ℤ := Ideal.span {((p : ℕ) : ℤ)} with hpZ
  haveI hmax : pZ.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hmem : ∀ P : Ideal (𝓞 H.E), P.IsPrime → (((p : ℕ) : 𝓞 H.E) ∈ P ↔ P.LiesOver pZ) := by
    intro P hP
    constructor
    · intro h
      rw [Ideal.liesOver_iff]
      refine hmax.eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.comap _)) ?_
      rw [hpZ, Ideal.span_le, Set.singleton_subset_iff]
      simpa [Ideal.under] using h
    · intro h
      have hz : ((p : ℕ) : ℤ) ∈ Ideal.under ℤ P := by
        rw [← (Ideal.liesOver_iff P pZ).1 h]
        exact Ideal.subset_span rfl
      simpa [Ideal.under] using hz
  have hset : (pZ.primesOver (𝓞 H.E)).ncard = Module.finrank ℚ H.E := by
    rw [← hcard]
    have heq : pZ.primesOver (𝓞 H.E) =
        (fun v : HeightOneSpectrum (𝓞 H.E) => v.asIdeal) '' {v | ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal} := by
      ext P
      constructor
      · rintro ⟨hP, hl⟩
        have hnb : P ≠ ⊥ := by
          intro hb
          have hz := (hmem P hP).2 hl
          rw [hb, Ideal.mem_bot] at hz
          exact hp.ne_zero (by exact_mod_cast hz)
        exact ⟨⟨P, hP, hnb⟩, (hmem P hP).2 hl, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v.isPrime, (hmem _ v.isPrime).1 hv⟩
    rw [heq, Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)]
  have hn : 0 < Module.finrank ℚ H.E := Module.finrank_pos
  obtain ⟨P, hPp, hPl⟩ := Set.nonempty_of_ncard_ne_zero (hset ▸ hn.ne')
  haveI := hPp
  haveI := hPl
  have key := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank (G := Gal(H.E/ℚ)) pZ P
  rw [hset, IsGalois.card_aut_eq_finrank, mul_assoc] at key
  have h1 : Nat.card (Ideal.inertia Gal(H.E/ℚ) P) * P.inertiaDeg ℤ = 1 :=
    Nat.eq_of_mul_eq_mul_left hn (key.trans (mul_one _).symm)
  have hI : Nat.card (Ideal.inertia Gal(H.E/ℚ) P) = 1 := Nat.eq_one_of_mul_eq_one_right h1
  have hbot := Subgroup.eq_bot_of_card_eq _ hI
  set σ : Gal(H.E/ℚ) := H.gal.symm (H.art u) with hσ
  have hin : ∀ x : 𝓞 H.E, σ • x - x ∈ P := by
    refine (H.der.inertia p P σ).2 ⟨u, ?_, by simp [σ]⟩
    refine Nat.ModEq.of_dvd ?_ hu
    have hpc : p ∣ H.condN := dvd_trans hdvd (HostRaw.QS_dvd_condN _)
    have hv : p ^ H.condN.factorization p ∣ H.condN := Nat.ordProj_dvd _ _
    refine Nat.div_dvd_div_left hv ?_
    exact dvd_pow_self p (Nat.Prime.factorization_pos_of_dvd hp (HostRaw.condN_ne_zero _) hpc).ne'
  have hσI : σ ∈ Ideal.inertia Gal(H.E/ℚ) P := AddSubgroup.mem_inertia.2 hin
  rw [hbot, Subgroup.mem_bot] at hσI
  apply hne
  simpa [σ] using congrArg H.gal hσI
end UpperTheory.Mu
