-- Prove2me | solution 1 for PI.SqPairW.sqPairGlue_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:57.642771+00:00
-- url     : https://prove2.me/submissions/2f49c227-e9f1-45eb-abc0-725a981694e2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ExistsDenLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_SqPairGlueMain
import Theorems.Thm_PI_SqPairW_crt_exists
import Theorems.Thm_PI_SqPairW_conjTranspose_mem_lam
import Theorems.Thm_PI_SqPairW_exists_den
import Theorems.Thm_PI_SqPairW_mem_of_local
import Theorems.Thm_PI_SqPairW_mset_cong
import Theorems.Thm_PI_SqPairW_mset_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairW
open Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
namespace PI.SqPairW
theorem _root_.solution : PI.SqPair.PLocalAll → SplitPairGen := by
  intro hP E _ _ _ hCM N L' L'' hN hL' hL'' n hn
  have hloc := hP E hCM N L' L'' hN hL' hL'' n hn
  unfold PI.SqPair.PLocal at hloc
  choose! f hf1 hf2 hf3 using hloc
  have hstar : ∀ x ∈ lam L' L'', xᴴ ∈ lam L' L'' := fun x hx => conjTranspose_mem_lam hL' hL'' hx
  obtain ⟨D, hD0, hD⟩ := exists_den hL' hL'' hn
  obtain ⟨e, heR, he⟩ := crt_exists (lam L' L'') f D D.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) (fun p hp => ⟨hf1 p (Nat.prime_of_mem_primeFactors hp),
      hf2 p (Nat.prime_of_mem_primeFactors hp)⟩)
  refine ⟨e, heR.1, heR.2, ?_⟩
  intro M hM y hy

  have himg : ∀ r ∈ lam L' L'', r *ᵥ y ∈ L' ∨ r *ᵥ y ∈ L'' := by
    intro r hr
    rcases hy with hy | hy
    · exact Or.inl (hr.1 y hy)
    · exact Or.inr (hr.2 y hy)
  have key : M *ᵥ y ∈ yg L' L'' n := by
    apply mem_of_local
    intro p hp
    by_cases hpD : p ∣ D
    · have hpS : p ∈ D.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpD, hD0.ne'⟩
      obtain ⟨d, hdR, hed⟩ := he p hpS
      rw [hed] at hM
      obtain ⟨M', hM', r, hrR, hMr⟩ := mset_cong hstar ⟨hf1 p hp, hf2 p hp⟩ hdR ((p : ℤ) ^ D) M hM
      obtain ⟨s, hps, m, hm1, hm2, hsm⟩ := hf3 p hp M' hM' y hy
      have hs : s • (M' *ᵥ y) ∈ yg L' L'' n := by
        rw [← Int.cast_smul_eq_zsmul E, hsm]
        exact ⟨m, hm1, hm2, rfl⟩
      have hr : (D : ℤ) • (r *ᵥ y) ∈ yg L' L'' n := hD _ (himg r hrR)
      obtain ⟨a, D', hpD', hDa⟩ := Nat.exists_eq_pow_mul_and_not_dvd hD0.ne' p hp.ne_one
      have ha : a ≤ D := by
        have h1 : p ^ a ≤ D := Nat.le_of_dvd hD0 ⟨D', hDa⟩
        have h2 : a < p ^ a := Nat.lt_pow_self hp.one_lt
        omega
      have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      refine ⟨s * D', ?_, ?_⟩
      · intro hdvd
        rcases hpZ.dvd_or_dvd hdvd with h | h
        · exact hps h
        · exact hpD' (Int.natCast_dvd_natCast.mp h)
      · have e1 : (s * (D' : ℤ)) • (M *ᵥ y) =
            (D' : ℤ) • (s • (M' *ᵥ y)) + (s * (p : ℤ) ^ (D - a)) • ((D : ℤ) • (r *ᵥ y)) := by
          have hpow : (p : ℤ) ^ D = (p : ℤ) ^ (D - a) * (p : ℤ) ^ a := by
            rw [← pow_add, Nat.sub_add_cancel ha]
          have hDZ : (D : ℤ) = (p : ℤ) ^ a * (D' : ℤ) := by rw [hDa]; push_cast; ring
          rw [hMr, add_mulVec, smul_mulVec, hpow, hDZ]
          module
        rw [e1]
        exact (yg L' L'' n).add_mem ((yg L' L'' n).zsmul_mem hs _) ((yg L' L'' n).zsmul_mem hr _)
    · refine ⟨D, fun h => hpD (Int.natCast_dvd_natCast.mp h), ?_⟩
      exact hD _ (himg M (mset_sub hstar heR M hM))
  obtain ⟨m, h1, h2, h3⟩ := key
  exact ⟨m, h1, h2, h3⟩
end PI.SqPairW
