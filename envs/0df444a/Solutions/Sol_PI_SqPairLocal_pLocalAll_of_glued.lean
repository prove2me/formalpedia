-- Prove2me | solution 1 for PI.SqPairLocal.pLocalAll_of_glued
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:25.273519+00:00
-- url     : https://prove2.me/submissions/98612ccc-7302-4bb3-be20-df121f2fecd3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Theorems.Thm_PI_SqPairLocal_coe_smul
import Theorems.Thm_PI_SqPairLocal_three_small

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
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PI.SqPairLocal
theorem _root_.solution (h1 : LocGlob) (h2 : IntMul) (h3 : Glued) : PLocalAll := by
  unfold PLocalAll
  intro E _ _ _ hE N L' L'' hN h' h'' n hn p hp
  unfold PLocal
  obtain ⟨c, hc0, hc⟩ := h2 E N L' L'' h' h'' n hn
  obtain ⟨a, c', hc', hcc⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc0 p hp.ne_one
  obtain ⟨e, he', he'', hg⟩ := h3 E hE N L' L'' hN h' h'' p hp a
  refine ⟨e, he', he'', ?_⟩
  intro M hM y hy
  have hcast : ((c : ℕ) : 𝓞 E) = (c' : 𝓞 E) * (p : 𝓞 E) ^ a := by
    rw [hcc]; push_cast; ring
  let X : Submodule (𝓞 E) (Fin N → E) := (L' ⊓ L'').map (n • LinearMap.id)
  have hloc : ∀ Q : Ideal (𝓞 E), Q.IsMaximal → (p : 𝓞 E) ∈ Q →
      ∃ s : 𝓞 E, s ∉ Q ∧ s • ((c' : 𝓞 E) • (M *ᵥ y)) ∈ X := by
    intro Q hQ hpQ
    haveI : Q.IsPrime := hQ.isPrime
    have hsm := three_small he' he'' (hg Q hQ hpQ) M hM
    have key : ∃ s : 𝓞 E, s ∉ Q ∧ ∃ m, (m ∈ L' ∨ m ∈ L'') ∧
        s • (M *ᵥ y) = (p : 𝓞 E) ^ a • m := by
      rcases hy with hy | hy
      · obtain ⟨s, hs, m, hm, h⟩ := hsm.1 y hy
        exact ⟨s, hs, m, Or.inl hm, h⟩
      · obtain ⟨s, hs, m, hm, h⟩ := hsm.2 y hy
        exact ⟨s, hs, m, Or.inr hm, h⟩
    obtain ⟨s, hs, m, hm, h⟩ := key
    obtain ⟨m', hm1, hm2, hm'⟩ := hc m hm
    refine ⟨s, hs, ?_⟩
    rw [Submodule.mem_map]
    refine ⟨m', ⟨hm1, hm2⟩, ?_⟩
    show n • m' = s • ((c' : 𝓞 E) • (M *ᵥ y))
    rw [← hm', smul_smul, mul_comm s, ← smul_smul, h, smul_smul, ← hcast]
  obtain ⟨s, hsp, hsx⟩ := h1 E (Fin N → E) X ((c' : 𝓞 E) • (M *ᵥ y)) p hp hloc
  rw [Submodule.mem_map] at hsx
  obtain ⟨m, ⟨hm1, hm2⟩, hmeq⟩ := hsx
  have hmeq' : n • m = (s : 𝓞 E) • ((c' : 𝓞 E) • (M *ᵥ y)) := hmeq
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnd : ¬ (p : ℤ) ∣ s * (c' : ℤ) := by
    intro hd
    rcases hpZ.dvd_or_dvd hd with hd | hd
    · exact hsp hd
    · exact hc' (by exact_mod_cast hd)
  have heq : (((s * (c' : ℤ)) : ℤ) : 𝓞 E) • (M *ᵥ y) = n • m := by
    rw [hmeq', smul_smul]
    push_cast
    rfl
  refine ⟨s * (c' : ℤ), hnd, m, hm1, hm2, ?_⟩
  first
  | exact heq
  | simpa only [coe_smul, Int.cast_smul_eq_zsmul] using heq
  | simpa [coe_smul] using heq
end PI.SqPairLocal
