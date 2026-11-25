-- Prove2me | solution 1 for PI.SqPairW.crt_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:23:03.159686+00:00
-- url     : https://prove2.me/submissions/06bd62ae-f883-4f8a-8915-cd442c9ec706

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ExistsDenLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_SqPairGlueMain

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
theorem _root_.solution (R : Subring (Matrix (Fin N) (Fin N) E)) (f : ℕ → Matrix (Fin N) (Fin N) E) (K : ℕ)
    (S : Finset ℕ) : (∀ p ∈ S, p.Prime) → (∀ p ∈ S, f p ∈ R) →
    ∃ e ∈ R, ∀ p ∈ S, ∃ d ∈ R, e = f p + ((p : ℤ) ^ K) • d := by
  intro hprime hf
  classical
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ → ℤ, Q = fun p => ∏ q ∈ S.erase p, ((q : ℤ) ^ K) := ⟨_, rfl⟩
  have hcop : ∀ p ∈ S, ∃ a b : ℤ, a * (p : ℤ) ^ K + b * Q p = 1 := by
    intro p hp
    have h : IsCoprime ((p : ℤ) ^ K) (Q p) := by
      rw [hQdef]
      apply IsCoprime.prod_right
      intro q hq
      apply IsCoprime.pow
      exact Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (hprime p hp)
        (hprime q (Finset.mem_of_mem_erase hq))).2 (Finset.ne_of_mem_erase hq).symm)
    exact h
  choose! a b hab using hcop
  refine ⟨∑ q ∈ S, (b q * Q q) • f q, ?_, ?_⟩
  · exact sum_mem fun q hq => zsmul_mem (hf q hq) _
  · intro p hp
    have hdiv : ∀ q ∈ S.erase p, ∃ t : ℤ, Q q = (p : ℤ) ^ K * t := by
      intro q hq
      have hm : p ∈ S.erase q := Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hq).symm, hp⟩
      have hd := Finset.dvd_prod_of_mem (fun r : ℕ => ((r : ℤ) ^ K)) hm
      rw [hQdef]
      exact hd
    choose! t ht using hdiv
    refine ⟨(-a p) • f p + ∑ q ∈ S.erase p, (b q * t q) • f q,
      add_mem (zsmul_mem (hf p hp) _)
        (sum_mem fun q hq => zsmul_mem (hf q (Finset.mem_of_mem_erase hq)) _), ?_⟩
    have hsplit := Finset.add_sum_erase S (fun q => (b q * Q q) • f q) hp
    rw [← hsplit]
    have e1 : b p * Q p = 1 + (p : ℤ) ^ K * (-a p) := by linear_combination hab p hp
    have e2 : ∑ q ∈ S.erase p, (b q * Q q) • f q
        = ((p : ℤ) ^ K) • ∑ q ∈ S.erase p, (b q * t q) • f q := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [smul_smul, ht q hq]
      congr 1
      ring
    rw [e2, e1, add_smul, one_smul, smul_add, smul_smul, add_assoc]
end PI.SqPairW
