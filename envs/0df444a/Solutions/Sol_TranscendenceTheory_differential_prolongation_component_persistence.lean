-- Prove2me | solution 1 for TranscendenceTheory.differential_prolongation_component_persistence
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T19:44:14.254002+00:00
-- url     : https://prove2.me/submissions/ba0813a5-7e20-4c45-8b81-e86df09c7170

import Definitions.Def_WeierstrassEllipticZeta_ChartProlongationData
import Mathlib.Tactic

namespace TranscendenceTheory

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]

private lemma iter_add (D : Derivation K R R) (n : ℕ) (f g : R) :
    (D^[n]) (f + g) = (D^[n]) f + (D^[n]) g := by
  simpa only [Module.End.pow_apply] using! (D.toLinearMap ^ n).map_add f g

private lemma jets_mul (D : Derivation K R R) (p : Ideal R) (n : ℕ)
    (f : R) (hf : ∀ j < n, (D^[j]) f ∈ p) (a : R) :
    ∀ j < n, (D^[j]) (a * f) ∈ p := by
  induction n generalizing a f with
  | zero => simp
  | succ n ih =>
    intro j hj
    cases j with
    | zero => simpa using p.mul_mem_left a (hf 0 (by omega))
    | succ j =>
      rw [Function.iterate_succ_apply, D.leibniz, smul_eq_mul, smul_eq_mul, iter_add]
      apply p.add_mem
      · apply ih (D f) _ a j (by omega)
        intro k hk
        simpa only [← Function.iterate_succ_apply] using hf (k + 1) (by omega)
      · rw [mul_comm f (D a)]
        exact ih f (fun k hk => hf k (by omega)) (D a) j (by omega)

private lemma span_jets (D : Derivation K R R) (s : Set R) (p : Ideal R) (n : ℕ)
    (hs : ∀ f ∈ s, ∀ k ≤ n, (D^[k]) f ∈ p) :
    ∀ f ∈ Ideal.span s, ∀ k ≤ n, (D^[k]) f ∈ p := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf => exact hs f hf
  | zero =>
    intro k hk
    simpa only [Module.End.pow_apply] using!
      (show (D.toLinearMap ^ k) 0 ∈ p by simp)
  | add f g _ _ ihf ihg =>
    intro k hk
    rw [iter_add]
    exact p.add_mem (ihf k hk) (ihg k hk)
  | smul a f _ ih =>
    intro k hk
    simpa only [smul_eq_mul] using
      jets_mul D p (n + 1) f (fun j hj => ih j (by omega)) a k (by omega)

private lemma prolong_le_iff (D : Derivation K R R) (I J : Ideal R) (n : ℕ) :
    differentialProlongation D I n ≤ J ↔ ∀ f ∈ I, ∀ k ≤ n, (D^[k]) f ∈ J := by
  rw [differentialProlongation, Ideal.span_le]
  constructor
  · intro h f hf k hk
    exact h ⟨f, hf, k, hk, rfl⟩
  · rintro h r ⟨f, hf, k, hk, rfl⟩
    exact h f hf k hk

private lemma prolong_mono (D : Derivation K R R) (I : Ideal R) {m n : ℕ}
    (hmn : m ≤ n) : differentialProlongation D I m ≤ differentialProlongation D I n := by
  apply (prolong_le_iff D I _ m).mpr
  intro f hf k hk
  exact Ideal.subset_span ⟨f, hf, k, hk.trans hmn, rfl⟩

private lemma prolong_comp (D : Derivation K R R) (I : Ideal R) (m n : ℕ) :
    differentialProlongation D (differentialProlongation D I m) n =
      differentialProlongation D I (m + n) := by
  apply le_antisymm
  · apply (prolong_le_iff D _ _ n).mpr
    apply span_jets D _ _ n
    rintro r ⟨f, hf, j, hj, rfl⟩ k hk
    rw [← Function.iterate_add_apply]
    exact Ideal.subset_span ⟨f, hf, k + j, by omega, rfl⟩
  · apply (prolong_le_iff D _ _ (m + n)).mpr
    intro f hf j hj
    refine Ideal.subset_span ⟨(D^[min j m]) f,
      Ideal.subset_span ⟨f, hf, min j m, Nat.min_le_right _ _, rfl⟩,
      j - min j m, by omega, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.min_le_left _ _)]


end TranscendenceTheory

open TranscendenceTheory

theorem solution
    (K R : Type*) [CommRing K] [CommRing R] [Algebra K R]
    (D : Derivation K R R) (I : Ideal R) :
    differentialProlongation D I 0 = I ∧
    (∀ m n : ℕ, differentialProlongation D (differentialProlongation D I m) n =
      differentialProlongation D I (m + n)) ∧
    ∀ (m n : ℕ) (p : Ideal R), p ∈ (differentialProlongation D I m).minimalPrimes →
      (p ∈ (differentialProlongation D I (m + n)).minimalPrimes ↔
        ∀ f ∈ differentialProlongation D I m, ∀ k ≤ n, (D^[k]) f ∈ p) := by
  refine ⟨?_, prolong_comp D I, ?_⟩
  · apply le_antisymm
    · apply (prolong_le_iff D I I 0).mpr
      intro f hf k hk
      have hk0 : k = 0 := by omega
      simpa [hk0] using hf
    · intro f hf
      exact Ideal.subset_span ⟨f, hf, 0, le_rfl, rfl⟩
  · intro m n p hp
    have hmono := prolong_mono D I (Nat.le_add_right m n)
    constructor
    · intro hend
      apply (prolong_le_iff D _ p n).mp
      rw [prolong_comp]
      exact hend.le
    · intro hjets
      have hle : differentialProlongation D I (m + n) ≤ p := by
        rw [← prolong_comp D I m n]
        exact (prolong_le_iff D _ p n).mpr hjets
      refine ⟨⟨hp.isPrime, hle⟩, ?_⟩
      intro q hq hqp
      exact hp.2 ⟨hq.1, hmono.trans hq.2⟩ hqp
