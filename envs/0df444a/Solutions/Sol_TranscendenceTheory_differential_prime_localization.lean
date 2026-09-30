-- Prove2me | solution 1 for TranscendenceTheory.differential_prime_localization
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T17:06:03.148101+00:00
-- url     : https://prove2.me/submissions/c96a0520-a6b8-47b2-89c1-060cd8882106

import Definitions.Def_TranscendenceTheory_PrimeMultiplicityData
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Tactic

noncomputable section
namespace TranscendenceTheory

private lemma extend_derivation (R S : Type*) [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] [Algebra R S] [IsScalarTower ℚ R S]
    (M : Submonoid R) [IsLocalization M S] (D : Derivation ℚ R R) :
    ∃ d : Derivation ℚ S S, ∀ a : R, d (algebraMap R S a) = algebraMap R S (D a) := by
  let : Algebra.FormallyEtale R S := Algebra.FormallyEtale.of_isLocalization (Rₘ := S) M
  let d₀ : Derivation ℚ R S := (Algebra.linearMap R S).compDer D
  let F := d₀.liftKaehlerDifferential.liftBaseChange S
  let E := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℚ R S
  let d : Derivation ℚ S S :=
    (F.comp E.symm.toLinearMap).compDer (KaehlerDifferential.D ℚ S)
  refine ⟨d, ?_⟩
  intro a
  change F (E.symm (KaehlerDifferential.D ℚ S (algebraMap R S a))) = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  simp only [F, LinearMap.liftBaseChange_tmul, one_smul,
    Derivation.liftKaehlerDifferential_comp_D]
  rfl

private lemma iter_add {R : Type*} [CommRing R] [Algebra ℚ R]
    (D : Derivation ℚ R R) (n : ℕ) (f g : R) :
    (D^[n]) (f + g) = (D^[n]) f + (D^[n]) g := by
  simpa only [Module.End.pow_apply] using! (D.toLinearMap ^ n).map_add f g

private lemma jets_mul {R : Type*} [CommRing R] [Algebra ℚ R]
    (D : Derivation ℚ R R) (p : Ideal R) (n : ℕ)
    (f : R) (hf : ∀ j ≤ n, (D^[j]) f ∈ p) (a : R) :
    ∀ j ≤ n, (D^[j]) (a * f) ∈ p := by
  induction n generalizing a f with
  | zero =>
    intro j hj
    have : j = 0 := by omega
    subst j
    simpa only [Function.iterate_zero_apply] using p.mul_mem_left a (hf 0 le_rfl)
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

private lemma iter_commutes {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] (D : Derivation ℚ R R) (d : Derivation ℚ S S)
    (f : R →+* S) (h : ∀ a, d (f a) = f (D a)) (n : ℕ) (a : R) :
    (d^[n]) (f a) = f ((D^[n]) a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, h, Function.iterate_succ_apply']


end TranscendenceTheory

open TranscendenceTheory

theorem solution
    (R : Type*) [CommRing R] [Algebra ℚ R]
    (D : Derivation ℚ R R) (p : Ideal R) [p.IsPrime] :
    ∃ d : Derivation ℚ (Localization.AtPrime p) (Localization.AtPrime p),
      (∀ a : R, d (algebraMap R (Localization.AtPrime p) a) =
        algebraMap R (Localization.AtPrime p) (D a)) ∧
      ∀ (I : Ideal R) (T : ℕ),
        (∀ f ∈ I, ∀ j ≤ T, (D^[j]) f ∈ p) ↔
        (∀ f ∈ I.map (algebraMap R (Localization.AtPrime p)), ∀ j ≤ T,
          (d^[j]) f ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p)) := by
  classical
  let S := Localization.AtPrime p
  let f : R →+* S := algebraMap R S
  let m : Ideal S := IsLocalRing.maximalIdeal S
  obtain ⟨d, hd⟩ := extend_derivation R S p.primeCompl D
  refine ⟨d, hd, ?_⟩
  intro I T
  constructor
  · intro hI z hz
    change z ∈ Ideal.span (f '' (I : Set R)) at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      intro j hj
      rw [iter_commutes D d f hd j a]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S p _).mpr (hI a ha j hj)
    | zero =>
      intro j hj
      simpa only [Module.End.pow_apply] using!
        (show (d.toLinearMap ^ j) 0 ∈ m by simp)
    | add a b ha hb iha ihb =>
      intro j hj
      rw [iter_add]
      exact m.add_mem (iha j hj) (ihb j hj)
    | smul a b hb ih =>
      simpa only [smul_eq_mul] using jets_mul d m T b ih a
  · intro hI a ha j hj
    have h := hI (f a) (Ideal.mem_map_of_mem f ha) j hj
    rw [iter_commutes D d f hd j a] at h
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S p _).mp h
