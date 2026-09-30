-- Prove2me | solution 1 for TranscendenceTheory.finite_quotient_degree_stabilization
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-21T05:13:30.919981+00:00
-- url     : https://prove2.me/submissions/33c03408-8891-474b-bc8b-ed9ec874128d

import Definitions.Def_TranscendenceTheory_PolynomialQuotientDegreeFiltration
import Mathlib.Tactic

noncomputable section
namespace TranscendenceTheory
open MvPolynomial

variable {K σ : Type*} [Field K]

lemma quotientDegreeImage_mono (I : Ideal (MvPolynomial σ K)) {m n : ℕ} (h : m ≤ n) :
    quotientDegreeImage I m ≤ quotientDegreeImage I n := by
  apply Submodule.map_mono
  intro p hp
  exact (mem_restrictTotalDegree _ _ _).mpr (((mem_restrictTotalDegree _ _ _).mp hp).trans h)

lemma quotientDegreeImage_eq_top_of_stable (I : Ideal (MvPolynomial σ K)) (n : ℕ)
    (heq : quotientDegreeImage I n = quotientDegreeImage I (n + 1)) :
    quotientDegreeImage I n = ⊤ := by
  apply top_unique
  intro a ha
  clear ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction p using MvPolynomial.induction_on with
  | C r =>
      exact ⟨C r, (mem_restrictTotalDegree _ _ _).mpr (by simp), rfl⟩
  | add p q hp hq =>
      simpa only [map_add] using (quotientDegreeImage I n).add_mem hp hq
  | mul_X p i hp =>
      obtain ⟨q, hq, hqp⟩ := hp
      rw [heq]
      refine ⟨q * X i, (mem_restrictTotalDegree _ _ _).mpr ?_, ?_⟩
      · exact (totalDegree_mul _ _).trans (by
          rw [totalDegree_X]
          exact Nat.add_le_add_right ((mem_restrictTotalDegree _ _ _).mp hq) 1)
      · change Ideal.Quotient.mk I (q * X i) = Ideal.Quotient.mk I (p * X i)
        rw [map_mul, map_mul]
        exact congrArg (fun a => a * Ideal.Quotient.mk I (X i)) hqp

lemma quotientDegreeImage_stable_of_rank_eq [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ)
    (h : Module.finrank K (quotientDegreeImage I n) =
      Module.finrank K (quotientDegreeImage I (n + 1))) :
    quotientDegreeImage I n = ⊤ := by
  apply quotientDegreeImage_eq_top_of_stable I n
  exact Submodule.eq_of_le_of_finrank_eq (quotientDegreeImage_mono I (Nat.le_succ n)) h

lemma quotientDegreeImage_degree_pred_eq_top [Finite σ]
    (I : Ideal (MvPolynomial σ K)) [Module.Finite K (MvPolynomial σ K ⧸ I)] :
    quotientDegreeImage I (Module.finrank K (MvPolynomial σ K ⧸ I) - 1) = ⊤ := by
  let A := MvPolynomial σ K ⧸ I
  by_cases hA : Subsingleton A
  · let := hA
    exact Subsingleton.elim _ _
  let : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
  have hone (n : ℕ) : (1 : A) ∈ quotientDegreeImage I n := by
    exact ⟨1, (mem_restrictTotalDegree _ _ _).mpr (by simp), by simp⟩
  have hpos (n : ℕ) : 0 < Module.finrank K (quotientDegreeImage I n) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨⟨1, hone n⟩, fun h => one_ne_zero (congrArg Subtype.val h)⟩
  have hstep (n : ℕ) (hn : quotientDegreeImage I n ≠ ⊤) :
      quotientDegreeImage I n < quotientDegreeImage I (n + 1) := by
    refine lt_of_le_of_ne (quotientDegreeImage_mono I (Nat.le_succ n)) ?_
    intro heq
    exact hn (quotientDegreeImage_eq_top_of_stable I n heq)
  have hbound (n : ℕ) (hn : quotientDegreeImage I n ≠ ⊤) :
      n + 1 ≤ Module.finrank K (quotientDegreeImage I n) := by
    induction n with
    | zero => exact hpos 0
    | succ n ih =>
        have hprev : quotientDegreeImage I n ≠ ⊤ := by
          intro ht
          apply hn
          exact top_unique (ht ▸ quotientDegreeImage_mono I (Nat.le_succ n))
        have hi := ih hprev
        have hlt := Submodule.finrank_lt_finrank_of_lt (hstep n hprev)
        omega
  by_contra hne
  have hd := hbound (Module.finrank K A - 1) hne
  have hlt : Module.finrank K (quotientDegreeImage I (Module.finrank K A - 1)) <
      Module.finrank K A := by
    have hh := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hne)
    simpa only [finrank_top] using hh
  have ha : 0 < Module.finrank K A := Module.finrank_pos
  omega


end TranscendenceTheory

open TranscendenceTheory MvPolynomial

theorem solution
    (K σ : Type*) [Field K] [Finite σ] (I : Ideal (MvPolynomial σ K)) :
    (∀ n : ℕ,
      Module.finrank K (quotientDegreeImage I n) =
        Module.finrank K (quotientDegreeImage I (n + 1)) →
      Module.Finite K (MvPolynomial σ K ⧸ I) ∧
      quotientDegreeImage I n = ⊤ ∧
      Module.finrank K (quotientDegreeImage I n) =
        Module.finrank K (MvPolynomial σ K ⧸ I)) ∧
    (Module.Finite K (MvPolynomial σ K ⧸ I) →
      quotientDegreeImage I (Module.finrank K (MvPolynomial σ K ⧸ I) - 1) = ⊤ ∧
      ∀ p : MvPolynomial σ K, ∃ q : MvPolynomial σ K,
        q.totalDegree ≤ Module.finrank K (MvPolynomial σ K ⧸ I) - 1 ∧ q - p ∈ I) := by
  constructor
  · intro n h
    have ht := quotientDegreeImage_stable_of_rank_eq I n h
    have hfinite : Module.Finite K (MvPolynomial σ K ⧸ I) :=
      Module.Finite.of_surjective (quotientDegreeImage I n).subtype (by
        intro a
        exact ⟨⟨a, ht ▸ Submodule.mem_top⟩, rfl⟩)
    exact ⟨hfinite, ht, by rw [ht, finrank_top]⟩
  · intro hfinite
    let : Module.Finite K (MvPolynomial σ K ⧸ I) := hfinite
    have ht := quotientDegreeImage_degree_pred_eq_top I
    refine ⟨ht, ?_⟩
    intro p
    have hp : Ideal.Quotient.mk I p ∈
        quotientDegreeImage I (Module.finrank K (MvPolynomial σ K ⧸ I) - 1) := by
      rw [ht]
      exact Submodule.mem_top
    obtain ⟨q, hq, hqp⟩ := hp
    exact ⟨q, (mem_restrictTotalDegree _ _ _).mp hq,
      (Ideal.Quotient.eq (I := I)).mp hqp⟩
