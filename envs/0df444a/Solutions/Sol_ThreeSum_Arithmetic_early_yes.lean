-- Prove2me | solution 1 for ThreeSum.Arithmetic.early_yes
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:35:56.872297+00:00
-- url     : https://prove2.me/submissions/cda36786-a582-48d7-9b51-fd056a107b8d

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Exact arithmetic interface for the deterministic histogram construction

These are finite arithmetic and counting theorems.  They do not assert a
running-time bound or the existence of a word-RAM implementation.
-/

namespace ThreeSum.Arithmetic

open Finset
open scoped BigOperators

/-! ## Guarded arithmetic-to-radix lifts -/






















































































































/-! ## The weighted false-count identity -/















































































































































/-! ## Exact early YES from per-original-triple representation caps -/





theorem sum_fiberWeight {ι τ : Type*} [Fintype τ] [DecidableEq τ]
    (I : Finset ι) (owner : ι → τ) (weight : ι → ℕ) :
    (∑ t : τ, fiberWeight I owner weight t) = ∑ i ∈ I, weight i := by
  classical
  unfold fiberWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- If total represented mass exceeds `Rmax * H`, some positive incidence
belongs to a true original triple.  The hypotheses bound individual false
fibers and the number of false originals, rather than postulating the
desired conclusion or a full running-time theorem. -/
theorem early_yes_sourceProof {ι τ : Type*} [Fintype τ] [DecidableEq τ]
    (I : Finset ι) (owner : ι → τ) (weight : ι → ℕ)
    (good : τ → Prop) [DecidablePred good] (Rmax H : ℕ)
    (hcap : ∀ t : τ, ¬ good t → fiberWeight I owner weight t ≤ Rmax)
    (hcount : (Finset.univ.filter (fun t : τ => ¬ good t)).card ≤ H)
    (hlarge : Rmax * H < ∑ i ∈ I, weight i) :
    ∃ i ∈ I, 0 < weight i ∧ good (owner i) := by
  classical
  by_contra hnone
  have hzero : ∀ i ∈ I, good (owner i) → weight i = 0 := by
    intro i hi hg
    by_contra hw
    exact hnone ⟨i, hi, Nat.pos_of_ne_zero hw, hg⟩
  have hbound : ∀ t : τ, fiberWeight I owner weight t ≤
      if good t then 0 else Rmax := by
    intro t
    by_cases ht : good t
    · simp only [if_pos ht]
      have hz : fiberWeight I owner weight t = 0 := by
        unfold fiberWeight
        apply Finset.sum_eq_zero
        intro i hi
        by_cases he : owner i = t
        · simp [he, hzero i hi (he.symm ▸ ht)]
        · simp [he]
      omega
    · simpa [ht] using hcap t ht
  have hsum : (∑ t : τ, if good t then (0 : ℕ) else Rmax) =
      (Finset.univ.filter (fun t : τ => ¬ good t)).card * Rmax := by
    calc
      (∑ t : τ, if good t then (0 : ℕ) else Rmax) =
          ∑ t ∈ Finset.univ.filter (fun t : τ => ¬ good t), Rmax := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro t ht
        by_cases hg : good t <;> simp [hg]
      _ = _ := by simp
  have htotal : (∑ i ∈ I, weight i) ≤ Rmax * H := by
    calc
      (∑ i ∈ I, weight i) = ∑ t : τ, fiberWeight I owner weight t :=
        (sum_fiberWeight I owner weight).symm
      _ ≤ ∑ t : τ, if good t then 0 else Rmax :=
        Finset.sum_le_sum (fun t ht => hbound t)
      _ = (Finset.univ.filter (fun t : τ => ¬ good t)).card * Rmax := hsum
      _ ≤ H * Rmax := Nat.mul_le_mul_right Rmax hcount
      _ = Rmax * H := Nat.mul_comm _ _
  omega

end ThreeSum.Arithmetic

end

universe u_1 u_2

theorem solution : ∀ {ι : Type u_1} {τ : Type u_2} [inst : Fintype.{u_2} τ] [inst_1 : DecidableEq.{u_2 + 1} τ] (I : Finset.{u_1} ι)
  (owner : ι → τ) (weight : ι → Nat) (good : τ → Prop) [inst_2 : @DecidablePred.{u_2 + 1} τ good] (Rmax H : Nat),
  (∀ (t : τ),
      Not (good t) →
        @LE.le.{0} Nat instLENat (@ThreeSum.Arithmetic.fiberWeight.{u_1, u_2} ι τ inst_1 I owner weight t) Rmax) →
    @LE.le.{0} Nat instLENat (@Finset.card.{u_2} τ {t : τ | Not (good t)}) H →
      @LT.lt.{0} Nat instLTNat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Rmax H)
          (∑ i ∈ I, weight i) →
        ∃ (i : ι),
          And
            (@Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
              (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) I i)
            (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (weight i))
              (good (owner i))) := by
  exact @ThreeSum.Arithmetic.early_yes_sourceProof

#print axioms solution
