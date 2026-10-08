-- Prove2me | solution 1 for PlunneckeType.Abelian.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-08T01:09:06.42201+00:00
-- url     : https://prove2.me/submissions/4b9ebbd7-57fb-4417-b5fd-2bbd01af43dd

-- SPDX-License-Identifier: Apache-2.0
-- Complete proof of Prove2Me 958c55cc-a922-4af7-a37f-9a8fa52b4f3f.
-- New complete proof using finite ratio minimization and the proved Mathlib Petridis inequality.
import Mathlib

set_option autoImplicit false


-- BEGIN MODULE RatioMinimizer
section

open scoped Pointwise
open Finset
namespace PlunneckeType.Abelian.Proof

lemma exists_ratio_minimizer {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B : Finset G) (α : ℝ) (hA : A.Nonempty)
    (hAB : (#(A+B) : ℝ) ≤ α * #A) :
    ∃ X ⊆ A, X.Nonempty ∧
      (∀ Z ⊆ X, #(X+B) * #Z ≤ #(Z+B) * #X) ∧
      (#(X+B) : ℝ) ≤ α * #X := by
  classical
  let F : Finset (Finset G) := A.powerset.erase ∅
  have hAF : A ∈ F := by simp [F,hA.ne_empty]
  obtain ⟨X,hXF,hmin⟩ := F.exists_min_image
    (fun Z => (#(Z+B) : ℝ) / #Z) ⟨A,hAF⟩
  have hX : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hXF).1
  have hXA : X ⊆ A := Finset.mem_powerset.mp (Finset.mem_erase.mp hXF).2
  have hxpos : (0 : ℝ) < #X := by exact_mod_cast hX.card_pos
  have hapos : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  refine ⟨X,hXA,hX,?_,?_⟩
  · intro Z hZX
    by_cases hz : Z = ∅
    · simp [hz]
    · have hZF : Z ∈ F := by
        simp only [F,Finset.mem_erase,Finset.mem_powerset]
        exact ⟨hz,hZX.trans hXA⟩
      have hzpos : (0 : ℝ) < #Z := by
        exact_mod_cast (Finset.nonempty_iff_ne_empty.mpr hz).card_pos
      have hr := hmin Z hZF
      have hc := (div_le_div_iff₀ hxpos hzpos).mp hr
      exact_mod_cast hc
  · have hr := hmin A hAF
    have ha : (#(A+B) : ℝ) / #A ≤ α := (div_le_iff₀ hapos).mpr hAB
    exact (div_le_iff₀ hxpos).mp (hr.trans ha)

end PlunneckeType.Abelian.Proof
end
-- END MODULE RatioMinimizer

-- BEGIN MODULE IteratedGrowth
section
set_option autoImplicit false
open scoped Pointwise
open Finset
namespace PlunneckeType.Abelian.Proof

lemma uniform_iterated_growth {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X B : Finset G) (α : ℝ) (hX : X.Nonempty)
    (hmin : ∀ Z ⊆ X, #(X+B) * #Z ≤ #(Z+B) * #X)
    (hXB : (#(X+B) : ℝ) ≤ α * #X) :
    ∀ h : ℕ, (#(X + h • B) : ℝ) ≤ α ^ h * #X := by
  have hpos : (0:ℝ) < #X := by exact_mod_cast hX.card_pos
  have hα : 0 ≤ α := by
    have hnonneg : (0:ℝ) ≤ #(X+B) := Nat.cast_nonneg _
    nlinarith
  intro h
  induction h with
  | zero => simp
  | succ h ih =>
    have hp : (#((h • B) + X + B) : ℝ) * #X ≤
        (#(X+B) : ℝ) * #((h • B) + X) := by
      exact_mod_cast Finset.pluennecke_petridis_inequality_add (h • B) hmin
    have he : X + (h+1) • B = (h • B) + X + B := by
      rw [succ_nsmul, add_left_comm, add_assoc]
    have hh : (#(X + (h+1) • B) : ℝ) * #X ≤ α * #X * #(X + h • B) := by
      rw [he]
      calc
        (#((h • B) + X + B) : ℝ) * #X ≤ (#(X+B) : ℝ) * #((h • B) + X) := hp
        _ ≤ (α * #X) * #((h • B) + X) := mul_le_mul_of_nonneg_right hXB (Nat.cast_nonneg _)
        _ = α * #X * #(X + h • B) := by rw [add_comm (h • B) X]
    have hstep : (#(X + (h+1) • B) : ℝ) ≤ α * #(X + h • B) := by
      apply (mul_le_mul_iff_left₀ hpos).mp
      nlinarith [hh]
    calc
      (#(X + (h+1) • B) : ℝ) ≤ α * #(X + h • B) := hstep
      _ ≤ α * (α^h * #X) := mul_le_mul_of_nonneg_left ih hα
      _ = α^(h+1) * #X := by ring

end PlunneckeType.Abelian.Proof
end
-- END MODULE IteratedGrowth

-- BEGIN MODULE UniformGrowth
section
open scoped Pointwise
open Finset

namespace PlunneckeType.Abelian

/-- Petridis, *New proofs of Plünnecke-type estimates for product sets in groups*,
arXiv:1101.3507v3, p. 7, Theorem 3.1. In an abelian group, if `|A + B| ≤ α|A|` and `A` is
nonempty, then one nonempty `X ⊆ A` satisfies `|X + hB| ≤ α^h |X|` for every `h`, where
`hB = h • B` is the `h`-fold sumset (`0 • B = {0}`). The same `X` serves every `h`. Without
`X.Nonempty` the statement would be satisfied by `X = ∅`. -/
theorem theorem_3_1 {G : Type*} [AddCommGroup G] [DecidableEq G] (A B : Finset G) (α : ℝ)
    (hA : A.Nonempty) (hAB : (#(A + B) : ℝ) ≤ α * #A) :
    ∃ X ⊆ A, X.Nonempty ∧ ∀ h : ℕ, (#(X + h • B) : ℝ) ≤ α ^ h * #X := by
  obtain ⟨X,hXA,hX,hmin,hXB⟩ := Proof.exists_ratio_minimizer A B α hA hAB
  exact ⟨X,hXA,hX,Proof.uniform_iterated_growth X B α hX hmin hXB⟩

end PlunneckeType.Abelian

end
-- END MODULE UniformGrowth

-- BEGIN MODULE PublicSolution
section
open scoped Pointwise
open Finset

theorem solution {G : Type*} [AddCommGroup G] [DecidableEq G] (A B : Finset G) (α : ℝ)
    (hA : A.Nonempty) (hAB : (#(A + B) : ℝ) ≤ α * #A) :
    ∃ X ⊆ A, X.Nonempty ∧ ∀ h : ℕ, (#(X + h • B) : ℝ) ≤ α ^ h * #X := by
  exact PlunneckeType.Abelian.theorem_3_1 A B α hA hAB


end
-- END MODULE PublicSolution

#print axioms PlunneckeType.Abelian.theorem_3_1
#print axioms solution
