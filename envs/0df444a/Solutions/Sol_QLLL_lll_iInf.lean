-- Prove2me | solution 1 for QLLL.lll_iInf
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:48:13.179589+00:00
-- url     : https://prove2.me/submissions/93246f45-cdee-4add-a26a-f0ed68d9c210

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_LocalLemma_Infinite
import Mathlib

-- inline helpers from QuantumLocalLemma.LocalLemma.Basic
/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# The Quantum Lovász Local Lemma

Formalization of Ambainis, Kempe, Sattath, *A Quantum Lovász Local Lemma*
(arXiv:0911.1696).

## Design

The paper observes, after its Theorem 14, that the proof uses only properties
(i)-(iv) of its Lemma 8, i.e. that these "are the only properties of `R` we
need in the proof". We take that literally: the local lemma is proved once for
an abstract `Valuation` on a bounded lattice, and then instantiated at

* `Submodule 𝕜 V` with `relDim X = finrank X / finrank V`, giving the quantum
  LLL (Theorem 14 of the paper), and
* a probability space with `Pr`, giving the classical asymmetric LLL
  (Erdős-Lovász 1975, Theorem 13 of the paper).

Mathlib currently contains no Lovász local lemma in either form, so the second
instantiation is a contribution independent of the paper.

## Main statements

* `Valuation.cond_inf_mul` : Lemma 8(iii), the chain rule.
* `Valuation.cond_ge_of_notMem` : Lemma 15, the inductive heart.
* `Valuation.lll` : Theorem 14, the asymmetric local lemma.
* `Valuation.lll_symmetric` : Theorem 4, the symmetric version.
-/

namespace QLLL

open Finset

namespace Valuation

variable {α : Type*} [Lattice α] [BoundedOrder α]

variable (R : Valuation α)

theorem nonneg (x : α) : 0 ≤ R x := R.nonneg' x

theorem monotone : Monotone (R : α → ℝ) := R.monotone'

theorem modular (x y : α) : R x + R y = R (x ⊔ y) + R (x ⊓ y) := R.modular' x y

theorem map_top : R ⊤ = 1 := R.map_top'

/-- A division-free form of Lemma 8(vi), which is what the proofs below
actually use. Multiplying (vi) by `R z` is valid even when `R z = 0`. -/
theorem inf_add_inf_le (x y z : α) :
    R (x ⊓ z) + R (y ⊓ z) ≤ R z + R (x ⊓ y ⊓ z) := by
  have hmod := R.modular (x ⊓ z) (y ⊓ z)
  have hinf : (x ⊓ z) ⊓ (y ⊓ z) = x ⊓ y ⊓ z := by
    rw [inf_inf_inf_comm, inf_idem]
  have hle : R ((x ⊓ z) ⊔ (y ⊓ z)) ≤ R z :=
    R.monotone (sup_le inf_le_right inf_le_right)
  rw [hinf] at hmod
  linarith

variable {n : ℕ} {X : Fin n → α} {Γ : Fin n → Finset (Fin n)} {y : Fin n → ℝ}

end Valuation

/-! ## Instantiation at subspaces: relative dimension -/

open Module

variable {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]

variable [FiniteDimensional 𝕜 V] [Nontrivial V]

/-! ## TODO

* Lemma 11: two projectors acting on disjoint sets of qubits are mutually
  R-independent. This is the step that needs the tensor-product structure
  `⨂ i, H i` (`PiTensorProduct`), and is expected to be the hardest part of the
  definitional layer.
* Corollary 16 / Corollary 5: a `k`-QSAT instance of rank-`≤ r` projectors in
  which every qubit appears in at most `2 ^ k / (e * r * k)` projectors is
  satisfiable.
* Instantiate `Valuation` at a probability space to obtain the classical
  asymmetric LLL (Theorem 13).
-/

end QLLL


-- inline helpers from QuantumLocalLemma.LocalLemma.Infinite
/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# The local lemma for an infinite index set

`QuantumLocalLemma.LocalLemma.Basic` proves the local lemma for finitely many events, indexed by
`Fin n`. This file removes the finiteness of the index set.

The observation that makes it work: the proof of `key_mul` uses the dependency
hypothesis at exactly one point, to say that `X i` is independent of the finite
family `S \ Γ i` when `i ∉ S`. Phrased as "independent of every finite set of
non-neighbours not containing `i`", that condition never mentions `univ`, so the
index type need not be finite at all. `prod_le_inf_of` therefore bounds every
finite meet, for an arbitrary index type.

Only the last step, passing from all finite meets to the meet of the whole
family, needs anything new, and what it needs is continuity from above. That is
supplied here as an explicit hypothesis rather than assumed silently, because it
is exactly the axiom the finite theory lacks:

* `QuantumLocalLemma.Quantum.NoCompactness` shows the classical compactness route is unavailable
  for subspaces, so continuity cannot be dodged.
* `relDim X = dim X / dim V` cannot satisfy it, since it requires finite
  dimension in the first place.
* A normalised trace on a finite von Neumann algebra can: it is a `[0,1]`-valued
  dimension on a complete projection lattice, modularity is the Kaplansky
  formula, and normality of the trace is precisely continuity from above.

So the combinatorial content is proved unconditionally, and the analytic content
is isolated in one named hypothesis.
-/

namespace QLLL

open Finset

variable {α : Type*} [Lattice α] [BoundedOrder α] (R : Valuation α)
variable {ι : Type*} {X : ι → α} {Γ : ι → Finset ι} {y : ι → ℝ}

/-- Multiplicative form of Lemma 15, for an arbitrary index type. -/
private theorem key_mul_of (hΓ : IsDependencyGraphOn R X Γ)
    (hy₀ : ∀ i, 0 ≤ y i) (hy₁ : ∀ i, y i < 1)
    (hX : ∀ i, 1 - y i * ∏ j ∈ Γ i, (1 - y j) ≤ R (X i)) :
    ∀ (m : ℕ) (S : Finset ι) (i : ι), S.card ≤ m → i ∉ S →
      (1 - y i) * R (S.inf X) ≤ R (X i ⊓ S.inf X) := by
  classical
  have hy1' : ∀ j, 0 < 1 - y j := fun j => by linarith [hy₁ j]
  have hPle : ∀ i, (∏ j ∈ Γ i, (1 - y j)) ≤ 1 := fun i =>
    Finset.prod_le_one (fun j _ => (hy1' j).le) (fun j _ => by linarith [hy₀ j])
  have hXge : ∀ i, 1 - y i ≤ R (X i) := by
    intro i
    have h₁ : y i * (∏ j ∈ Γ i, (1 - y j)) ≤ y i * 1 :=
      mul_le_mul_of_nonneg_left (hPle i) (hy₀ i)
    linarith [hX i]
  intro m
  induction m with
  | zero =>
    intro S i hcard hi
    have hS : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hS
    simp only [Finset.inf_empty, inf_top_eq]
    rw [R.map_top, mul_one]
    exact hXge i
  | succ m ih =>
    intro S i hcard hi
    set D := S ∩ Γ i with hDdef
    set I := S \ Γ i with hIdef
    have hDS : D ⊆ S := Finset.inter_subset_left
    have hIS : I ⊆ S := Finset.sdiff_subset
    have hDΓ : D ⊆ Γ i := Finset.inter_subset_right
    have hdisj : Disjoint D I := by
      rw [Finset.disjoint_left]
      intro a haD haI
      rw [hDdef, Finset.mem_inter] at haD
      rw [hIdef, Finset.mem_sdiff] at haI
      exact haI.2 haD.2
    have hSDI : D ∪ I = S := by
      rw [hDdef, hIdef, Finset.union_comm]
      exact Finset.sdiff_union_inter S (Γ i)
    have hinfS : S.inf X = D.inf X ⊓ I.inf X := by
      rw [← hSDI, Finset.inf_union]
    have inner : ∀ D' : Finset ι, D' ⊆ D →
        (∏ j ∈ D', (1 - y j)) * R (I.inf X) ≤ R (D'.inf X ⊓ I.inf X) := by
      intro D'
      induction D' using Finset.induction_on with
      | empty =>
        intro _
        simp only [Finset.prod_empty, Finset.inf_empty, one_mul, top_inf_eq]
        exact le_rfl
      | @insert j D'' hj ihD =>
        intro hsub
        have hD''sub : D'' ⊆ D := (Finset.subset_insert j D'').trans hsub
        have hjD : j ∈ D := hsub (Finset.mem_insert_self j D'')
        have hjS : j ∈ S := hDS hjD
        have hjnot : j ∉ D'' ∪ I := by
          rw [Finset.mem_union]
          rintro (h | h)
          · exact hj h
          · exact (Finset.disjoint_left.mp hdisj hjD) h
        have hcardT : (D'' ∪ I).card ≤ m := by
          have hsubS : D'' ∪ I ⊆ S.erase j := by
            intro a ha
            rw [Finset.mem_erase]
            refine ⟨fun hEq => hjnot (hEq ▸ ha), ?_⟩
            rcases Finset.mem_union.mp ha with h | h
            · exact hDS (hD''sub h)
            · exact hIS h
          have hc := Finset.card_le_card hsubS
          rw [Finset.card_erase_of_mem hjS] at hc
          have hpos : 0 < S.card := Finset.card_pos.mpr ⟨j, hjS⟩
          omega
        have hkey := ih (D'' ∪ I) j hcardT hjnot
        rw [Finset.inf_union] at hkey
        rw [Finset.prod_insert hj, Finset.inf_insert, inf_assoc]
        calc ((1 - y j) * ∏ k ∈ D'', (1 - y k)) * R (I.inf X)
            = (1 - y j) * ((∏ k ∈ D'', (1 - y k)) * R (I.inf X)) := by ring
          _ ≤ (1 - y j) * R (D''.inf X ⊓ I.inf X) :=
              mul_le_mul_of_nonneg_left (ihD hD''sub) (hy1' j).le
          _ ≤ R (X j ⊓ (D''.inf X ⊓ I.inf X)) := hkey
    -- the one place the dependency hypothesis is used, and it needs no `univ`
    have hiI : i ∉ I := fun h => hi (hIS h)
    have hdisjI : Disjoint I (Γ i) := Finset.sdiff_disjoint
    have hindep : R (X i ⊓ I.inf X) = R (X i) * R (I.inf X) := hΓ i I hiI hdisjI
    have hPD : (∏ j ∈ Γ i, (1 - y j)) ≤ ∏ j ∈ D, (1 - y j) := by
      have hA1 : (∏ j ∈ Γ i \ D, (1 - y j)) ≤ 1 :=
        Finset.prod_le_one (fun j _ => (hy1' j).le) (fun j _ => by linarith [hy₀ j])
      have hBpos : 0 < ∏ j ∈ D, (1 - y j) := Finset.prod_pos fun j _ => hy1' j
      rw [← Finset.prod_sdiff hDΓ]
      calc (∏ j ∈ Γ i \ D, (1 - y j)) * (∏ j ∈ D, (1 - y j))
          ≤ 1 * (∏ j ∈ D, (1 - y j)) := mul_le_mul_of_nonneg_right hA1 hBpos.le
        _ = _ := one_mul _
    have hden : (∏ j ∈ Γ i, (1 - y j)) * R (I.inf X) ≤ R (D.inf X ⊓ I.inf X) :=
      le_trans (mul_le_mul_of_nonneg_right hPD (R.nonneg _)) (inner D Finset.Subset.rfl)
    have hvi := R.inf_add_inf_le (X i) (D.inf X) (I.inf X)
    have h₁ : 1 - R (X i) ≤ y i * ∏ j ∈ Γ i, (1 - y j) := by linarith [hX i]
    have h₂ : (1 - R (X i)) * R (I.inf X)
        ≤ (y i * ∏ j ∈ Γ i, (1 - y j)) * R (I.inf X) :=
      mul_le_mul_of_nonneg_right h₁ (R.nonneg _)
    have h₃ : y i * ((∏ j ∈ Γ i, (1 - y j)) * R (I.inf X))
        ≤ y i * R (D.inf X ⊓ I.inf X) :=
      mul_le_mul_of_nonneg_left hden (hy₀ i)
    rw [hinfS, ← inf_assoc]
    linarith

/-- **Every finite meet is bounded below, for an arbitrary index type.** No
finiteness of `ι`, and no continuity. -/
theorem prod_le_inf_of (hΓ : IsDependencyGraphOn R X Γ)
    (hy₀ : ∀ i, 0 ≤ y i) (hy₁ : ∀ i, y i < 1)
    (hX : ∀ i, 1 - y i * ∏ j ∈ Γ i, (1 - y j) ≤ R (X i)) (S : Finset ι) :
    (∏ j ∈ S, (1 - y j)) ≤ R (S.inf X) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [R.map_top]
  | @insert j D'' hj ihD =>
    have hkey := key_mul_of R hΓ hy₀ hy₁ hX D''.card D'' j le_rfl hj
    have hy1' : 0 < 1 - y j := by linarith [hy₁ j]
    rw [Finset.prod_insert hj, Finset.inf_insert]
    calc (1 - y j) * ∏ k ∈ D'', (1 - y k)
        ≤ (1 - y j) * R (D''.inf X) := mul_le_mul_of_nonneg_left ihD hy1'.le
      _ ≤ R (X j ⊓ D''.inf X) := hkey

end QLLL

namespace QLLL

open Finset

variable {α : Type*} [CompleteLattice α] (R : Valuation α)
variable {ι : Type*} {X : ι → α} {Γ : ι → Finset ι} {y : ι → ℝ}

end QLLL


section

open QLLL
open Finset
variable {α : Type*} [CompleteLattice α] (R : Valuation α)
variable {ι : Type*} {X : ι → α} {Γ : ι → Finset ι} {y : ι → ℝ}

theorem solution (hΓ : IsDependencyGraphOn R X Γ)
    (hy₀ : ∀ i, 0 ≤ y i) (hy₁ : ∀ i, y i < 1)
    (hX : ∀ i, 1 - y i * ∏ j ∈ Γ i, (1 - y j) ≤ R (X i))
    (c : ℝ) (hc : ∀ S : Finset ι, c ≤ ∏ j ∈ S, (1 - y j))
    (hcont : ∀ b : ℝ, (∀ S : Finset ι, b ≤ R (S.inf X)) → b ≤ R (⨅ i, X i)) :
    c ≤ R (⨅ i, X i) :=
  hcont c fun S => le_trans (hc S) (prod_le_inf_of R hΓ hy₀ hy₁ hX S)

end
