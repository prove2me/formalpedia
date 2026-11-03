-- Prove2me | solution 1 for QuantumMaxCutEnergy.matching_balanced_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T01:51:41.768338+00:00
-- url     : https://prove2.me/submissions/5b3b1f32-419a-4622-8cae-54ade8d42739

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Mathlib

set_option autoImplicit false
open scoped BigOperators

/-!
# Balanced split of a load-polytope point — solution

Perturbation step of Edmonds' exactness: the direction `1_B - 1_A` of a locally balanced pair of edge
sets is a circulation, so moving a polytope point along it as far as nonnegativity allows gives the
endpoints of a segment through the point, and the extreme steps make one edge of `A` (resp. `B`)
vanish. Everything is in terms of the published load `QuantumMaxCutEnergy.loadAt`.
-/

namespace QuantumMaxCutEnergy

/-- Loads add under a pointwise sum of edge weights. -/
lemma loadAt_add {n : ℕ} (x d : Edge n → ℝ) (t : ℝ) (v : Fin n) :
    loadAt (fun e => x e + t * d e) v = loadAt x v + t * loadAt d v := by
  unfold loadAt
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun e _ => by
    by_cases h : v = e.val.1 ∨ v = e.val.2 <;> simp [h])

/-- The load of the `0/1` edge weight of a finite set of edges is its degree into that set. -/
lemma loadAt_zero_one {n : ℕ} (B : Finset (Edge n)) (v : Fin n) :
    loadAt (fun e => if e ∈ B then (1 : ℝ) else 0) v
      = ((B.filter (fun e => v = e.val.1 ∨ v = e.val.2)).card : ℝ) := by
  unfold loadAt
  have h : ∀ e : Edge n,
      (if v = e.val.1 ∨ v = e.val.2 then (if e ∈ B then (1 : ℝ) else 0) else 0)
        = (if e ∈ B then (if v = e.val.1 ∨ v = e.val.2 then (1 : ℝ) else 0) else 0) := by
    intro e
    by_cases h1 : v = e.val.1 ∨ v = e.val.2 <;> by_cases h2 : e ∈ B <;> simp [h1, h2]
  simp only [h]
  rw [← Finset.sum_filter]
  have huniv : (Finset.univ.filter (fun e : Edge n => e ∈ B)) = B := by
    ext e; simp
  rw [huniv, Finset.sum_boole]

end QuantumMaxCutEnergy

open QuantumMaxCutEnergy

/-- **Balanced split of a load-polytope point.**

Let `x ≥ 0` be an edge weight with all vertex loads at most `1`, and let `A`, `B` be disjoint
nonempty finite sets of edges that are *locally balanced*: at every vertex, as many edges of `A` as
of `B` are incident. Then `x` is a convex combination of two points `y`, `z` of the load polytope,
each of which has strictly smaller support: `y` vanishes on some edge of `A`, `z` on some edge of
`B`. The two points differ from `x` only on `A ∪ B`.

This is the perturbation step of Edmonds' exactness: the direction `1_B - 1_A` is a circulation (it
leaves every vertex load unchanged), so moving `x` along it as far as nonnegativity allows produces
the endpoints of a segment through `x` inside the polytope. -/
theorem solution {n : ℕ} (x : Edge n → ℝ) (A B : Finset (Edge n))
    (hx : ∀ e, 0 ≤ x e) (hload : ∀ v, loadAt x v ≤ 1)
    (hApos : ∀ e ∈ A, 0 < x e) (hBpos : ∀ e ∈ B, 0 < x e)
    (hA : A.Nonempty) (hB : B.Nonempty) (hdisj : Disjoint A B)
    (hbal : ∀ v : Fin n,
      (A.filter (fun e => v = e.val.1 ∨ v = e.val.2)).card
        = (B.filter (fun e => v = e.val.1 ∨ v = e.val.2)).card) :
    ∃ (y z : Edge n → ℝ) (lam : ℝ),
      (∀ e, 0 ≤ y e) ∧ (∀ v, loadAt y v ≤ 1) ∧
      (∀ e, 0 ≤ z e) ∧ (∀ v, loadAt z v ≤ 1) ∧
      0 ≤ lam ∧ lam ≤ 1 ∧
      (∀ e, x e = lam * y e + (1 - lam) * z e) ∧
      (∃ e, x e ≠ 0 ∧ y e = 0) ∧ (∃ e, x e ≠ 0 ∧ z e = 0) := by
  classical
  set d : Edge n → ℝ := fun e => (if e ∈ B then (1 : ℝ) else 0) - (if e ∈ A then (1 : ℝ) else 0) with hddef
  have hdload : ∀ v : Fin n, loadAt d v = 0 := by
    intro v
    have hsub : loadAt d v
        = loadAt (fun e => if e ∈ B then (1 : ℝ) else 0) v
          - loadAt (fun e => if e ∈ A then (1 : ℝ) else 0) v := by
      rw [hddef]
      unfold loadAt
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun e _ => by
        by_cases h : v = e.val.1 ∨ v = e.val.2 <;> simp [h])
    rw [hsub, loadAt_zero_one, loadAt_zero_one, hbal v, sub_self]
  obtain ⟨a₀, ha₀A, ha₀⟩ := Finset.exists_mem_eq_inf' hA x
  obtain ⟨b₀, hb₀B, hb₀⟩ := Finset.exists_mem_eq_inf' hB x
  have halpos : 0 < A.inf' hA x := by rw [ha₀]; exact hApos a₀ ha₀A
  have hbepos : 0 < B.inf' hB x := by rw [hb₀]; exact hBpos b₀ hb₀B
  have hdA : ∀ e ∈ A, d e = -1 := by
    intro e he
    have hne : e ∉ B := Finset.disjoint_left.mp hdisj he
    simp [hddef, he, hne]
  have hdB : ∀ e ∈ B, d e = 1 := by
    intro e he
    have hne : e ∉ A := Finset.disjoint_right.mp hdisj he
    simp [hddef, he, hne]
  have hdle : ∀ e ∈ A, A.inf' hA x ≤ x e := fun e he => Finset.inf'_le x he
  have hble : ∀ e ∈ B, B.inf' hB x ≤ x e := fun e he => Finset.inf'_le x he
  set al := A.inf' hA x with haldef
  set be := B.inf' hB x with hbedef
  have hspos : 0 < al + be := by linarith
  refine ⟨fun e => x e + al * d e, fun e => x e - be * d e, be / (al + be), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- nonnegativity of `y`
    intro e
    change 0 ≤ x e + al * d e
    by_cases heA : e ∈ A
    · have hde : d e = -1 := hdA e heA
      have hle : al ≤ x e := hdle e heA
      rw [hde]
      nlinarith
    · by_cases heB : e ∈ B
      · have hd1 : d e = 1 := hdB e heB
        rw [hd1]
        nlinarith [hx e, le_of_lt halpos]
      · have hd0 : d e = 0 := by simp [hddef, heA, heB]
        rw [hd0]
        simpa using hx e
  · -- loads of `y`
    intro v
    have hy : (fun e => x e + al * d e) = fun e => x e + al * d e := rfl
    rw [loadAt_add, hdload v, mul_zero, add_zero]
    exact hload v
  · -- nonnegativity of `z`
    intro e
    change 0 ≤ x e - be * d e
    by_cases heB : e ∈ B
    · have hde : d e = 1 := hdB e heB
      have hle : be ≤ x e := hble e heB
      rw [hde]
      nlinarith
    · by_cases heA : e ∈ A
      · have hd1 : d e = -1 := hdA e heA
        rw [hd1]
        nlinarith [hx e, le_of_lt hbepos]
      · have hd0 : d e = 0 := by simp [hddef, heA, heB]
        rw [hd0]
        simpa using hx e
  · -- loads of `z`
    intro v
    have hz : loadAt (fun e => x e - be * d e) v = loadAt x v - be * loadAt d v := by
      unfold loadAt
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun e _ => by
        by_cases h : v = e.val.1 ∨ v = e.val.2 <;> simp [h])
    rw [hz, hdload v, mul_zero, sub_zero]
    exact hload v
  · -- `0 ≤ lam`
    positivity
  · -- `lam ≤ 1`
    rw [div_le_one hspos]
    linarith
  · -- the convex combination identity
    intro e
    have hde : d e = (if e ∈ B then (1:ℝ) else 0) - (if e ∈ A then (1:ℝ) else 0) := rfl
    field_simp
    ring
  · -- `y` vanishes at the minimiser over `A`
    refine ⟨a₀, ?_, ?_⟩
    · rw [← ha₀]; exact ne_of_gt halpos
    · change x a₀ + al * d a₀ = 0
      have hd1 : d a₀ = -1 := hdA a₀ ha₀A
      rw [hd1, ha₀]
      ring
  · -- `z` vanishes at the minimiser over `B`
    refine ⟨b₀, ?_, ?_⟩
    · rw [← hb₀]; exact ne_of_gt hbepos
    · change x b₀ - be * d b₀ = 0
      have hd1 : d b₀ = 1 := hdB b₀ hb₀B
      rw [hd1, hb₀]
      ring

#print axioms solution
