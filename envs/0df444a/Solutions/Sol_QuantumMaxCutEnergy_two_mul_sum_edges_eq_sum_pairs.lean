-- Prove2me | solution 1 for QuantumMaxCutEnergy.two_mul_sum_edges_eq_sum_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T02:35:49.437317+00:00
-- url     : https://prove2.me/submissions/17fe4b45-9081-47b0-836b-ca85d7233b24

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutMatchingPadding
import Mathlib

set_option autoImplicit false
open scoped BigOperators

open QuantumMaxCutEnergy

/-- A symmetric, diagonal-free function on ordered pairs sums to twice its edge sum. -/
theorem solution {n : ℕ} (g : Fin n → Fin n → ℝ)
    (hcomm : ∀ a b, g a b = g b a) (hdiag : ∀ a, g a a = 0) :
    2 * (∑ e : Edge n, g e.val.1 e.val.2) = ∑ a, ∑ b, g a b := by
  classical
  set f : Fin n × Fin n → ℝ := fun p => g p.1 p.2 with hf
  set U : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 < p.2) with hU
  set L : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.2 < p.1) with hL
  have hprod : ∑ a, ∑ b, g a b = ∑ p : Fin n × Fin n, f p := by
    rw [hf, ← Finset.univ_product_univ, Finset.sum_product]
  rw [hprod]
  -- the diagonal contributes nothing
  have hdiag0 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2), f p = 0 := by
    refine Finset.sum_eq_zero (fun p hp => ?_)
    have h : p.1 = p.2 := (Finset.mem_filter.mp hp).2
    simp [hf, h, hdiag]
  have hnd : ∑ p : Fin n × Fin n, f p
      = ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2), f p := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin n × Fin n)))
      (p := fun p : Fin n × Fin n => p.1 = p.2) (f := f), hdiag0, zero_add]
  rw [hnd]
  -- the off-diagonal part is the disjoint union of the two triangles
  have hunion : Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2) = U ∪ L := by
    ext p
    simp only [hU, hL, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    omega
  have hdisj : Disjoint U L := by
    rw [hU, hL, Finset.disjoint_filter]
    intro p _ h1 h2
    omega
  rw [hunion, Finset.sum_union hdisj]
  -- the two triangles agree by symmetry
  have hsym : ∑ p ∈ L, f p = ∑ p ∈ U, f p := by
    have hLimg : L = U.image (fun p : Fin n × Fin n => (p.2, p.1)) := by
      ext q
      simp only [hU, hL, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hlt
        exact ⟨(q.2, q.1), hlt, rfl⟩
      · rintro ⟨p, hp, heq⟩
        rw [← heq]
        exact hp
    have hinj : Set.InjOn (fun p : Fin n × Fin n => (p.2, p.1)) ↑U := by
      intro p _ q _ hpq
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext hpq.2 hpq.1
    rw [hLimg, Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun p _ => by simp only [hf]; exact (hcomm p.1 p.2).symm)
  rw [hsym]
  -- the upper triangle is the edge sum
  have hedge : ∑ p ∈ U, f p = ∑ e : Edge n, g e.val.1 e.val.2 := by
    refine Finset.sum_bij (s := U) (t := (Finset.univ : Finset (Edge n)))
      (f := f) (g := fun e : Edge n => g e.val.1 e.val.2)
      (fun p (hp : p ∈ U) => (⟨p, ?_⟩ : Edge n)) ?_ ?_ ?_ ?_
    · rw [hU] at hp
      exact (Finset.mem_filter.mp hp).2
    · intro p _; exact Finset.mem_univ _
    · intro p1 _ p2 _ heq; exact Subtype.ext_iff.mp heq
    · intro e _
      refine ⟨e.val, ?_, ?_⟩
      · rw [hU, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, e.property⟩
      · exact Subtype.ext rfl
    · intro p _
      rfl
  rw [hedge]
  ring


#print axioms solution
