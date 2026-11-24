-- Prove2me | solution 1 for SensitivityWeightedCliqueCertificate.coloring_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:21:28.694812+00:00
-- url     : https://prove2.me/submissions/79dbccb0-b2f1-406f-b86b-eaaa9d031f63

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_CliqueCertificate
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_WeightedCliqueCertificate
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Nat.Bitwise

namespace SensitivityCliqueCertificate
end SensitivityCliqueCertificate
namespace SensitivityWeightedCliqueCertificate
end SensitivityWeightedCliqueCertificate

section


/-! The same explicit branch/coloring proof objects with nonnegative vertex weights. -/
namespace SensitivityWeightedCliqueCertificate

open scoped BigOperators
open SensitivityCliqueCertificate
set_option autoImplicit false



theorem weight_le_classFee (weight : ℕ → ℕ) (group : List ℕ) (v : ℕ) (hv : v ∈ group) :
    weight v ≤ classFee weight group := by
  induction group with
  | nil => simp at hv
  | cons a rest ih =>
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Nat.le_max_left _ _
    · exact (ih hv).trans (Nat.le_max_right _ _)













end SensitivityWeightedCliqueCertificate

end

/-! The same explicit branch/coloring proof objects with nonnegative vertex weights. -/
open SensitivityWeightedCliqueCertificate
open scoped BigOperators
open SensitivityCliqueCertificate
set_option autoImplicit false

theorem solution (adj weight : ℕ → ℕ) (classes : List (List ℕ))
    (hgood : ∀ group ∈ classes, independentCheck adj group = true)
    (vertices : Finset ℕ) (hclique : Clique adj vertices)
    (hcover : ∀ v ∈ vertices, v ∈ classes.flatten) :
    (∑ v ∈ vertices, weight v) ≤ (classes.map (classFee weight)).sum := by
  induction classes generalizing vertices with
  | nil =>
    have hempty : vertices = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      simpa using hcover v hv
    simp [hempty]
  | cons group rest ih =>
    let inside := vertices.filter (fun v => v ∈ group)
    let outside := vertices.filter (fun v => v ∉ group)
    have hinside : inside.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro v hv w hw
      have hvm := Finset.mem_filter.mp hv
      have hwm := Finset.mem_filter.mp hw
      by_contra hne
      have hfalse := independentCheck_sound (hgood group List.mem_cons_self) hvm.2 hwm.2
      have htrue := hclique v hvm.1 w hwm.1 hne
      rw [hfalse] at htrue
      contradiction
    have hin : (∑ v ∈ inside, weight v) ≤ classFee weight group := by
      have hs := Finset.sum_le_sum (fun v (hv : v ∈ inside) =>
        weight_le_classFee weight group v (Finset.mem_filter.mp hv).2)
      have hs' : (∑ v ∈ inside, weight v) ≤ inside.card * classFee weight group := by simpa using hs
      have hm := Nat.mul_le_mul_right (classFee weight group) hinside
      exact hs'.trans (by simpa using hm)
    have hout : (∑ v ∈ outside, weight v) ≤ (rest.map (classFee weight)).sum := by
      apply ih
      · intro next hn
        exact hgood next (List.mem_cons_of_mem _ hn)
      · intro v hv w hw hne
        exact hclique v (Finset.mem_filter.mp hv).1 w (Finset.mem_filter.mp hw).1 hne
      · intro v hv
        obtain ⟨hv, hn⟩ := Finset.mem_filter.mp hv
        have hh := hcover v hv
        simp only [List.flatten_cons, List.mem_append] at hh
        exact hh.resolve_left hn
    have hsum : (∑ v ∈ inside, weight v) + (∑ v ∈ outside, weight v) = ∑ v ∈ vertices, weight v :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    simp only [List.map_cons, List.sum_cons]
    omega
