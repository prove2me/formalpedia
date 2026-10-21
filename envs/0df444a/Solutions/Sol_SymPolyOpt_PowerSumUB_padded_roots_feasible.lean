-- Prove2me | solution 1 for SymPolyOpt.PowerSumUB.padded_roots_feasible
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:14:28.193618+00:00
-- url     : https://prove2.me/submissions/f336d4fd-76f3-406a-a958-afa05f09deb9

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumUB_Setting

set_option autoImplicit false
open Polynomial SymPolyOpt.PowerSumUB

theorem solution (n m q : ℕ) (γ : ℕ → ℝ) (hmn : m ≤ n) (p : ℝ[X])
    (hp : p ∈ feasU m γ) (hreal : ∀ z ∈ p.aroots ℂ, z.im = 0) (hq : 1 ≤ q) :
    ∃ x ∈ SymPolyOpt.PowerSumLB.feasP n m γ, SymPolyOpt.PowerSumLB.powerSum x q = newtonSum p q := by
  obtain ⟨hmonic, hdeg, hγ, _⟩ := hp
  set R : Multiset ℂ := p.aroots ℂ with hR
  have hcard : Multiset.card R = m := by
    rw [hR, Polynomial.aroots_def, IsAlgClosed.card_roots_eq_natDegree, natDegree_map, hdeg]
  set M : Multiset ℝ := R.map Complex.re with hM
  have hMcard : Multiset.card M = m := by rw [hM, Multiset.card_map, hcard]
  have hRM : R = M.map (fun r : ℝ => (r : ℂ)) := by
    rw [hM, Multiset.map_map]
    conv_lhs => rw [← Multiset.map_id R]
    refine Multiset.map_congr rfl fun z hz => ?_
    exact (Complex.ext (by simp) (by simp [hreal z hz])).symm
  have hc : ∀ (j : ℕ) (N : Multiset ℝ), (N.map (fun r : ℝ => ((r : ℂ) ^ j))).sum
      = (((N.map (fun r => r ^ j)).sum : ℝ) : ℂ) := by
    intro j N
    induction N using Multiset.induction_on with
    | empty => simp
    | cons a N ih => simp [ih]
  have hpow : ∀ j, newtonSum p j = (M.map (fun r => r ^ j)).sum := by
    intro j
    have h1 : newtonSum p j = ((R.map (· ^ j)).sum).re := rfl
    rw [h1, hRM, Multiset.map_map]
    have : (M.map ((fun z : ℂ => z ^ j) ∘ (fun r : ℝ => (r : ℂ)))) = M.map (fun r : ℝ => ((r : ℂ) ^ j)) := rfl
    rw [this, hc]
    simp
  set L : List ℝ := M.toList ++ List.replicate (n - m) 0 with hL
  have hlen : L.length = n := by simp [hL, hMcard]; omega
  obtain ⟨x, hx⟩ : ∃ x : Fin n → ℝ, ∀ f : ℝ → ℝ, ∑ i, f (x i) = (L.map f).sum := by
    refine ⟨fun i => L.get ⟨i, by rw [hlen]; exact i.2⟩, fun f => ?_⟩
    have h1 : List.ofFn (fun i : Fin n => L.get ⟨i, by rw [hlen]; exact i.2⟩) = L := by
      apply List.ext_getElem <;> simp [hlen]
    rw [← List.sum_ofFn]
    have : List.ofFn (fun i : Fin n => f (L.get ⟨i, by rw [hlen]; exact i.2⟩))
        = L.map f := by
      apply List.ext_getElem <;> simp [hlen]
    rw [this]
  have hps : ∀ j, 1 ≤ j → SymPolyOpt.PowerSumLB.powerSum x j = newtonSum p j := by
    intro j hj
    rw [hpow]
    unfold SymPolyOpt.PowerSumLB.powerSum
    rw [hx (fun r => r ^ j), hL, List.map_append, List.sum_append]
    have h2 : (List.map (fun r : ℝ => r ^ j) (List.replicate (n - m) 0)).sum = 0 := by
      simp [List.map_replicate, List.sum_replicate, zero_pow (by omega : j ≠ 0)]
    rw [h2, add_zero]
    conv_rhs => rw [← Multiset.coe_toList M]
    simp [Multiset.map_coe]
  refine ⟨x, fun j h1 h2 => ?_, hps q hq⟩
  rw [hps j h1]
  exact hγ j h1 h2
