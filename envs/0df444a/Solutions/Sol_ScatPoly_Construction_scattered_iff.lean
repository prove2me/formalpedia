-- Prove2me | solution 1 for ScatPoly.Construction.scattered_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:12:13.344631+00:00
-- url     : https://prove2.me/submissions/a2017722-31cc-427f-a34c-420c0570dfa6

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model
import Definitions.Def_ScatPoly_Construction_Model

open ScatPoly.Construction ScatCaps.LinearSets in
theorem solution (F : Type*) [Field F] [Fintype F] (p r n q : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 0 < r) (hq : q = p ^ r) (hcard : Fintype.card F = q ^ n) (c : ℕ → F) :
    (IsScattered (subfieldOf F p r 1) ⊤ (graph (qpoly q n c)) ↔
        IsScatteredPoly (subfieldOf F p r 1) (qpoly q n c)) ∧
    (IsScatteredPoly (subfieldOf F p r 1) (qpoly q n c) ↔
        ∀ x γ : F, x ≠ 0 → qpoly q n c (γ * x) = γ * qpoly q n c x →
          γ ∈ subfieldOf F p r 1) := by
  set f := qpoly q n c with hf
  set Fq := subfieldOf F p r 1 with hFq
  have hq0 : q ≠ 0 := by
    rw [hq]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hf0 : f 0 = 0 := by
    rw [hf]; unfold qpoly
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [zero_pow (pow_ne_zero _ hq0), mul_zero]
  -- equivalence of IsScatteredPoly with the γ-form
  have h2 : IsScatteredPoly Fq f ↔
      ∀ x γ : F, x ≠ 0 → f (γ * x) = γ * f x → γ ∈ Fq := by
    constructor
    · intro hS x γ hx hγ
      by_cases hγ0 : γ = 0
      · rw [hγ0]; exact Fq.zero_mem
      · have hz : γ * x ≠ 0 := mul_ne_zero hγ0 hx
        have hrat : f (γ * x) / (γ * x) = f x / x := by
          rw [hγ, mul_div_mul_left _ _ hγ0]
        obtain ⟨c', hc', hzc⟩ := hS (γ * x) x hz hx hrat
        have : γ = c' := mul_right_cancel₀ hx hzc
        rw [this]; exact hc'
    · intro hC z y hz hy hrat
      refine ⟨z / y, ?_, by field_simp⟩
      apply hC y (z / y) hy
      have e : z / y * y = z := by field_simp
      rw [e]
      have : f z = f z / z * z := by field_simp
      rw [this, hrat]
      field_simp
  -- equivalence of IsScattered on the graph with the γ-form
  have h1 : IsScattered Fq ⊤ (graph f) ↔
      ∀ x γ : F, x ≠ 0 → f (γ * x) = γ * f x → γ ∈ Fq := by
    constructor
    · intro hS x γ hx hγ
      have hu : (![x, f x] : Fin 2 → F) ∈ graph f := ⟨x, rfl⟩
      have hu0 : (![x, f x] : Fin 2 → F) ≠ 0 := by
        intro h
        have := congrFun h 0
        simp at this
        exact hx this
      have hmem : ((((⟨γ, Subfield.mem_top γ⟩ : (⊤ : Subfield F))) : F) • (![x, f x] : Fin 2 → F))
          ∈ graph f := by
        refine ⟨γ * x, ?_⟩
        ext i
        fin_cases i
        · simp
        · simp [hγ]
      exact hS _ hu hu0 ⟨γ, Subfield.mem_top γ⟩ hmem
    · rintro hC u ⟨x, rfl⟩ hu0 cc ⟨x', hx'⟩
      have hx : x ≠ 0 := by
        rintro rfl
        apply hu0
        ext i
        fin_cases i <;> simp [hf0]
      have e0 := congrFun hx' 0
      have e1 := congrFun hx' 1
      simp at e0 e1
      apply hC x (cc : F) hx
      rw [e0, e1]
  exact ⟨h1.trans h2.symm, h2⟩
