-- Prove2me | solution 1 for WeierstrassEllipticZeta.auxiliary_grid_quotient_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T14:43:02.983129+00:00
-- url     : https://prove2.me/submissions/5721dce9-31af-4e38-b91b-576a5d4f865f

import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section
open scoped Pointwise

open WeierstrassEllipticZeta

private lemma p2m_grid_quotient_card (Λ : Submodule ℤ ℂ) (ω u₁ u₂ : ℂ)
    (hcong : ∀ m n : Fin 3 → ℤ,
      integerGridPoint u₁ u₂ ω m - integerGridPoint u₁ u₂ ω n ∈ Λ ↔
        m 0 = n 0 ∧ m 1 = n 1)
    (A : Fin 3 → ℕ) (hA : 0 < A 2) :
    (Λ.mkQ '' (auxiliaryGrid u₁ u₂ ω A : Set ℂ)).ncard = A 0 * A 1 := by
  classical
  let f : Fin (A 0) × Fin (A 1) → ℂ ⧸ Λ := fun m =>
    Λ.mkQ (integerGridPoint u₁ u₂ ω ![(m.1 : ℕ), (m.2 : ℕ), 0])
  have hf : Function.Injective f := by
    intro m n h
    have hlat := (Submodule.Quotient.eq Λ).mp h
    have heq := (hcong _ _).mp hlat
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at heq
    apply Prod.ext
    · apply Fin.ext
      exact_mod_cast heq.1
    · apply Fin.ext
      exact_mod_cast heq.2
  have himage : Λ.mkQ '' (auxiliaryGrid u₁ u₂ ω A : Set ℂ) = Set.range f := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hz
      refine ⟨(m 0, m 1), ?_⟩
      apply (Submodule.Quotient.eq Λ).mpr
      exact (hcong _ _).mpr ⟨rfl, rfl⟩
    · rintro ⟨m, rfl⟩
      refine ⟨integerGridPoint u₁ u₂ ω ![(m.1 : ℕ), (m.2 : ℕ), 0], ?_, rfl⟩
      let v : (i : Fin 3) → Fin (A i) := fun i =>
        ⟨![(m.1 : ℕ), (m.2 : ℕ), 0] i, by
          fin_cases i
          · exact m.1.isLt
          · exact m.2.isLt
          · exact hA⟩
      change _ ∈ Finset.univ.image _
      refine Finset.mem_image.mpr ⟨v, Finset.mem_univ _, ?_⟩
      congr 1
      funext i
      fin_cases i <;> rfl
  rw [himage, Set.ncard_range_of_injective hf]
  simp

theorem solution
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (A : Fin 3 → ℕ) (hA : ∀ i, 1 ≤ A i) :
    0 ∈ auxiliaryGrid u₁ u₂ ω A ∧
    (auxiliaryGrid u₁ u₂ ω A + auxiliaryGrid u₁ u₂ ω A +
      auxiliaryGrid u₁ u₂ ω A ⊆ auxiliaryGrid u₁ u₂ ω (fun i => 3 * A i)) ∧
    (auxiliaryGrid u₁ u₂ ω A).card = A 0 * A 1 * A 2 ∧
    (L.lattice.mkQ '' (auxiliaryGrid u₁ u₂ ω A : Set ℂ)).ncard = A 0 * A 1 := by
  classical
  refine ⟨?_, ?_, ?_, p2m_grid_quotient_card L.lattice ω u₁ u₂ h_grid.congruent_iff A (hA 2)⟩
  · let m : (i : Fin 3) → Fin (A i) := fun i => ⟨0, hA i⟩
    change 0 ∈ Finset.univ.image _
    refine Finset.mem_image.mpr ⟨m, Finset.mem_univ _, ?_⟩
    simp [integerGridPoint, m]
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨v, hv, w, hw, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hy
    let d : (i : Fin 3) → Fin (3 * A i) := fun i =>
      ⟨(a i : ℕ) + (b i : ℕ) + (c i : ℕ), by
        have ha := (a i).isLt
        have hb := (b i).isLt
        have hc := (c i).isLt
        omega⟩
    change _ ∈ Finset.univ.image _
    refine Finset.mem_image.mpr ⟨d, Finset.mem_univ _, ?_⟩
    dsimp [integerGridPoint, d]
    push_cast
    ring
  · rw [h_grid.card_grid]
    simp [Fin.prod_univ_succ, mul_assoc]

