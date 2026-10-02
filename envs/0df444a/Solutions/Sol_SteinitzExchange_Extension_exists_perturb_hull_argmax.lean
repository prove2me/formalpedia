-- Prove2me | solution 1 for SteinitzExchange.Extension.exists_perturb_hull_argmax
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T17:38:55.350079+00:00
-- url     : https://prove2.me/submissions/f3a900c7-d281-42e0-98c9-71f9b8ee4a86

import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Algebra.BigOperators.Field
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange

/- BUNDLE COMPONENT: FarkasPort -/

/-
Ported from https://github.com/jmoy/farkas_lean
Copyright 2026 Jyotirmoy Bhattacharya

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the “Software”), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-/

universe u v
set_option autoImplicit false

/- Original module: AlgebraHelpers -/

open Matrix

namespace FarkasLemma

lemma mulVec_lastCases_split
    {m : Type*} {F : Type*} [Semiring F] {n : ℕ}
    (A : Matrix m (Fin (n + 1)) F)
    (xₙ : F)
    (x' : Fin n → F)
    (i : m) :
    A.mulVec (Fin.lastCases xₙ x') i
      = (A.submatrix id Fin.castSucc i ⬝ᵥ x') + A i (Fin.last n) * xₙ := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

lemma dotProduct_mul_right
  {F : Type*} [CommSemiring F] {n : ℕ}
    (a x : Fin n → F)
    (c : F) :
    ((fun j : Fin n => a j * c) ⬝ᵥ x) = (a ⬝ᵥ x) * c := by
  calc
    ((fun j : Fin n => a j * c) ⬝ᵥ x)
        = ∑ j : Fin n, (a j * c) * x j := by simp [dotProduct]
    _ = ∑ j : Fin n, (a j * x j) * c := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (∑ j : Fin n, a j * x j) * c := by
          rw [← Finset.sum_mul]
    _ = (a ⬝ᵥ x) * c := by simp [dotProduct]

lemma dotProduct_scaled_inv_mul
    {F : Type*} [Field F] {n : ℕ}
    (a x : Fin n → F)
    (c : F)
    (hc : c ≠ 0) :
    ((fun j : Fin n => a j * c⁻¹) ⬝ᵥ x) * c = a ⬝ᵥ x := by
  calc
    ((fun j : Fin n => a j * c⁻¹) ⬝ᵥ x) * c
        = ((a ⬝ᵥ x) * c⁻¹) * c := by
            rw [dotProduct_mul_right]
    _ = a ⬝ᵥ x := by
          field_simp [hc]

lemma dotProduct_mul_inv
  {F : Type*} [Field F] {n : ℕ}
    (a x : Fin n → F)
    (c : F) :
    ((fun j : Fin n => a j * c⁻¹) ⬝ᵥ x) = (a ⬝ᵥ x) * c⁻¹ := by
  simpa using dotProduct_mul_right a x c⁻¹

lemma split_add_mul_inv
    {F : Type*} [Field F]
    (u x c : F)
    (hc : c ≠ 0) :
    ((u + c * x) * c⁻¹) = u * c⁻¹ + x := by
  calc
    ((u + c * x) * c⁻¹)
        = u * c⁻¹ + (c * x) * c⁻¹ := by ring
    _ = u * c⁻¹ + x := by
          have hx : (c * x) * c⁻¹ = x := by
            calc
              (c * x) * c⁻¹ = x * (c * c⁻¹) := by ring
              _ = x := by simp [mul_inv_cancel₀ hc]
          simp [hx]

lemma mul_inv_cancel_right
    {F : Type*} [Field F]
    (a c : F)
    (hc : c ≠ 0) :
    (a * c⁻¹) * c = a := by
  calc
    (a * c⁻¹) * c = a * (c⁻¹ * c) := by ring
    _ = a := by simp [inv_mul_cancel₀ hc]

lemma upper_bound_from_linear_pos
  {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (u x b c : F)
    (hc : 0 < c)
    (hlin : u + c * x ≤ b) :
    x + u * c⁻¹ ≤ b * c⁻¹ := by
  have hscaled : (u + c * x) * c⁻¹ ≤ b * c⁻¹ :=
    mul_le_mul_of_nonneg_right hlin (inv_nonneg.mpr (le_of_lt hc))
  calc
    x + u * c⁻¹ = u * c⁻¹ + x := by ring
    _ = (u + c * x) * c⁻¹ := by
          symm
          exact split_add_mul_inv u x c (ne_of_gt hc)
    _ ≤ b * c⁻¹ := hscaled

lemma lower_bound_from_linear_neg
  {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (u x b c : F)
    (hc : c < 0)
    (hlin : u + c * x ≤ b) :
    b * c⁻¹ ≤ x + u * c⁻¹ := by
  have hscaled : b * c⁻¹ ≤ (u + c * x) * c⁻¹ :=
    mul_le_mul_of_nonpos_right hlin (inv_nonpos.mpr (le_of_lt hc))
  calc
    b * c⁻¹ ≤ (u + c * x) * c⁻¹ := hscaled
    _ = u * c⁻¹ + x := split_add_mul_inv u x c (ne_of_lt hc)
    _ = x + u * c⁻¹ := by ring

end FarkasLemma

/- Original module: FourierMotzkin -/

namespace FarkasLemma

-- A helper lemma first

-- Given finite index sets of lower and upper bounds in a lattice, if every lower bound
-- is below every upper bound, then there exists an element lying between all lowers
-- and all uppers.
--
-- If one side is empty, the witness is chosen from the nonempty side via `sup'`/`inf'`;
-- if both are empty, a witness is provided by `h_nonempty`.
private lemma finite_bounds_witness
    {ι : Type*} [Finite ι]
    {κ : Type*} [Finite κ]
    {F : Type*} [Lattice F]
    (h_nonempty : Nonempty F)
    (lhss : ι → F)
    (rhss : κ → F)
    (h : ∀ i j, lhss i ≤ rhss j) :
    ∃ x : F, ((∀ i, lhss i ≤ x) ∧ (∀ j, x ≤ rhss j)) := by
  haveI:= Fintype.ofFinite ι
  haveI:= Fintype.ofFinite κ
  by_cases hi: Nonempty ι
  · -- lhss is nonempty, use sup over it
    exact ⟨ Finset.univ.sup' Finset.univ_nonempty lhss,
            fun i => Finset.univ.le_sup' lhss (Finset.mem_univ i),
            fun j => Finset.sup'_le _ _ (fun i _ => h i j) ⟩
  · by_cases hj: Nonempty κ
    · -- rhss is nonempty, use inf over it
      exact ⟨ Finset.univ.inf' Finset.univ_nonempty rhss,
              fun i => False.elim (hi ⟨i⟩),
              fun j => Finset.univ.inf'_le _ (Finset.mem_univ j) ⟩
    · -- both are empty, any element will do
      obtain ⟨x⟩ := h_nonempty
      exact ⟨x,fun i => False.elim (hi ⟨i⟩),
               fun j => False.elim (hj ⟨j⟩)⟩

/--
`Fourier_Motzkin` performs one-step Fourier–Motzkin elimination on the last variable
of a finite linear system `A.mulVec x ≤ b`.

It constructs a finite index type `κ` and a nonnegative matrix `M` such that:
* the last column is eliminated: `(M * A) i (Fin.last n) = 0`,
* feasibility is preserved and reflected:
  the original system in `n+1` variables is feasible iff the projected system
  `(M * (A.submatrix id Fin.castSucc)).mulVec x' ≤ M.mulVec b` is feasible in `n` variables.

This is the standard elimination step used in proofs of Farkas-type results.
-/
theorem Fourier_Motzkin
  {m : Type u}
  {F : Type v}
  [Fintype m]
  [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  {n : ℕ}
  (A : Matrix m (Fin (n + 1)) F)
  (b : m → F) :
  ∃ κ : Type u, ∃ _ : Fintype κ, ∃ M : Matrix κ m F,
      (∀ i j, 0 ≤ M i j) ∧
      (∀ i, (M * A) i (Fin.last n) = 0) ∧
      ((∃ x : Fin (n + 1) → F, A.mulVec x ≤ b) ↔
        ∃ x' : Fin n → F,
          (M * (A.submatrix id Fin.castSucc)).mulVec x' ≤ M.mulVec b) := by
  /-

  ----------------------------------------------
  PART 1. Definitions and setup.
  ----------------------------------------------

  -/
  -- For notational convenience split A into last column and other columns
  let Aₙ : m → F := fun i => A i (Fin.last n)
  let A₀ : Matrix m (Fin n) F := A.submatrix id Fin.castSucc
  -- Partition rows by the sign of the eliminated variable coefficient.
  let posRow : Finset m := Finset.univ.filter (fun i => 0 < Aₙ i)
  let negRow : Finset m := Finset.univ.filter (fun i => Aₙ i < 0)
  let zeroRow : Finset m := Finset.univ.filter (fun i => Aₙ i = 0)
  -- New row index type after elimination:
  -- * `inl (iPos, iNeg)` for combined inequalities from positive/negative rows,
  -- * `inr iZero` for rows already independent of the eliminated variable.
  let κ : Type _ := ((↥posRow × ↥negRow) ⊕ ↥zeroRow)
  -- Normalized coefficient/bound functions used to isolate `xₙ`.
  let posCoeffs : posRow -> Fin n -> F := fun i j => A₀ i j * (Aₙ i)⁻¹
  let posb : posRow -> F := fun i => b i * (Aₙ i)⁻¹
  let negCoeffs : negRow -> Fin n -> F := fun i j => A₀ i j * (Aₙ i)⁻¹
  let negb : negRow -> F := fun i => b i * (Aₙ i)⁻¹
  let zeroCoeffs : zeroRow -> Fin n -> F := fun i j => A₀ i j
  let zerob : zeroRow -> F := fun i => b i
  -- Eliminated system `(A', b')` in `n` variables.
  let A' : Matrix κ (Fin n) F := fun i j => match i with
    | Sum.inl (iPos, iNeg) => posCoeffs iPos j - negCoeffs iNeg j
    | Sum.inr iZero => zeroCoeffs iZero j
  let b' : κ -> F := fun i => match i with
    | Sum.inl (iPos, iNeg) => posb iPos - negb iNeg
    | Sum.inr iZero => zerob iZero
  /-

  ----------------------------------------------
  PART 2. Forward direction.
  ----------------------------------------------
  Every solution of the original system projects to
  a solution of the eliminated system.


  -/
  have hlft: ∀ x : Fin (n + 1) → F,
        A.mulVec x ≤ b → ∃ x' : Fin n → F, A'.mulVec x' ≤ b' := by
    intro x hx
    -- Just dropping the last coordinate is going to be enough
    -- But the value of the last coordinate will have work to do.
    let x' : Fin n → F := fun j => x (Fin.castSucc j)
    let xₙ := x (Fin.last n)
    use x'
    intro i
    match i with
    | Sum.inl (iPos, iNeg) =>
      -- We have to satisfy a combined inequality arising from a positive
      -- and a negative row.
      -- Strategy: use the eliminated coordinate `xₙ` itself as a witness.
      -- From the positive row we derive an upper bound on `xₙ`, and from the
      -- negative row a lower bound on `xₙ`; combining these yields the reduced
      -- inequality for the `(iPos, iNeg)` row.
      --
      -- Now the real work begins. We will use xₙ to chain two inequalities
      -- Derive the upper-bound inequality for xₙ from the positive row.
      have h₁ : xₙ ≤ posb iPos - (posCoeffs iPos) ⬝ᵥ x' := by
        have hpos : 0 < Aₙ iPos := (Finset.mem_filter.mp iPos.property).2
        have hrow_pos := hx iPos
        have hpos_ne : Aₙ iPos ≠ 0 := ne_of_gt hpos
        have hlin_pos :
            (A₀ iPos ⬝ᵥ x') + Aₙ iPos * xₙ ≤ b iPos := by
          simpa [Matrix.mulVec, dotProduct, x', xₙ, Aₙ, Fin.sum_univ_castSucc,
            add_assoc, add_left_comm, add_comm, A₀] using hrow_pos
        have hdot_pos :
            (posCoeffs iPos) ⬝ᵥ x' = (A₀ iPos ⬝ᵥ x') * (Aₙ iPos)⁻¹ := by
          simpa [posCoeffs] using dotProduct_mul_inv (A₀ iPos) x' (Aₙ iPos)
        have hbound_pos : xₙ + (posCoeffs iPos) ⬝ᵥ x' ≤ posb iPos := by
          calc
            xₙ + (posCoeffs iPos) ⬝ᵥ x'
                = xₙ + (A₀ iPos ⬝ᵥ x') * (Aₙ iPos)⁻¹ := by rw [hdot_pos]
            _ ≤ b iPos * (Aₙ iPos)⁻¹ :=
              upper_bound_from_linear_pos
                (A₀ iPos ⬝ᵥ x') xₙ (b iPos) (Aₙ iPos) hpos hlin_pos
            _ = posb iPos := by simp [posb]
        simpa [le_sub_iff_add_le] using hbound_pos
      -- Derive the lower-bound inequality for xₙ from the negative row.
      have h₂ : negb iNeg - (negCoeffs iNeg) ⬝ᵥ x' ≤ xₙ := by
        have hneg : Aₙ iNeg < 0 := (Finset.mem_filter.mp iNeg.property).2
        have hrow_neg := hx iNeg
        have hneg_ne : Aₙ iNeg ≠ 0 := ne_of_lt hneg
        have hlin_neg :
            (A₀ iNeg ⬝ᵥ x') + Aₙ iNeg * xₙ ≤ b iNeg := by
          simpa [Matrix.mulVec, dotProduct, x', xₙ, Aₙ, Fin.sum_univ_castSucc,
            add_assoc, add_left_comm, add_comm, A₀] using hrow_neg
        have hdot_neg :
            (negCoeffs iNeg) ⬝ᵥ x' = (A₀ iNeg ⬝ᵥ x') * (Aₙ iNeg)⁻¹ := by
          simpa [negCoeffs] using dotProduct_mul_inv (A₀ iNeg) x' (Aₙ iNeg)
        have hbound_neg : negb iNeg ≤ xₙ + (negCoeffs iNeg) ⬝ᵥ x' := by
          calc
            negb iNeg = b iNeg * (Aₙ iNeg)⁻¹ := by simp [negb]
            _ ≤ xₙ + (A₀ iNeg ⬝ᵥ x') * (Aₙ iNeg)⁻¹ :=
              lower_bound_from_linear_neg
                (A₀ iNeg ⬝ᵥ x') xₙ (b iNeg) (Aₙ iNeg) hneg hlin_neg
            _ = xₙ + (negCoeffs iNeg) ⬝ᵥ x' := by rw [hdot_neg]
        simpa [sub_le_iff_le_add] using hbound_neg
      -- Combine the upper and lower bounds to get the eliminated inequality.
      have h_combined : (posCoeffs iPos) ⬝ᵥ x' - negCoeffs iNeg ⬝ᵥ x'
                          ≤ posb iPos - negb iNeg := by
        linarith [h₁, h₂]
      simpa [A', b', Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib] using h_combined
    --
    | Sum.inr iZero =>
      -- A zero row is easy, the reduced inequality is the same as the original
      simp only [A', b', Matrix.mulVec,zeroCoeffs, zerob]
      have hzero : Aₙ iZero = 0 := (Finset.mem_filter.mp iZero.property).2
      have hzero' : A iZero (Fin.last n) = 0 := by simpa [Aₙ] using hzero
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hzero', A₀, x'] using hx iZero
  /-

  ----------------------------------------------
  PART 3. Backward direction.
  ----------------------------------------------

  From an eliminated solution, reconstruct a witness
  for the eliminated coordinate and then lift back to the original system.



  -/
  have hright : ∀ x' : Fin n → F,
        A'.mulVec x' ≤ b' → ∃ x : Fin (n + 1) → F, A.mulVec x ≤ b := by
    intro x' hsol
    -- Candidate lower/upper bounds for the eliminated variable.
    let valpos : posRow → F := fun i => posb i - (posCoeffs i) ⬝ᵥ x'
    let valneg : negRow → F := fun i => negb i - (negCoeffs i) ⬝ᵥ x'
    -- Pairwise compatibility of lower and upper bounds follows from `hsol`.
    have hbounds : ∀ iNeg iPos, valneg iNeg ≤ valpos iPos := by
      intro iNeg iPos
      have := hsol (Sum.inl (iPos, iNeg))
      dsimp [A', b'] at this
      have hlin :
          (posCoeffs iPos) ⬝ᵥ x' - (negCoeffs iNeg) ⬝ᵥ x' ≤ posb iPos - negb iNeg := by
        simpa [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib] using this
      have hbound :
          negb iNeg - (negCoeffs iNeg) ⬝ᵥ x' ≤
        posb iPos - (posCoeffs iPos) ⬝ᵥ x' := by
        linarith [hlin]
      simpa [valpos, valneg] using hbound
    -- Choose `xₙ` between all lower and upper bounds.
    obtain ⟨xₙ, h_xₙn, h_xₙp⟩ := finite_bounds_witness ⟨0⟩ valneg valpos hbounds
    -- Reassemble the full vector from `xₙ` and `x'`.
    let x : Fin (n + 1) → F := Fin.lastCases xₙ x'
    -- We need to show that this will work
    refine ⟨x, fun i => ?_⟩
    by_cases hlast : Aₙ i = 0
    -- The zero row is the easy case
    · let iZero : zeroRow := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlast⟩⟩
      have hlast' : A i (Fin.last n) = 0 := by simpa [Aₙ] using hlast
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hlast', x, A', b', zeroCoeffs, zerob,
        A₀, iZero]
        using hsol (Sum.inr iZero)
    · cases lt_or_gt_of_ne hlast with
      | inl hneg =>
      -- Negative row
        let iNeg : negRow := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hneg⟩⟩
        have hiNeg : (iNeg : m) = i := rfl
        have h := h_xₙn iNeg
        dsimp [valneg] at h
        rw [sub_le_iff_le_add] at h
        rw [add_comm] at h
        have h_scaled := mul_le_mul_of_nonpos_right h (le_of_lt hneg)
        have h_scaled' : (xₙ + (negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg ≤ negb iNeg * Aₙ iNeg := by
          simpa [hiNeg, add_comm] using h_scaled
        have hdot_neg : A₀ i ⬝ᵥ x' = ((negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg := by
          calc
            A₀ i ⬝ᵥ x' = A₀ iNeg ⬝ᵥ x' := by simp [hiNeg]
            _ = ((fun j : Fin n => A₀ iNeg j * (Aₙ iNeg)⁻¹) ⬝ᵥ x') * Aₙ iNeg := by
                  symm
                  exact dotProduct_scaled_inv_mul (A₀ iNeg) x' (Aₙ iNeg) (ne_of_lt hneg)
            _ = ((negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg := by rfl
        calc
          A.mulVec x i
              = (A₀ i ⬝ᵥ x') + Aₙ i * xₙ := by
                  simpa [x, A₀, Aₙ] using mulVec_lastCases_split A xₙ x' i
          _ = ((negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg + xₙ * Aₙ iNeg := by
                rw [hdot_neg]
                simp [Aₙ, hiNeg, mul_comm]
          _ = (xₙ + (negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg := by ring
          _ ≤ negb iNeg * Aₙ iNeg := h_scaled'
          _ = b i := by
                calc
                  negb iNeg * Aₙ iNeg
                      = (b iNeg * (Aₙ iNeg)⁻¹) * Aₙ iNeg := by simp [negb]
                  _ = b iNeg := by
                    simpa using mul_inv_cancel_right (b iNeg) (Aₙ iNeg) (ne_of_lt hneg)
                  _ = b i := by simp [hiNeg]
      | inr hpos =>
      -- Positive row
        let iPos : posRow := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpos⟩⟩
        have hiPos : (iPos : m) = i := rfl
        have h := h_xₙp iPos
        dsimp [valpos] at h
        rw [le_sub_iff_add_le, add_comm] at h
        have h_scaled := mul_le_mul_of_nonneg_right h (le_of_lt hpos)
        have h_scaled' : ((posCoeffs iPos) ⬝ᵥ x' + xₙ) * Aₙ iPos ≤ posb iPos * Aₙ iPos := by
          simpa [hiPos] using h_scaled
        have hdot_pos : A₀ i ⬝ᵥ x' = ((posCoeffs iPos) ⬝ᵥ x') * Aₙ iPos := by
          calc
            A₀ i ⬝ᵥ x' = A₀ iPos ⬝ᵥ x' := by simp [hiPos]
            _ = ((fun j : Fin n => A₀ iPos j * (Aₙ iPos)⁻¹) ⬝ᵥ x') * Aₙ iPos := by
                  symm
                  exact dotProduct_scaled_inv_mul (A₀ iPos) x' (Aₙ iPos) hpos.ne'
            _ = ((posCoeffs iPos) ⬝ᵥ x') * Aₙ iPos := by rfl
        calc
          A.mulVec x i
              = (A₀ i ⬝ᵥ x') + Aₙ i * xₙ := by
                  simpa [x, A₀, Aₙ] using mulVec_lastCases_split A xₙ x' i
          _ = ((posCoeffs iPos) ⬝ᵥ x') * Aₙ iPos + xₙ * Aₙ iPos := by
                rw [hdot_pos]
                simp [Aₙ, hiPos, mul_comm]
          _ = ((posCoeffs iPos) ⬝ᵥ x' + xₙ) * Aₙ iPos := by ring
          _ ≤ posb iPos * Aₙ iPos := h_scaled'
          _ = b i := by
                calc
                  posb iPos * Aₙ iPos
                      = (b iPos * (Aₙ iPos)⁻¹) * Aₙ iPos := by simp [posb]
                  _ = b iPos := by
                    simpa using mul_inv_cancel_right (b iPos) (Aₙ iPos) hpos.ne'
                  _ = b i := by simp [hiPos]
  /-

  ----------------------------------------------
  PART 4. Assembling the products
  ----------------------------------------------

  The difficult mathematical work has been done.
  Now we have to assemble the products into the form required by
  the statement of the theorem.

  -/
  classical
  -- Build a nonnegative combination matrix `M` realizing the elimination:
  -- rows for `(iPos,iNeg)` combine one positive and one negative row,
  -- zero rows are copied.
  let M : Matrix κ m F := fun i j =>
    match i with
    | Sum.inl (iPos, iNeg) =>
      (if (j : m) = (iPos : m) then (Aₙ iPos)⁻¹ else 0) +
      (if (j : m) = (iNeg : m) then -(Aₙ iNeg)⁻¹ else 0)
    | Sum.inr iZero =>
        if (j : m) = (iZero : m) then 1 else 0
  -- Identify abstract eliminated data `(A', b')` with matrix expressions via `M`.
  have hA'_eq : A' = M * A₀ := by
    ext i j
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos, iNeg⟩
      rw [Matrix.mul_apply]
      simp [A', M, posCoeffs, negCoeffs, A₀, add_mul, Finset.sum_add_distrib]
      ring
    | inr iZero =>
      rw [Matrix.mul_apply]
      simp [A', M, zeroCoeffs, A₀]
  have hb'_eq : b' = M.mulVec b := by
    ext i
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos, iNeg⟩
      rw [Matrix.mulVec, dotProduct]
      simp [b', M, posb, negb, add_mul, Finset.sum_add_distrib]
      ring
    | inr iZero =>
      rw [Matrix.mulVec, dotProduct]
      simp [b', M, zerob]
  -- `M` is entrywise nonnegative.
  have hM_nonneg : ∀ i j, 0 ≤ M i j := by
    intro i j
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos, iNeg⟩
      refine add_nonneg ?_ ?_
      · by_cases h : (j : m) = (iPos : m)
        · simpa [M, h] using inv_nonneg.mpr (le_of_lt (Finset.mem_filter.mp iPos.property).2)
        · simp [h]
      · by_cases h : (j : m) = (iNeg : m)
        · simpa [M, h]
            using neg_nonneg.mpr (inv_nonpos.mpr (le_of_lt (Finset.mem_filter.mp iNeg.property).2))
        · simp [h]
    | inr iZero =>
      by_cases h0 : (j : m) = (iZero : m)
      · simp [M, h0]
      · simp [M, h0]
  -- Multiplying by `M` eliminates the last column exactly.
  have hM_last_zero : ∀ i, (M * A) i (Fin.last n) = 0 := by
    intro i
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos, iNeg⟩
      have hposnz : Aₙ iPos ≠ 0 := ne_of_gt (Finset.mem_filter.mp iPos.property).2
      have hnegnz : Aₙ iNeg ≠ 0 := ne_of_lt (Finset.mem_filter.mp iNeg.property).2
      rw [Matrix.mul_apply]
      simp [M, Aₙ, hposnz, hnegnz, add_mul, Finset.sum_add_distrib]
    | inr iZero =>
      rw [Matrix.mul_apply]
      simp [M, Aₙ, (Finset.mem_filter.mp iZero.property).2]
  -- Main equivalence rewritten in terms of `M`.
  have h_equiv_M :
      (∃ x : Fin (n + 1) → F, A.mulVec x ≤ b) ↔
        ∃ x' : Fin n → F,
          (M * A₀).mulVec x' ≤ M.mulVec b := by
    constructor
    · rintro ⟨x, hx⟩
      rcases hlft x hx with ⟨x', hElim⟩
      refine ⟨x', ?_⟩
      simpa only [hA'_eq, hb'_eq] using hElim
    · rintro ⟨x', hxElim⟩
      have hA'ineq : A'.mulVec x' ≤ b' := by
        simpa only [hA'_eq, hb'_eq] using hxElim
      exact hright x' hA'ineq
  -- Package all existential witnesses and side conditions.
  exact ⟨κ, inferInstance, M, hM_nonneg, hM_last_zero, by simpa [A₀] using h_equiv_M⟩
end FarkasLemma

/- Original module: Farkas1 -/

open Matrix
/-
A theorem of the alternative.

Either Ax <= b has a solution, or
y >=0, y'A = 0, y'b < 0 has a solution.

We prove it using our Fourier-Motzkin elimination theorem.
-/

namespace FarkasLemma

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {m : Type*} [Fintype m]

/-!
## Definitions using Matrix Operations
A is an m × n matrix.
`A.mulVec x` is matrix-vector multiplication (Ax).
`vecMul y A` is vector-matrix multiplication (y^T A).
-/

def Farkas1Primal {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  ∃ x : Fin n → F, A.mulVec x ≤  b

def Farkas1Dual {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  ∃ y : m → F, (∀ j, 0 ≤ y j) ∧ (y ᵥ* A = 0) ∧ (y ⬝ᵥ b < 0)

/-!
## Mutual Exclusivity
Matrix associativity makes this trivial compared to manual sums.
-/

theorem Farkas1Exclusive {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
  ¬(Farkas1Primal A b ∧ Farkas1Dual A b) := by
  rintro ⟨⟨x, hAx⟩, ⟨y, hy, hyA, hyb⟩⟩
  have hyb_nonneg : 0 ≤ y ⬝ᵥ b := by
    have hdot_le : y ⬝ᵥ (A *ᵥ x) ≤ y ⬝ᵥ b := by
      simpa using dotProduct_le_dotProduct_of_nonneg_left hAx hy
    have hdot_eq : y ⬝ᵥ (A *ᵥ x) = 0 := by
      calc
        y ⬝ᵥ (A *ᵥ x) = (y ᵥ* A) ⬝ᵥ x := by
          simpa using Matrix.dotProduct_mulVec y A x
        _ = 0 := by simp [hyA]
    have hzero : 0 ≤ y ⬝ᵥ (A *ᵥ x) := by
      simp [hdot_eq]
    exact le_trans hzero hdot_le
  linarith

private theorem liftDual_of_fourierMotzkin {κ : Type*} [Fintype κ] {n : ℕ}
    (A : Matrix m (Fin (n + 1)) F) (b : m → F) (M : Matrix κ m F)
    (hM_last : ∀ i, (M * A) i (Fin.last n) = 0)
    (hMt_nonneg : ∀ i j, 0 ≤ (M.transpose) i j)
  (y' : κ → F)
  (hy'_nonneg : ∀ j, 0 ≤ y' j)
  (hy'_Ared : y' ᵥ* (M * (A.submatrix id Fin.castSucc)) = 0)
  (hy'_bred : y' ⬝ᵥ M.mulVec b < 0) :
  let y : m → F := M.transpose.mulVec y'
  (∀ j, 0 ≤ y j) ∧ (y ᵥ* A = 0) ∧ (y ⬝ᵥ b < 0) := by
  have hy_nonneg : ∀ j, 0 ≤ (M.transpose.mulVec y') j := by
    intro j
    simpa [Matrix.mulVec, Matrix.transpose_apply, dotProduct] using
      dotProduct_nonneg_of_nonneg (hMt_nonneg j) hy'_nonneg
  have hy'_Acast : y' ᵥ* ((M * A).submatrix id Fin.castSucc) = 0 := by
    have hAred_eq : M * (A.submatrix id Fin.castSucc) = (M * A).submatrix id Fin.castSucc := by
      simpa using
        (submatrix_mul M A id id Fin.castSucc Function.bijective_id).symm
    simpa [hAred_eq] using hy'_Ared
  have hy'_MA : y' ᵥ* (M * A) = 0 := by
    ext j
    refine Fin.lastCases ?_ ?_ j
    · simp [Matrix.vecMul, dotProduct, hM_last]
    · intro k
      simpa [Matrix.vecMul, dotProduct] using congr_fun hy'_Acast k
  have hyA : (M.transpose.mulVec y') ᵥ* A = 0 := by
    calc
      (M.transpose.mulVec y') ᵥ* A = (y' ᵥ* M) ᵥ* A := by
        rw [Matrix.mulVec_transpose]
      _ = y' ᵥ* (M * A) := by
        rw [Matrix.vecMul_vecMul]
      _ = 0 := hy'_MA
  have hyb : (M.transpose.mulVec y') ⬝ᵥ b < 0 := by
    calc
      (M.transpose.mulVec y') ⬝ᵥ b = (y' ᵥ* M) ⬝ᵥ b := by
        rw [Matrix.mulVec_transpose]
      _ = y' ⬝ᵥ M.mulVec b := by
        symm
        simpa using Matrix.dotProduct_mulVec y' M b
      _ < 0 := hy'_bred
  simpa using
    (show (∀ j, 0 ≤ (M.transpose.mulVec y') j) ∧
        ((M.transpose.mulVec y') ᵥ* A = 0) ∧ ((M.transpose.mulVec y') ⬝ᵥ b < 0) from
      ⟨hy_nonneg, hyA, hyb⟩)

/-!
## Farkas' Lemma
-/

theorem Farkas1Exhaust {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
  Farkas1Primal A b ∨ Farkas1Dual A b := by
  induction n generalizing m b with
  | zero =>
      by_cases hb : 0 ≤ b
      · left
        refine ⟨Fin.elim0, ?_⟩
        simpa [Matrix.mulVec] using hb
      · right
        have hbi : ∃ i : m, b i < 0 := by
          by_contra hbi
          apply hb
          intro i
          by_contra hnonneg
          exact hbi ⟨i, lt_of_not_ge hnonneg⟩
        rcases hbi with ⟨i, hbi⟩
        classical
        let y : m → F := fun j => if j = i then 1 else 0
        refine ⟨y, ?_, ?_, ?_⟩
        · intro j
          by_cases hji : j = i <;> simp [y, hji]
        · ext j
          exact j.elim0
        · have hyb : y ⬝ᵥ b = b i := by
            simp [y, dotProduct]
          rw [hyb]
          exact hbi
  | succ n ih =>
      by_cases hP : Farkas1Primal A b
      · exact Or.inl hP
      · right
        rcases Fourier_Motzkin A b with ⟨κ, _, M, hM_nonneg, hM_last, hFM⟩
        let Ared : Matrix κ (Fin n) F := M * (A.submatrix id Fin.castSucc)
        let bred : κ → F := M.mulVec b
        have hFM' : Farkas1Primal A b ↔ Farkas1Primal (m := κ) Ared bred := by
          simpa [Farkas1Primal, Ared, bred] using hFM
        have hred_noPrimal : ¬ Farkas1Primal (m := κ) Ared bred := by
          intro h
          exact hP (hFM'.2 h)
        have hred_exhaust : Farkas1Primal (m := κ) Ared bred ∨ Farkas1Dual (m := κ) Ared bred :=
          ih (m := κ) (A := Ared) (b := bred)
        have hred_dual : Farkas1Dual (m := κ) Ared bred := by
          cases hred_exhaust with
          | inl h => exact False.elim (hred_noPrimal h)
          | inr h => exact h
        rcases hred_dual with ⟨y', hy'_nonneg, hy'_Ared, hy'_bred⟩
        have hMt_nonneg : ∀ i j, 0 ≤ (M.transpose) i j := by
          intro i j
          simpa [Matrix.transpose_apply] using hM_nonneg j i
        have hdual_lift : Farkas1Dual A b := by
          refine ⟨M.transpose.mulVec y', ?_⟩
          simpa [Ared, bred] using
            (liftDual_of_fourierMotzkin A b M hM_last hMt_nonneg y' hy'_nonneg hy'_Ared hy'_bred)
        exact hdual_lift
end FarkasLemma

/- Original module: Farkas2 -/

/-
Proving Farkas Lemma Based on the theorem of the alternative in
Farkas1.Lean
-/

open Matrix

namespace FarkasLemma2

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {m : Type*} [Fintype m]

/-!
## Definitions using Matrix Operations
A is an m × n matrix.
`A.mulVec x` is matrix-vector multiplication (Ax).
`vecMul y A` is vector-matrix multiplication (y^T A).
-/

def InCone2 {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  ∃ x : Fin n → F, (∀ j, 0 ≤ x j) ∧ A.mulVec x = b

def HasDualCert2 {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  ∃ y : m → F, (∀ j, 0 ≤ (vecMul y A) j) ∧ y ⬝ᵥ b < 0

/-!
## Mutual Exclusivity
Matrix associativity makes this trivial compared to manual sums.
-/

/-!
## Reduction to Farkas1
-/

-- Matrix part of the reduction to `Farkas1`.
def farkas2RedA {n : ℕ} (A : Matrix m (Fin n) F) : Matrix (m ⊕ m ⊕ Fin n) (Fin n) F :=
  fun i j =>
    match i with
    | Sum.inl i₁ => A i₁ j
    | Sum.inr (Sum.inl i₂) => -A i₂ j
    | Sum.inr (Sum.inr k) => if k = j then (-1 : F) else 0

-- RHS part of the reduction to `Farkas1`.
def farkas2Redd {n : ℕ} (b : m → F) : (m ⊕ m ⊕ Fin n) → F :=
  fun i =>
    match i with
    | Sum.inl i₁ => b i₁
    | Sum.inr (Sum.inl i₂) => -b i₂
    | Sum.inr (Sum.inr _) => 0

-- Packed transformed data.
def farkas2_to_farkas1 {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
  Matrix (m ⊕ m ⊕ Fin n) (Fin n) F × ((m ⊕ m ⊕ Fin n) → F) :=
  (farkas2RedA A, farkas2Redd b)

-- Shorthand for the reduced `Farkas1` primal system.
def Farkas2ReducedPrimal {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  FarkasLemma.Farkas1Primal (m := m ⊕ m ⊕ Fin n) (farkas2RedA A) (farkas2Redd b)

-- Shorthand for the reduced `Farkas1` dual system.
def Farkas2ReducedDual {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  FarkasLemma.Farkas1Dual (m := m ⊕ m ⊕ Fin n) (farkas2RedA A) (farkas2Redd b)

/-!
## Mapping lemmas
-/

-- Converts a reduced `Farkas1` primal witness into an `InCone2` witness.
omit [Fintype m] in
lemma farkas1_primal_to_inCone2 {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F)
    (hP : Farkas2ReducedPrimal A b) :
    InCone2 A b := by
  rcases hP with ⟨x, hx_le⟩
  refine ⟨x, ?_, ?_⟩
  · intro j
    have hj := hx_le (Sum.inr (Sum.inr j))
    have hj' : -x j ≤ (0 : F) := by
      simpa [Farkas2ReducedPrimal, farkas2RedA, farkas2Redd, Matrix.mulVec, dotProduct] using hj
    linarith
  · ext i
    have hi₁ := hx_le (Sum.inl i)
    have hi₂ := hx_le (Sum.inr (Sum.inl i))
    have hle : A.mulVec x i ≤ b i := by
      simpa [Farkas2ReducedPrimal, farkas2RedA, farkas2Redd, Matrix.mulVec, dotProduct] using hi₁
    have hge_neg : -(A.mulVec x i) ≤ -b i := by
      simpa [Farkas2ReducedPrimal, farkas2RedA, farkas2Redd, Matrix.mulVec, dotProduct] using hi₂
    have hge : b i ≤ A.mulVec x i := by
      linarith
    exact le_antisymm hle hge

-- Converts a reduced `Farkas1` dual witness into a `HasDualCert2` witness.
lemma farkas1_dual_to_hasDualCert2 {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F)
    (hD : Farkas2ReducedDual A b) :
    HasDualCert2 A b := by
  rcases hD with ⟨w, hw_nonneg, hwC_zero, hwd_neg⟩
  let y₁ : m → F := fun i => w (Sum.inl i)
  let y₂ : m → F := fun i => w (Sum.inr (Sum.inl i))
  let y : m → F := y₁ - y₂
  refine ⟨y, ?_, ?_⟩
  · intro j
    have hcol0 : (w ᵥ* farkas2RedA A) j = 0 := by simpa using congr_fun hwC_zero j
    have hcol : (vecMul y A) j = w (Sum.inr (Sum.inr j)) := by
      have hsplit :
          (w ᵥ* farkas2RedA A) j =
            (vecMul y₁ A) j - (vecMul y₂ A) j - w (Sum.inr (Sum.inr j)) := by
        simp [farkas2RedA, y₁, y₂, Matrix.vecMul, dotProduct]
        ring
      have hy_split : (vecMul y A) j = (vecMul y₁ A) j - (vecMul y₂ A) j := by
        simp [y, Matrix.vecMul, dotProduct, Finset.sum_sub_distrib, sub_mul]
      linarith [hcol0, hsplit, hy_split]
    have hj_nonneg : 0 ≤ w (Sum.inr (Sum.inr j)) := hw_nonneg (Sum.inr (Sum.inr j))
    simpa [hcol] using hj_nonneg
  · have hwd : w ⬝ᵥ farkas2Redd b = y ⬝ᵥ b := by
      calc
        w ⬝ᵥ farkas2Redd b = y₁ ⬝ᵥ b - y₂ ⬝ᵥ b := by
          simp [farkas2Redd, y₁, y₂, dotProduct]
          ring
        _ = y ⬝ᵥ b := by
          simp [y, dotProduct, Finset.sum_sub_distrib, sub_mul]
    rw [hwd] at hwd_neg
    exact hwd_neg

/-!
## Farkas' Lemma
-/

theorem farkas2_exhaustive {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
  InCone2 A b ∨ HasDualCert2 A b := by
  have hAlt : Farkas2ReducedPrimal A b ∨ Farkas2ReducedDual A b :=
    FarkasLemma.Farkas1Exhaust (m := m ⊕ m ⊕ Fin n) (farkas2RedA A) (farkas2Redd b)
  cases hAlt with
  | inl hP =>
      exact Or.inl (farkas1_primal_to_inCone2 A b hP)
  | inr hD =>
      exact Or.inr (farkas1_dual_to_hasDualCert2 A b hD)

theorem farkas2_exclusive {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
  ¬(InCone2 A b ∧ HasDualCert2 A b) := by
  rintro ⟨⟨x, hx_nonneg, rfl⟩, y, hyA_nonneg, hyb_neg⟩
  have h_assoc : y ⬝ᵥ (A.mulVec x) = (vecMul y A) ⬝ᵥ x :=
    dotProduct_mulVec y A x
  have h_nonneg : 0 ≤ (vecMul y A) ⬝ᵥ x :=
    dotProduct_nonneg_of_nonneg hyA_nonneg hx_nonneg
  linarith [h_assoc, h_nonneg, hyb_neg]

theorem farkas2 {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
  InCone2 A b ∨ HasDualCert2 A b :=
  farkas2_exhaustive A b

end FarkasLemma2

#print axioms FarkasLemma.Farkas1Exhaust
#print axioms FarkasLemma2.farkas2_exhaustive

/- BUNDLE COMPONENT: SteinitzSupportingFaceHelpers -/

set_option autoImplicit false

open Finset Set

namespace SteinitzSupportingFace

variable {ι V : Type*} [Fintype ι] [Fintype V]

/-- The barycentric weights representing a fixed point using a finite family. -/
def feasibleWeights (x : ι → V → ℝ) (b : V → ℝ) : Set (ι → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • x i = b}

theorem feasibleWeights_nonempty_of_mem_convexHull (x : ι → V → ℝ) (b : V → ℝ)
    (hb : b ∈ convexHull ℝ (Set.range x)) : (feasibleWeights x b).Nonempty := by
  classical
  have hc : Convex ℝ {b | (feasibleWeights x b).Nonempty} := by
    intro u hu v hv a d ha hd had
    obtain ⟨wu, hwu⟩ := hu
    obtain ⟨wv, hwv⟩ := hv
    refine ⟨fun i => a * wu i + d * wv i,
      fun i => add_nonneg (mul_nonneg ha (hwu.1 i)) (mul_nonneg hd (hwv.1 i)), ?_, ?_⟩
    · rw [sum_add_distrib, ← mul_sum, ← mul_sum, hwu.2.1, hwv.2.1]
      simpa using had
    · simp_rw [add_smul, mul_smul, sum_add_distrib, ← smul_sum]
      rw [hwu.2.2, hwv.2.2]
  apply convexHull_min ?_ hc hb
  rintro _ ⟨i, rfl⟩
  refine ⟨fun j => if j = i then 1 else 0, ?_, ?_, ?_⟩
  · intro j
    dsimp
    split_ifs <;> norm_num
  · simp
  · simp

theorem isClosed_feasibleWeights (x : ι → V → ℝ) (b : V → ℝ) :
    IsClosed (feasibleWeights x b) := by
  have hnonneg : IsClosed {w : ι → ℝ | ∀ i, 0 ≤ w i} := by
    change IsClosed (Set.Ici (0 : ι → ℝ))
    exact isClosed_Ici
  have hsum : IsClosed {w : ι → ℝ | ∑ i, w i = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have hbary : IsClosed {w : ι → ℝ | ∑ i, w i • x i = b} :=
    isClosed_eq (by fun_prop) continuous_const
  exact hnonneg.inter (hsum.inter hbary)

theorem isCompact_feasibleWeights (x : ι → V → ℝ) (b : V → ℝ) :
    IsCompact (feasibleWeights x b) := by
  refine (isCompact_Icc : IsCompact (Icc (0 : ι → ℝ) 1)).of_isClosed_subset
    (isClosed_feasibleWeights x b) ?_
  intro w hw
  refine ⟨hw.1, fun i => ?_⟩
  calc
    w i ≤ ∑ j, w j := single_le_sum (fun j _ => hw.1 j) (mem_univ i)
    _ = 1 := hw.2.1

theorem exists_maximal_weights (x : ι → V → ℝ) (b : V → ℝ) (g : ι → ℝ)
    (hW : (feasibleWeights x b).Nonempty) :
    ∃ w ∈ feasibleWeights x b,
      ∀ z ∈ feasibleWeights x b, (∑ i, z i * g i) ≤ ∑ i, w i * g i := by
  exact (isCompact_feasibleWeights x b).exists_isMaxOn
    (f := fun w : ι → ℝ => ∑ i, w i * g i) hW (by fun_prop)

#print axioms exists_maximal_weights

end SteinitzSupportingFace

/- BUNDLE COMPONENT: SteinitzLiftedSeparation -/

set_option autoImplicit false

open Finset Set Matrix

namespace SteinitzSupportingFace

variable {V : Type*} [Fintype V] {n : ℕ}

/-- A maximal convex combination of finitely many lifted points has a supporting
    functional whose height coefficient is strictly negative, including over
    boundary points of the base convex hull. -/
theorem maximal_weights_separator (x : Fin n → V → ℝ) (b : V → ℝ) (g : Fin n → ℝ)
    (w : Fin n → ℝ) (hw : w ∈ feasibleWeights x b)
    (hmax : ∀ z ∈ feasibleWeights x b, (∑ i, z i * g i) ≤ ∑ i, w i * g i) :
    ∃ y : Option V → ℝ, y none < 0 ∧
      ∀ i, 0 ≤ y none * (g i - ∑ j, w j * g j) +
        ∑ v, y (some v) * (x i v - b v) := by
  classical
  let t : ℝ := ∑ i, w i * g i
  let A : Matrix (Option V) (Fin n) ℝ :=
    fun j i => match j with
      | none => g i - t
      | some v => x i v - b v
  let e : Option V → ℝ := fun j => match j with
    | none => 1
    | some _ => 0
  rcases FarkasLemma2.farkas2_exhaustive A e with hprimal | hdual
  · obtain ⟨a, ha, hae⟩ := hprimal
    have hheight : ∑ i, a i * g i - (∑ i, a i) * t = 1 := by
      have h := congrFun hae none
      simp only [A, e, Matrix.mulVec, dotProduct] at h
      simp_rw [sub_mul] at h
      rw [sum_sub_distrib, ← mul_sum] at h
      simpa only [mul_comm] using h
    have hbase : ∀ v, ∑ i, a i * x i v = (∑ i, a i) * b v := by
      intro v
      have h := congrFun hae (some v)
      have h' : (∑ i, a i * x i v) - (∑ i, a i) * b v = 0 := by
        simp only [A, e, Matrix.mulVec, dotProduct] at h
        simp_rw [sub_mul] at h
        rw [sum_sub_distrib, ← mul_sum] at h
        simpa only [mul_comm] using h
      exact sub_eq_zero.mp h'
    have hsum : 0 < ∑ i, a i := by
      have hnonneg : 0 ≤ ∑ i, a i := sum_nonneg fun i _ => ha i
      by_contra hnot
      have hz : ∑ i, a i = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
      have hall : ∀ i, a i = 0 := fun i =>
        (sum_eq_zero_iff_of_nonneg (fun j _ => ha j)).mp hz i (mem_univ i)
      simp [hall] at hheight
    let z : Fin n → ℝ := fun i => a i / ∑ j, a j
    have hz : z ∈ feasibleWeights x b := by
      refine ⟨fun i => div_nonneg (ha i) hsum.le, ?_, ?_⟩
      · dsimp [z]
        rw [← sum_div, div_self hsum.ne']
      · ext v
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        change (∑ i, (a i / ∑ j, a j) * x i v) = b v
        simp_rw [div_mul_eq_mul_div]
        rw [← sum_div, hbase v, mul_div_cancel_left₀ _ hsum.ne']
    have hzg : ∑ i, z i * g i = t + (∑ i, a i)⁻¹ := by
      dsimp [z]
      simp_rw [div_mul_eq_mul_div]
      rw [← sum_div]
      have hg : ∑ i, a i * g i = 1 + (∑ i, a i) * t := by linarith
      rw [hg, add_div, one_div, mul_div_cancel_left₀ _ hsum.ne']
      ring
    have hm := hmax z hz
    change (∑ i, z i * g i) ≤ t at hm
    rw [hzg] at hm
    exact False.elim ((not_le_of_gt (inv_pos.mpr hsum)) (by linarith))
  · obtain ⟨y, hyA, hye⟩ := hdual
    refine ⟨y, ?_, fun i => ?_⟩
    · simpa [e, dotProduct, Fintype.sum_option] using hye
    · simpa [A, t, Matrix.vecMul, dotProduct, Fintype.sum_option, add_comm] using hyA i

#print axioms maximal_weights_separator

theorem maximal_weights_majorant (x : Fin n → V → ℝ) (b : V → ℝ) (g : Fin n → ℝ)
    (w : Fin n → ℝ) (hw : w ∈ feasibleWeights x b)
    (hmax : ∀ z ∈ feasibleWeights x b, (∑ i, z i * g i) ≤ ∑ i, w i * g i) :
    ∃ p : V → ℝ, ∀ i,
      g i + (∑ v, p v * x i v) ≤ (∑ j, w j * g j) + (∑ v, p v * b v) := by
  obtain ⟨y, hy, hsep⟩ := maximal_weights_separator x b g w hw hmax
  let p : V → ℝ := fun v => y (some v) / y none
  refine ⟨p, fun i => ?_⟩
  have hsum : (∑ v, y (some v) * (x i v - b v)) =
      y none * ((∑ v, p v * x i v) - ∑ v, p v * b v) := by
    simp only [mul_sub, sum_sub_distrib, mul_sum]
    congr 1 <;> apply sum_congr rfl <;> intro v _
    all_goals
      dsimp [p]
      field_simp [hy.ne]
      <;> ring
  have hprod : 0 ≤ y none *
      (g i + (∑ v, p v * x i v) - ((∑ j, w j * g j) + ∑ v, p v * b v)) := by
    have hi := hsep i
    rw [hsum] at hi
    nlinarith [hi]
  exact sub_nonpos.mp (nonpos_of_mul_nonneg_right hprod hy)

#print axioms maximal_weights_majorant

theorem exists_supporting_face (x : Fin n → V → ℝ) (b : V → ℝ) (g : Fin n → ℝ)
    (hW : (feasibleWeights x b).Nonempty) :
    ∃ p : V → ℝ, b ∈ convexHull ℝ
      (x '' {i | ∀ j, g j + (∑ v, p v * x j v) ≤ g i + (∑ v, p v * x i v)}) := by
  classical
  obtain ⟨w, hw, hmax⟩ := exists_maximal_weights x b g hW
  obtain ⟨p, hp⟩ := maximal_weights_majorant x b g w hw hmax
  let q : Fin n → ℝ := fun i => g i + ∑ v, p v * x i v
  let c : ℝ := (∑ i, w i * g i) + ∑ v, p v * b v
  have hq : ∀ i, q i ≤ c := hp
  have hsumq : ∑ i, w i * q i = c := by
    dsimp [q, c]
    simp_rw [mul_add, sum_add_distrib]
    congr 1
    calc
      (∑ i, w i * ∑ v, p v * x i v) = ∑ v, p v * ∑ i, w i * x i v := by
        simp_rw [mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro v _
        apply sum_congr rfl
        intro i _
        ring
      _ = ∑ v, p v * b v := by
        apply sum_congr rfl
        intro v _
        have hb := congrFun hw.2.2 v
        have hb' : (∑ i, w i * x i v) = b v := by simpa using hb
        rw [hb']
  have hslack : ∑ i, w i * (c - q i) = 0 := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib, ← sum_mul, hw.2.1, one_mul, hsumq, sub_self]
  have hsupport : ∀ i, w i ≠ 0 → q i = c := by
    intro i hi
    have hz := (sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hw.1 j) (sub_nonneg.mpr (hq j)))).mp hslack i (mem_univ i)
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hi)).symm
  let s : Finset (Fin n) := univ.filter fun i => w i ≠ 0
  have hsum : ∑ i ∈ s, w i = 1 := by
    calc
      (∑ i ∈ s, w i) = ∑ i, w i := sum_subset (filter_subset _ _)
        (fun i _ hi => by simpa [s] using hi)
      _ = 1 := hw.2.1
  have hbary : ∑ i ∈ s, w i • x i = b := by
    calc
      (∑ i ∈ s, w i • x i) = ∑ i, w i • x i := sum_subset (filter_subset _ _)
        (fun i _ hi => by
          have hz : w i = 0 := by simpa [s] using hi
          simp [hz])
      _ = b := hw.2.2
  refine ⟨p, ?_⟩
  rw [← hbary]
  apply (convex_convexHull ℝ _).sum_mem (fun i _ => hw.1 i) hsum
  intro i hi
  apply subset_convexHull
  refine ⟨i, ?_, rfl⟩
  intro j
  change q j ≤ q i
  rw [hsupport i ((mem_filter.mp hi).2)]
  exact hq j

#print axioms exists_supporting_face

end SteinitzSupportingFace

/- BUNDLE COMPONENT: SteinitzSupportingFaceSolution -/

set_option autoImplicit false

open SteinitzExchange.Extension

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (g : (V → ℤ) → ℝ) (b : V → ℝ)
    (hb : b ∈ hull B) :
    ∃ p : V → ℝ, b ∈ hull (argmaxB B (perturb g p)) := by
  classical
  let e : Fin (Fintype.card (B : Set (V → ℤ))) ≃ (B : Set (V → ℤ)) :=
    (Fintype.equivFin (B : Set (V → ℤ))).symm
  let x : Fin (Fintype.card (B : Set (V → ℤ))) → V → ℝ := fun i => toReal (e i)
  let g' : Fin (Fintype.card (B : Set (V → ℤ))) → ℝ := fun i => g (e i)
  have hrange : Set.range x = toReal '' (B : Set (V → ℤ)) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, (e i).property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨e.symm ⟨z, hz⟩, by simp [x]⟩
  have hbx : b ∈ convexHull ℝ (Set.range x) := by
    rw [hrange]
    exact hb
  have hW := SteinitzSupportingFace.feasibleWeights_nonempty_of_mem_convexHull x b hbx
  obtain ⟨p, hp⟩ := SteinitzSupportingFace.exists_supporting_face x b g' hW
  refine ⟨p, convexHull_mono ?_ hp⟩
  rintro z ⟨i, hi, rfl⟩
  refine ⟨e i, ?_, rfl⟩
  simp only [argmaxB, Finset.mem_coe, Finset.mem_filter]
  refine ⟨(e i).property, ?_⟩
  intro z hz
  have h := hi (e.symm ⟨z, hz⟩)
  simpa [x, g', perturb, pairing] using h

#print axioms solution
