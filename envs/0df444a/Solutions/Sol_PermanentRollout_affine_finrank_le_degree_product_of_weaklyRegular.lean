-- Prove2me | solution 1 for PermanentRollout.affine_finrank_le_degree_product_of_weaklyRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/1a556762-84fa-48fb-9add-98436eb1ba1d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_finiteDimensional_quotient_of_zeroLocus_finite
import Theorems.Thm_PermanentRollout_affine_finrank_le_degree_product_of_regular_prefix

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (f : Fin (Fintype.card ι) → MvPolynomial ι ℂ)
    (hweak : RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial ι ℂ) (List.ofFn f))
    (hfinite :
      (MvPolynomial.zeroLocus ℂ (Ideal.span (Set.range f))).Finite) :
    Module.finrank ℂ
        (MvPolynomial ι ℂ ⧸ Ideal.span (Set.range f)) ≤
      ∏ i, (f i).totalDegree := by
  classical
  let n := Fintype.card ι
  let s : List (MvPolynomial ι ℂ) := List.ofFn f
  let I : ℕ → Ideal (MvPolynomial ι ℂ) :=
    fun j => Ideal.ofList (s.take j)
  let g : ℕ → MvPolynomial ι ℂ :=
    fun j => if h : j < n then f ⟨j, h⟩ else 0
  have hIzero : I 0 = ⊥ := by
    simp [I]
  have hIn : I n = Ideal.span (Set.range f) := by
    change Ideal.ofList ((List.ofFn f).take (Fintype.card ι)) = _
    have htake :
        (List.ofFn f).take (Fintype.card ι) = List.ofFn f := by
      exact List.take_of_length_le (by simp)
    rw [htake]
    change Ideal.span {p : MvPolynomial ι ℂ | p ∈ List.ofFn f} =
      Ideal.span (Set.range f)
    congr 1
    ext p
    simp
  have hInext : ∀ j, j < n →
      I (j + 1) = I j ⊔
        Ideal.span ({g j} : Set (MvPolynomial ι ℂ)) := by
    intro j hj
    dsimp [I]
    rw [List.take_succ_eq_append_getElem
      (show j < s.length by simpa [s, n] using hj)]
    rw [Ideal.ofList_append, Ideal.ofList_singleton]
    simp [s, g, hj]
  have hIregular : ∀ j, j < n →
      IsSMulRegular (MvPolynomial ι ℂ ⧸ I j) (g j) := by
    intro j hj
    have hprev := hweak.regular_mod_prev j
      (show j < (List.ofFn f).length by
        simpa [n] using hj)
    have hsub :
        Ideal.ofList ((List.ofFn f).take j) •
          (⊤ : Submodule (MvPolynomial ι ℂ) (MvPolynomial ι ℂ)) =
            (I j : Submodule (MvPolynomial ι ℂ)
              (MvPolynomial ι ℂ)) := by
      simp [I, s]
    apply ((Submodule.quotEquivOfEq _ _ hsub).isSMulRegular_congr
      (g j)).mp
    simpa [g, hj] using hprev
  letI : Module.Finite ℂ (MvPolynomial ι ℂ ⧸ I n) := by
    rw [hIn]
    exact finiteDimensional_quotient_of_zeroLocus_finite
      (Ideal.span (Set.range f)) hfinite
  have hbound := affine_finrank_le_degree_product_of_regular_prefix
    I g hIzero hInext hIregular
  have hproduct :
      (∏ j ∈ Finset.range n, (g j).totalDegree) =
        ∏ i, (f i).totalDegree := by
    calc
      (∏ j ∈ Finset.range n, (g j).totalDegree) =
          ∏ i : Fin n, (g i).totalDegree :=
        (Fin.prod_univ_eq_prod_range (fun j => (g j).totalDegree) n).symm
      _ = ∏ i : Fin n, (f i).totalDegree := by
        apply Finset.prod_congr rfl
        intro i _
        simp [g, i.isLt]
  rw [hIn, hproduct] at hbound
  exact hbound
end PermanentRollout
