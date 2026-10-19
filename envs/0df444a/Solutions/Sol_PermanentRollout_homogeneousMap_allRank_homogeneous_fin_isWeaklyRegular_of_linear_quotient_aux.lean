-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_homogeneous_fin_isWeaklyRegular_of_linear_quotient_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/32e1a9b1-e5a0-49b4-a6b2-45587b3fa9c0

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_fin_hyperplane_isSMulRegular_of_quotient_weaklyRegular_aux
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_homogeneous_isSMulRegular_of_linear_hyperplane_aux
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_isSMulRegular_sup_of_quotient_map_aux

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} {e : ℕ}
    (ell : MvPolynomial ι ℂ)
    (hell : ell ≠ 0)
    (hellhom : ell.IsHomogeneous 1) :
    ∀ (n : ℕ) (f : Fin n → MvPolynomial ι ℂ),
      (∀ i, (f i).IsHomogeneous e) →
      RingTheory.Sequence.IsWeaklyRegular
        (MvPolynomial ι ℂ ⧸
          Ideal.span ({ell} : Set (MvPolynomial ι ℂ)))
        (List.ofFn fun i =>
          Ideal.Quotient.mk
            (Ideal.span ({ell} : Set (MvPolynomial ι ℂ))) (f i)) →
      RingTheory.Sequence.IsWeaklyRegular
        (MvPolynomial ι ℂ) (List.ofFn f) := by
  classical
  intro n
  induction n with
  | zero =>
      intro f _ _
      exact RingTheory.Sequence.IsWeaklyRegular.nil _ _
  | succ n ih =>
      intro f hf hregular
      let R := MvPolynomial ι ℂ
      let J : Ideal R := Ideal.span ({ell} : Set R)
      let q : R →+* R ⧸ J := Ideal.Quotient.mk J
      let fp : Fin n → R := fun i => f i.castSucc
      let g : R := f (Fin.last n)
      let I : Ideal R := Ideal.span (Set.range fp)
      have hlist :
          List.ofFn (fun i : Fin (n + 1) => q (f i)) =
            (List.ofFn fun i : Fin n => q (fp i)) ++ [q g] :=
        List.ofFn_succ_last
      have hsplit :=
        (RingTheory.Sequence.isWeaklyRegular_append_iff
          (R ⧸ J) (List.ofFn fun i : Fin n => q (fp i)) [q g]).mp
          (hlist ▸ hregular)
      have hprefix : RingTheory.Sequence.IsWeaklyRegular
          (R ⧸ J) (List.ofFn fun i : Fin n => q (fp i)) := hsplit.1
      have hsourceprefix : RingTheory.Sequence.IsWeaklyRegular
          R (List.ofFn fp) :=
        ih fp (fun i => hf i.castSucc) hprefix
      have himage :
          Ideal.ofList (List.ofFn fun i : Fin n => q (fp i)) =
            I.map q := by
        change Ideal.span {x : R ⧸ J |
          x ∈ List.ofFn (fun i : Fin n => q (fp i))} =
          (Ideal.span (Set.range fp)).map q
        rw [Ideal.map_span]
        congr 1
        ext x
        simp
      have hquotientlast : IsSMulRegular
          ((R ⧸ J) ⧸ I.map q) (q g) := by
        have hlast :=
          (RingTheory.Sequence.isWeaklyRegular_singleton_iff
            ((R ⧸ J) ⧸
              (Ideal.ofList
                (List.ofFn fun i : Fin n => q (fp i)) •
                  (⊤ : Submodule (R ⧸ J) (R ⧸ J))))
            (q g)).mp hsplit.2
        have hsub :
            Ideal.ofList (List.ofFn fun i : Fin n => q (fp i)) •
                (⊤ : Submodule (R ⧸ J) (R ⧸ J)) =
              (I.map q : Submodule (R ⧸ J) (R ⧸ J)) := by
          simp [himage]
        let E := Submodule.quotEquivOfEq _ _ hsub
        exact (E.isSMulRegular_congr (q g)).mp hlast
      have hgmod : IsSMulRegular (R ⧸ (I ⊔ J)) g :=
        homogeneousMap_allRank_isSMulRegular_sup_of_quotient_map_aux
          I J g hquotientlast
      have hI : I.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule ι ℂ) := by
        apply Ideal.homogeneous_span
        rintro _ ⟨i, rfl⟩
        exact ⟨e, hf i.castSucc⟩
      have hellI : IsSMulRegular (R ⧸ I) ell :=
        homogeneousMap_allRank_fin_hyperplane_isSMulRegular_of_quotient_weaklyRegular_aux
          fp ell hell hprefix
      have hgI : IsSMulRegular (R ⧸ I) g :=
        homogeneousMap_allRank_homogeneous_isSMulRegular_of_linear_hyperplane_aux
          I hI g ell (hf (Fin.last n)) hellhom hellI hgmod
      rw [List.ofFn_succ_last]
      apply (RingTheory.Sequence.isWeaklyRegular_append_iff
        R (List.ofFn fp) [g]).mpr
      refine ⟨hsourceprefix, ?_⟩
      rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      have hspan : Ideal.ofList (List.ofFn fp) = I := by
        change Ideal.span {x : R | x ∈ List.ofFn fp} =
          Ideal.span (Set.range fp)
        congr 1
        ext x
        simp
      have hsub :
          Ideal.ofList (List.ofFn fp) •
              (⊤ : Submodule R R) =
            (I : Submodule R R) := by
        simp [hspan]
      let E := Submodule.quotEquivOfEq _ _ hsub
      exact (E.isSMulRegular_congr g).mpr hgI
end PermanentRollout
