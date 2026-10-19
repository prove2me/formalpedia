-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allTarget_rees_chartCoordinate_isWeaklyRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/9582f919-3a64-4624-8196-1422ea695e19

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentCircuitCompatibility_ofList_take_succ
import Theorems.Thm_PermanentRollout_affine_isSMulRegular_sup_span_swap
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_reesCoordinate_isWeaklyRegular
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_rees_prefix_parameter_sub_isSMulRegular

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (Fin (k + 1)) ℂ ⧸
        homogeneousMapAllTargetReesChartIdeal k (1 : ℂ))
      (List.ofFn fun i : Fin k =>
        Ideal.Quotient.mk
          (homogeneousMapAllTargetReesChartIdeal k (1 : ℂ))
          (homogeneousMapAllTargetReesCoordinate F target e i)) := by
  classical
  let R := MvPolynomial (Fin (k + 1)) ℂ
  let G : Fin k → R := homogeneousMapAllTargetReesCoordinate F target e
  let ell : R :=
    MvPolynomial.X (0 : Fin (k + 1)) - MvPolynomial.C (1 : ℂ)
  let J : Ideal R := Ideal.span ({ell} : Set R)
  let q : R →+* R ⧸ J := Ideal.Quotient.mk J
  have hG := homogeneousMap_allTarget_reesCoordinate_isWeaklyRegular
    F target e he hF hzero
  change RingTheory.Sequence.IsWeaklyRegular (R ⧸ J)
    (List.ofFn fun i : Fin k => q (G i))
  refine ⟨?_⟩
  intro j hjlist
  have hj : j < k := by
    simpa only [List.length_ofFn] using hjlist
  let idx : Fin k := ⟨j, hj⟩
  let I : Ideal R := Ideal.ofList ((List.ofFn G).take j)
  have hgreg : IsSMulRegular (R ⧸ I) (G idx) := by
    have hprev := hG.regular_mod_prev j (by
      simpa only [List.length_ofFn] using hj)
    have hsub :
        Ideal.ofList ((List.ofFn G).take j) •
          (⊤ : Submodule R R) = (I : Submodule R R) := by
      simp [I]
    apply ((Submodule.quotEquivOfEq _ _ hsub).isSMulRegular_congr
      (G idx)).mp
    simpa [idx] using hprev
  have hnext :
      I ⊔ Ideal.span ({G idx} : Set R) =
        Ideal.ofList ((List.ofFn G).take (j + 1)) := by
    change
      Ideal.ofList ((List.ofFn G).take j) ⊔
          Ideal.span ({G ⟨j, hj⟩} : Set R) =
        Ideal.ofList ((List.ofFn G).take (j + 1))
    exact
      PermanentCircuitCompatibility.ofList_take_succ
        G j hj
  have hell : IsSMulRegular
      (R ⧸ (I ⊔ Ideal.span ({G idx} : Set R))) ell := by
    rw [hnext]
    exact homogeneousMap_allTarget_rees_prefix_parameter_sub_isSMulRegular
      F target e he hF hzero (j + 1) (by omega) 1
  have hswap : IsSMulRegular
      (R ⧸ (I ⊔ Ideal.span ({ell} : Set R))) (G idx) :=
    affine_isSMulRegular_sup_span_swap I (G idx) ell hgreg hell
  have himage :
      Ideal.ofList
        ((List.ofFn fun i : Fin k => q (G i)).take j) = I.map q := by
    have hlist :
        (List.ofFn fun i : Fin k => q (G i)).take j =
          ((List.ofFn G).take j).map q := by
      simp [List.map_take, List.map_ofFn, Function.comp_def]
    change
      Ideal.span
        {x : R ⧸ J |
          x ∈ (List.ofFn fun i : Fin k => q (G i)).take j} =
        (Ideal.span {x : R | x ∈ (List.ofFn G).take j}).map q
    rw [hlist, Ideal.map_span]
    congr 1
    ext x
    change
      x ∈ ((List.ofFn G).take j).map q ↔
        ∃ y, y ∈ (List.ofFn G).take j ∧ q y = x
    exact List.mem_map
  have hdouble : IsSMulRegular
      ((R ⧸ J) ⧸ I.map q) (q (G idx)) := by
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem
      (I.map q) (q (G idx))).mpr
    intro p hp
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective p
    have hproduct : G idx * r ∈ I ⊔ J := by
      apply Ideal.mem_quotient_iff_mem_sup.mp
      simpa [smul_eq_mul, map_mul] using hp
    have hr : r ∈ I ⊔ J := by
      apply (isSMulRegular_quotient_iff_mem_of_smul_mem
        (I ⊔ J) (G idx)).mp hswap r
      simpa only [smul_eq_mul] using hproduct
    exact Ideal.mem_quotient_iff_mem_sup.mpr hr
  have hsub :
      Ideal.ofList
          ((List.ofFn fun i : Fin k => q (G i)).take j) •
        (⊤ : Submodule (R ⧸ J) (R ⧸ J)) =
          (I.map q : Submodule (R ⧸ J) (R ⧸ J)) := by
    simp [himage]
  simpa [idx] using
    ((Submodule.quotEquivOfEq _ _ hsub).isSMulRegular_congr
      (q (G idx))).mpr hdouble
end PermanentRollout
