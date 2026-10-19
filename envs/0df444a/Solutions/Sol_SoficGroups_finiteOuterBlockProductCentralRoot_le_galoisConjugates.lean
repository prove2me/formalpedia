-- Prove2me | solution 1 for SoficGroups.finiteOuterBlockProductCentralRoot_le_galoisConjugates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/1d4eda5a-d931-419d-b3fd-2733ced43e3a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finiteOuterElementaryRoot_conjugate_by_successor
import Theorems.Thm_SoficGroups_finiteBlockCoefficientMatrixHom_galoisRightInverse
import Theorems.Thm_SoficGroups_finiteBlockGalois_right_inverse_difference

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (W : Submodule (ZMod 2) R)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W)
    (s t : finiteBlockGaloisField) (hst : s ≠ t) :
    finiteOuterBlockProductCentralRootSubgroup W i k hik B ≤
      finiteOuterBlockGaloisConjugateRootWithCoefficient
          W i j k hij hjk B s ⊔
        finiteOuterBlockGaloisConjugateRootWithCoefficient
          W i j k hij hjk B t := by
  intro z hz
  obtain ⟨A, rfl⟩ := hz
  let D : Matrix (Fin 3) (Fin 3) W :=
    finiteBlockGaloisRightInverseCoefficientMatrix W A.toAdd s t
  let x : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R) :=
    finiteOuterBlockRootHom W i j hij (Multiplicative.ofAdd D)
  let ys : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R) :=
    finiteOuterBlockGaloisConjugatorWithCoefficient W j k hjk B s
  let yt : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R) :=
    finiteOuterBlockGaloisConjugatorWithCoefficient W j k hjk B t
  let J : Subgroup (elementaryGroup (Fin 3)
      (Matrix (Fin 3) (Fin 3) R)) :=
    finiteOuterBlockGaloisConjugateRootWithCoefficient
        W i j k hij hjk B s ⊔
      finiteOuterBlockGaloisConjugateRootWithCoefficient
        W i j k hij hjk B t
  have hx : x ∈ finiteOuterBlockRootSubgroup W i j hij :=
    ⟨Multiplicative.ofAdd D, rfl⟩
  have hs : MulAut.conj ys x ∈
      finiteOuterBlockGaloisConjugateRootWithCoefficient
        W i j k hij hjk B s :=
    ⟨x, hx, rfl⟩
  have ht : MulAut.conj yt x ∈
      finiteOuterBlockGaloisConjugateRootWithCoefficient
        W i j k hij hjk B t :=
    ⟨x, hx, rfl⟩
  have hprod : MulAut.conj ys x * (MulAut.conj yt x)⁻¹ ∈ J :=
    J.mul_mem (Subgroup.mem_sup_left hs)
      (J.inv_mem (Subgroup.mem_sup_right ht))
  let C₀ : Matrix (Fin 3) (Fin 3) R :=
    finiteBlockCoefficientMatrixHom W A.toAdd
  let B₀ : Matrix (Fin 3) (Fin 3) R :=
    finiteBlockCoefficientMatrixHom W B
  let D₀ : Matrix (Fin 3) (Fin 3) R :=
    finiteBlockCoefficientMatrixHom W D
  let P : Matrix (Fin 3) (Fin 3) R :=
    finiteBlockGaloisMatrixOver R s * B₀
  let Q : Matrix (Fin 3) (Fin 3) R :=
    finiteBlockGaloisMatrixOver R t * B₀
  have hD : D₀ = C₀ * finiteBlockGaloisMatrixOver R (t - s)⁻¹ :=
    finiteBlockCoefficientMatrixHom_galoisRightInverse W A.toAdd s t
  have hdiff : - (D₀ * P) + D₀ * Q = C₀ * B₀ := by
    calc
      - (D₀ * P) + D₀ * Q =
          (D₀ * finiteBlockGaloisMatrixOver R t -
            D₀ * finiteBlockGaloisMatrixOver R s) * B₀ := by
        dsimp [P, Q]
        noncomm_ring
      _ = C₀ * B₀ := by
        rw [hD, finiteBlockGalois_right_inverse_difference s t hst C₀]
  have hroot :
      (elementaryRootHom i k hik (Multiplicative.ofAdd (D₀ * P)))⁻¹ *
        elementaryRootHom i k hik (Multiplicative.ofAdd (D₀ * Q)) =
      finiteOuterBlockProductCentralRootHom W i k hik B A := by
    calc
      _ = elementaryRootHom i k hik
          ((Multiplicative.ofAdd (D₀ * P))⁻¹ *
            Multiplicative.ofAdd (D₀ * Q)) := by
        simp only [map_mul, map_inv]
      _ = elementaryRootHom i k hik
          (Multiplicative.ofAdd (C₀ * B₀)) := by
        congr 1
      _ = finiteOuterBlockProductCentralRootHom W i k hik B A := by
        rfl
  change
    MulAut.conj
        (elementaryRootHom j k hjk (Multiplicative.ofAdd P))
        (elementaryRootHom i j hij (Multiplicative.ofAdd D₀)) *
      (MulAut.conj
        (elementaryRootHom j k hjk (Multiplicative.ofAdd Q))
        (elementaryRootHom i j hij (Multiplicative.ofAdd D₀)))⁻¹ ∈ J
    at hprod
  simp only [MulAut.conj_apply] at hprod
  rw [finiteOuterElementaryRoot_conjugate_by_successor
        i j k hij hjk hik D₀ P,
      finiteOuterElementaryRoot_conjugate_by_successor
        i j k hij hjk hik D₀ Q] at hprod
  have hcancel :
      ((elementaryRootHom i k hik (Multiplicative.ofAdd (D₀ * P)))⁻¹ *
        elementaryRootHom i j hij (Multiplicative.ofAdd D₀)) *
        ((elementaryRootHom i k hik (Multiplicative.ofAdd (D₀ * Q)))⁻¹ *
          elementaryRootHom i j hij (Multiplicative.ofAdd D₀))⁻¹ =
      (elementaryRootHom i k hik (Multiplicative.ofAdd (D₀ * P)))⁻¹ *
        elementaryRootHom i k hik (Multiplicative.ofAdd (D₀ * Q)) := by
    group
  rw [hcancel, hroot] at hprod
  exact hprod
end SoficGroups
