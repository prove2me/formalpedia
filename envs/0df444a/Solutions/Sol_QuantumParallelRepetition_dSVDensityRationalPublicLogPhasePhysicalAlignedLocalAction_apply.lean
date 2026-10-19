-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalPublicLogPhasePhysicalAlignedLocalAction_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/5a181c3d-8135-423e-a97d-da729776ef62

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource_apply
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift_apply
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary_apply

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    (B N d L m : ℕ)
    (U V : Matrix.unitaryGroup
      (DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L) ℂ)
    (φ ψ : Fin B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) (i j : Fin m) :
    localUnitaryAction
      (dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
        B N d L m
        (dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
          B U))
      (dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
        B N d L m
        (dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
          B V))
      (dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
        B N d L m)
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
          B N d L m ((φ, a), i),
       dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
          B N d L m ((ψ, b), j)) =
      (if φ = ψ then
        (((Real.sqrt (B : ℝ))⁻¹ : ℝ) : ℂ)
      else 0) *
      (∑ x : DSVUniformDensityThresholdWholeHistoryLocalIndex
          N d L,
        ∑ y : DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L,
          (U : Matrix
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L)
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L) ℂ) a x *
          (V : Matrix
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L)
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L) ℂ) b y *
          dSVUniformDensityThresholdWholeHistorySharedState
            N d L (x, y)) *
      embezzlementState m (i, j) := by
  classical
  let H := DSVUniformDensityThresholdWholeHistoryLocalIndex
    N d L
  let P := DSVDensityRationalPublicLogPhaseHistoryLocalIndex
    B N d L
  let n := dSVDensityRationalPublicLogPhaseResidual B N d L m
  let e := dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
    B N d L m
  let A := dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
    B N d L m
    (dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
      B U)
  let D := dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
    B N d L m
    (dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
      B V)
  let source := dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
    B N d L m
  have left (χ : Fin B) (x : H) (k : Fin m) :
      (A : Matrix (Fin (d * n)) (Fin (d * n)) ℂ)
        (e ((φ, a), i)) (e ((χ, x), k)) =
        if i = k then
          if φ = χ then (U : Matrix H H ℂ) a x else 0
        else 0 := by
    rw [dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift_apply,
      dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary_apply]
  have right (χ : Fin B) (x : H) (k : Fin m) :
      (D : Matrix (Fin (d * n)) (Fin (d * n)) ℂ)
        (e ((ψ, b), j)) (e ((χ, x), k)) =
        if j = k then
          if ψ = χ then (V : Matrix H H ℂ) b x else 0
        else 0 := by
    rw [dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift_apply,
      dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary_apply]
  have resource (χ υ : Fin B) (x y : H) (k l : Fin m) :
      source (e ((χ, x), k), e ((υ, y), l)) =
        (if χ = υ then
          (((Real.sqrt (B : ℝ))⁻¹ : ℝ) : ℂ)
        else 0) *
          dSVUniformDensityThresholdWholeHistorySharedState
            N d L (x, y) *
          embezzlementState m (k, l) :=
    dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource_apply
      B N d L m χ υ x y k l
  change
    (∑ q : Fin (d * n) × Fin (d * n),
      ((A : Matrix (Fin (d * n)) (Fin (d * n)) ℂ) ⊗ₖ
        (D : Matrix (Fin (d * n)) (Fin (d * n)) ℂ))
          (e ((φ, a), i), e ((ψ, b), j)) q * source q) = _
  calc
    _ =
      ∑ q : (P × Fin m) × (P × Fin m),
        ((A : Matrix (Fin (d * n)) (Fin (d * n)) ℂ) ⊗ₖ
          (D : Matrix (Fin (d * n)) (Fin (d * n)) ℂ))
          (e ((φ, a), i), e ((ψ, b), j)) (e q.1, e q.2) *
          source (e q.1, e q.2) :=
      (Equiv.sum_comp (Equiv.prodCongr e e)
        (fun q : Fin (d * n) × Fin (d * n) =>
          ((A : Matrix (Fin (d * n)) (Fin (d * n)) ℂ) ⊗ₖ
            (D : Matrix (Fin (d * n)) (Fin (d * n)) ℂ))
            (e ((φ, a), i), e ((ψ, b), j)) q *
            source q)).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply]
      dsimp only [P, DSVDensityRationalPublicLogPhaseHistoryLocalIndex]
      simp only [Fintype.sum_prod_type]
      change
        (∑ χ : Fin B,
          ∑ x : H,
            ∑ k : Fin m,
              ∑ υ : Fin B,
                ∑ y : H,
                  ∑ l : Fin m,
                    (A : Matrix (Fin (d * n)) (Fin (d * n)) ℂ)
                        (e ((φ, a), i)) (e ((χ, x), k)) *
                      (D : Matrix (Fin (d * n)) (Fin (d * n)) ℂ)
                        (e ((ψ, b), j)) (e ((υ, y), l)) *
                      source (e ((χ, x), k), e ((υ, y), l))) = _
      simp_rw [left, right, resource]
      simp [mul_ite, ite_mul, mul_assoc, Finset.sum_mul]
      split_ifs
      · simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      · rfl
end QuantumParallelRepetition
