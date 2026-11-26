-- Prove2me | solution 1 for TunnellMap.generatorWitness_with_frame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:21:26.361803+00:00
-- url     : https://prove2.me/submissions/83fffb36-e4c4-45c1-b221-3d5d49893760

import Definitions.Def_TunnellMap_MidpointRecord
import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_QuadraticRoots
import Definitions.Def_TunnellMap_TauLattice
import Definitions.Def_TunnellMap_GeneratorRecovery
import Theorems.Thm_TunnellMap_preferred_half_norm_lt
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_OrthogonalFrame_affine_coset
import Theorems.Thm_TunnellMap_OrthogonalFrame_affine_norm_root_certificate
import Theorems.Thm_TunnellMap_OrthogonalFrame_short_interval_identity
import Theorems.Thm_TunnellMap_assemble_inl
import Theorems.Thm_TunnellMap_assemble_inr
import Theorems.Thm_TunnellMap_directionKey_negTriple
import Theorems.Thm_TunnellMap_directionKey_primitiveDirection
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_minusVector_neg_source
import Theorems.Thm_TunnellMap_minusVector_neg_target
import Theorems.Thm_TunnellMap_odd_third_ne_zero
import Theorems.Thm_TunnellMap_plusVector_neg_source
import Theorems.Thm_TunnellMap_plusVector_neg_target
import Theorems.Thm_TunnellMap_polynomialTriple_neg
import Theorems.Thm_TunnellMap_polynomialTriple_triplePolynomial
import Theorems.Thm_TunnellMap_primitiveDirection_idem
import Theorems.Thm_TunnellMap_primitiveDirection_negTriple
import Theorems.Thm_TunnellMap_primitiveDirection_two_vsmul
import Theorems.Thm_TunnellMap_primitivePartTriple_negTriple
import Theorems.Thm_TunnellMap_primitivePartTriple_two_vsmul
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_pos_of_ne_zero
import Theorems.Thm_TunnellMap_qForm_tau
import Theorems.Thm_TunnellMap_qForm_vsmul
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_source
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_target
import Theorems.Thm_TunnellMap_residualSourceLift_neg
import Theorems.Thm_TunnellMap_residualTargetLift_neg
import Theorems.Thm_TunnellMap_tripleContent_negTriple
import Theorems.Thm_TunnellMap_tripleContent_orientDirection
import Theorems.Thm_TunnellMap_tripleContent_primitiveDirection
import Theorems.Thm_TunnellMap_tripleContent_primitivePartTriple
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_one
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_two
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_zero
import Theorems.Thm_TunnellMap_triplePolynomial_negTriple
import Theorems.Thm_TunnellMap_triplePolynomial_vsmul
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.assemble_inl
attribute [local simp] TunnellMap.assemble_inr
attribute [local simp] TunnellMap.directionKey_negTriple
attribute [local simp] TunnellMap.directionKey_primitiveDirection
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.minusVector_neg_source
attribute [local simp] TunnellMap.minusVector_neg_target
attribute [local simp] TunnellMap.plusVector_neg_source
attribute [local simp] TunnellMap.plusVector_neg_target
attribute [local simp] TunnellMap.polynomialTriple_neg
attribute [local simp] TunnellMap.polynomialTriple_triplePolynomial
attribute [local simp] TunnellMap.primitiveDirection_idem
attribute [local simp] TunnellMap.primitiveDirection_negTriple
attribute [local simp] TunnellMap.primitiveDirection_two_vsmul
attribute [local simp] TunnellMap.primitivePartTriple_negTriple
attribute [local simp] TunnellMap.primitivePartTriple_two_vsmul
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_tau
attribute [local simp] TunnellMap.qForm_vsmul
attribute [local simp] TunnellMap.representativeEdgeKey_neg_source
attribute [local simp] TunnellMap.representativeEdgeKey_neg_target
attribute [local simp] TunnellMap.residualSourceLift_neg
attribute [local simp] TunnellMap.residualTargetLift_neg
attribute [local simp] TunnellMap.tripleContent_negTriple
attribute [local simp] TunnellMap.tripleContent_orientDirection
attribute [local simp] TunnellMap.tripleContent_primitiveDirection
attribute [local simp] TunnellMap.tripleContent_primitivePartTriple
attribute [local simp] TunnellMap.triplePolynomial_coeff_one
attribute [local simp] TunnellMap.triplePolynomial_coeff_two
attribute [local simp] TunnellMap.triplePolynomial_coeff_zero
attribute [local simp] TunnellMap.triplePolynomial_negTriple
attribute [local simp] TunnellMap.triplePolynomial_vsmul



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hn : Odd n) (hnpos : 0 < n)
    (s : BResidual n) (t : AResidual n) (R : PreferredMidpointRecord s t)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    ∃ W : GeneratorWitness s t R, W.frame = F := by
  let E := residualSourceLift s
  let d := R.direction
  let A := qForm d
  let q := R.multiplier
  let r := tau d
  have hdne : d ≠ ⟨0, 0, 0⟩ := odd_third_ne_zero R.direction_third_odd
  have hApos : 0 < A := qForm_pos_of_ne_zero hdne
  have hpNorm : dot (tau E) (tau E) = n := by
    rw [qForm_tau]
    simp [E, residualSourceLift]
  have hdot : dot (tau E) r = q * A := by
    calc
      dot (tau E) r = qBilinear E d := by
        simp [r, qBilinear]
      _ = q * qForm d := R.bilinear
      _ = q * A := rfl
  obtain ⟨ab, hab, _habUnique⟩ := F.affine_coset (q * A) r hdot
  let a := ab.1
  let b := ab.2
  have haffine : r = linComb3 a b (q * A) F.e₁ F.e₂ F.z := by
    simpa [a, b] using hab
  have hrnorm : dot r r = A := by
    simpa [r, A] using qForm_tau d
  obtain ⟨u, huSquare, huLinear⟩ :=
    (F.affine_norm_root_certificate A q a b).mp (by
      rw [← haffine]
      exact hrnorm)
  have hDnonneg : 0 ≤ F.halfDiscriminant A q b := by
    rw [← huSquare]
    exact sq_nonneg u
  have hshort := F.short_interval_identity A q b
  rw [hpNorm] at hshort
  dsimp at hshort
  have hnDnonneg : 0 ≤ n * F.halfDiscriminant A q b :=
    mul_nonneg (le_of_lt hnpos) hDnonneg
  have hwindow :
      let α := dot F.e₁ F.e₁
      let β := dot F.e₁ F.e₂
      let δ := dot F.z F.e₁
      let ε := dot F.z F.e₂
      let K := β * δ - α * ε
      let M := A * (n - q ^ 2 * A)
      (n * b - q * A * K) ^ 2 ≤ α * M := by
    dsimp
    nlinarith
  refine ⟨{
    frame := F
    A := A
    q := q
    r := r
    a := a
    b := b
    u := u
    A_eq := rfl
    q_eq := rfl
    r_eq := rfl
    A_pos := hApos
    A_bound := R.direction_bound
    q_odd := R.multiplier_odd
    q_range := preferred_half_norm_lt hn R
    r_tau_parity := tau_mem d
    affine_coordinates := haffine
    affine_norm := hrnorm
    root_certificate := ⟨huSquare, huLinear⟩
    short_window := hwindow }, rfl⟩
end TunnellMap
