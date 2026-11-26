-- Prove2me | solution 1 for boundedSesquilinearFormOfQuadratic_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:11.8688+00:00
-- url     : https://prove2.me/submissions/86d29ef9-a096-4f30-b032-64bac1175943

import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Spectral_Spectral_Polarization
section
open scoped ComplexConjugate
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
section
variable (q : V → ℝ)
variable (hq_smul : ∀ (c : ℂ) (x : V), q (c • x) = ‖c‖ ^ 2 * q x)
variable (hq_para : ∀ x y : V,
  q (x + y) + q (x - y) = (q x + q x) + (q y + q y))
include hq_smul
omit hq_smul
include hq_para
include hq_smul
omit hq_para
include hq_para
variable (hq_nonneg : ∀ x : V, 0 ≤ q x)
include hq_nonneg
variable (hq_le : ∀ x : V, q x ≤ ‖x‖ ^ 2)
include hq_le
omit hq_para hq_nonneg hq_le
include hq_para hq_nonneg hq_le
private theorem complexPolarization_self (x : V) :
    complexPolarization q x x = q x := by
  have hI := realPolarization_I_left q hq_smul hq_para hq_nonneg hq_le x x
  rw [realPolarization_symm q hq_smul x (Complex.I • x)] at hI
  have hzero : realPolarization q (Complex.I • x) x = 0 := by linarith
  unfold complexPolarization
  rw [realPolarization_self q hq_smul, hzero]
  norm_num
end
end

set_option autoImplicit false
open scoped ComplexConjugate
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable (q : V → ℝ)
variable (hq_smul : ∀ (c : ℂ) (x : V), q (c • x) = ‖c‖ ^ 2 * q x)
variable (hq_para : ∀ x y : V,
  q (x + y) + q (x - y) = (q x + q x) + (q y + q y))
include hq_smul
omit hq_smul
include hq_para
include hq_smul
omit hq_para
include hq_para
variable (hq_nonneg : ∀ x : V, 0 ≤ q x)
include hq_nonneg
variable (hq_le : ∀ x : V, q x ≤ ‖x‖ ^ 2)
include hq_le
omit hq_para hq_nonneg hq_le
include hq_para hq_nonneg hq_le
theorem _root_.solution (x : V) :
    boundedSesquilinearFormOfQuadratic q hq_smul hq_para hq_nonneg hq_le x x = q x := by
  change complexPolarization q x x = q x
  exact complexPolarization_self q hq_smul hq_para hq_nonneg hq_le x
