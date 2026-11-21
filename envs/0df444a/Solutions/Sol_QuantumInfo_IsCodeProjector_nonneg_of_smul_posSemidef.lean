-- Prove2me | solution 1 for QuantumInfo.IsCodeProjector.nonneg_of_smul_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:50:45.284969+00:00
-- url     : https://prove2.me/submissions/bb7019a4-34fd-4fce-9046-6a84e850c3e5

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_IsCodeProjector_trace_pos
public import Theorems.Thm_QuantumInfo_Channel_id_apply
attribute [local simp] QuantumInfo.Channel.id_apply



set_option autoImplicit false
@[expose] public section
public section
open Matrix Unitary
open scoped ComplexOrder ComplexConjugate
open QuantumInfo
variable {n : Type*} [Fintype n]
open QuantumInfo.IsCodeProjector
variable {P : Matrix n n ℂ} (hP : IsCodeProjector P)
include hP
namespace QuantumInfo.IsCodeProjector
theorem _root_.solution (hP0 : P ≠ 0) {a : ℝ}
    (h : ((a : ℂ) • P).PosSemidef) : 0 ≤ a := by
  have h1 := h.trace_nonneg
  rw [trace_smul, smul_eq_mul, Complex.nonneg_iff] at h1
  have h2 := hP.trace_pos hP0
  rw [Complex.pos_iff] at h2
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h1
  exact (mul_nonneg_iff_of_pos_right h2.1).mp h1.1
end QuantumInfo.IsCodeProjector
