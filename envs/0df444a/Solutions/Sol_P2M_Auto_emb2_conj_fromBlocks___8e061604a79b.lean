-- Prove2me | solution 1 for P2M_Auto_emb2_conj_fromBlocks___8e061604a79b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:10:39.90835+00:00
-- url     : https://prove2.me/submissions/ce120782-102a-40ed-9690-c596211d57f2

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Auto
theorem _root_.solution (X11 X12 X21 X22 : Matrix ι ι ℂ) :
    emb2 (ι := ι) 1 2 * Matrix.fromBlocks X11 X12 X21 X22 * (emb2 (ι := ι) 1 2)ᴴ =
      blk3 !![0, 0, 0; 0, X11, X12; 0, X21, X22] := by
  ext ⟨w, a⟩ ⟨w', b⟩
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, emb2, Matrix.of_apply, Sum.elim_inl,
    Sum.elim_inr, Matrix.conjTranspose_apply, blk3, Matrix.comp_apply, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  fin_cases w <;> fin_cases w' <;> simp [Prod.ext_iff]
end Auto
