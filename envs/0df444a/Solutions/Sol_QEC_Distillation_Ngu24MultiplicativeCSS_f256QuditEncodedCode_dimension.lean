-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.f256QuditEncodedCode_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:38:18.353466+00:00
-- url     : https://prove2.me/submissions/bac3861b-dc42-4f66-9ebb-c0c72b95f729

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureDistance
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureFamily
import Theorems.Thm_QEC_Coding_f256_card
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry.F256GarciaStichtenoth Semantics
open Ngu24MultiplicativeCCZ
open Filter
open scoped BigOperators Topology
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_a61e848631_24
namespace QEC.Distillation.Ngu24MultiplicativeCSS
theorem _root_.solution (i : ℕ) :
    (f256QuditEncodedCode i).code.dimension = 256 ^ f256MultiplicationLogicalCount i := by
  have h := (f256QuditEncodedCode i).encoding.toLinearEquiv.finrank_eq
  rw [finrank_euclideanSpace] at h
  change Fintype.card (Fin (f256MultiplicationLogicalCount i) → F256) =
    (f256QuditEncodedCode i).code.dimension at h
  rw [← Nat.card_eq_fintype_card, Nat.card_fun, Nat.card_fin,
    Nat.card_eq_fintype_card, f256_card] at h
  exact h.symm
end QEC.Distillation.Ngu24MultiplicativeCSS
