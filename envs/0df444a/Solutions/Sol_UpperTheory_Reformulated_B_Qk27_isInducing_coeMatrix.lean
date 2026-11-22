-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qk27.isInducing_coeMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:46.752622+00:00
-- url     : https://prove2.me/submissions/a85dc907-7790-40c8-8aaa-b182689f4078

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsInducingCoeMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.Qk27.Jm_mul_self {n : ℕ} (ε : Fin n → Bool) :
    UpperTheory.Reformulated.B.Qk27.Jm ε * UpperTheory.Reformulated.B.Qk27.Jm ε = 1 := by
  unfold UpperTheory.Reformulated.B.Qk27.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qk27
theorem _root_.solution :
    ∀ {n : ℕ} (ε : Fin n → Bool), Topology.IsInducing (UpperTheory.Reformulated.B.Qk27.coeMatrixAlt ε) := by
  intro n ε
  let k : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    fun x ↦ (x, MulOpposite.op (UpperTheory.Reformulated.B.Qk27.Jm ε * (x.conjTranspose * UpperTheory.Reformulated.B.Qk27.Jm ε)))
  have hk : Continuous k :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      (continuous_const.matrix_mul (continuous_id.matrix_conjTranspose.matrix_mul continuous_const)))
  have hc : Continuous (UpperTheory.Reformulated.B.Qk27.coeMatrixAlt ε) :=
    Units.continuous_val.comp continuous_subtype_val
  have he : k ∘ UpperTheory.Reformulated.B.Qk27.coeMatrixAlt ε =
      Units.embedProduct (Matrix (Fin n) (Fin n) ℂ) ∘
        (Subtype.val : ↥(UpperTheory.Reformulated.B.Qk27.UJ ε) → (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
    funext g
    have hg : (g.1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Qk27.Jm ε * g.1 =
        UpperTheory.Reformulated.B.Qk27.Jm ε := g.2
    have hi : ((g.1⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
        UpperTheory.Reformulated.B.Qk27.Jm ε *
          ((g.1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Qk27.Jm ε) := by
      apply Units.inv_eq_of_mul_eq_one_left
      rw [Matrix.mul_assoc, hg, UpperTheory.Reformulated.B.Qk27.Jm_mul_self]
    exact Prod.ext rfl (congrArg MulOpposite.op hi.symm)
  refine Topology.IsInducing.of_comp hc hk ?_
  rw [he]
  exact Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal
end UpperTheory.Reformulated.B.Qk27
