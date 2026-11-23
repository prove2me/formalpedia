-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:16.993268+00:00
-- url     : https://prove2.me/submissions/1f34114f-7177-4b04-8c44-c6d673a169a5

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsClosedEmbeddingToM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.Qk16.Jm_mul_Jm {n : ℕ} (ε : Fin n → Bool) :
    UpperTheory.Reformulated.B.Qk16.Jm ε * UpperTheory.Reformulated.B.Qk16.Jm ε = 1 := by
  unfold UpperTheory.Reformulated.B.Qk16.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp
private theorem UpperTheory.Reformulated.B.Qk16.left_inv {n : ℕ} (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : UpperTheory.Reformulated.B.Qk16.inUJ ε A) :
    UpperTheory.Reformulated.B.Qk16.Jm ε * A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A = 1 := by
  have h : A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A = UpperTheory.Reformulated.B.Qk16.Jm ε := hA
  calc UpperTheory.Reformulated.B.Qk16.Jm ε * A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A
      = UpperTheory.Reformulated.B.Qk16.Jm ε * (A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, UpperTheory.Reformulated.B.Qk16.Jm_mul_Jm]
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qk16
theorem _root_.solution :
    ∀ {n : ℕ} (ε : Fin n → Bool), Topology.IsClosedEmbedding fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g := by
  intro n ε
  have hc : Continuous fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g :=
    Units.continuous_val.comp continuous_subtype_val
  refine ⟨?_, ?_⟩
  · let F : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
      fun A ↦ (A, MulOpposite.op (UpperTheory.Reformulated.B.Qk16.Jm ε * A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε))
    have hF : Continuous F :=
      continuous_id.prodMk (MulOpposite.continuous_op.comp
        ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
    refine Topology.IsEmbedding.of_comp hc hF ?_
    have he : Topology.IsEmbedding
        ((Units.embedProduct (Matrix (Fin n) (Fin n) ℂ)) ∘
          (Subtype.val : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε) → (Matrix (Fin n) (Fin n) ℂ)ˣ)) :=
      Units.isEmbedding_embedProduct.comp Topology.IsEmbedding.subtypeVal
    have heq : (F ∘ fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g) =
        ((Units.embedProduct (Matrix (Fin n) (Fin n) ℂ)) ∘
          (Subtype.val : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε) → (Matrix (Fin n) (Fin n) ℂ)ˣ)) := by
      funext g
      have hg : UpperTheory.Reformulated.B.Qk16.inUJ ε (g.1 : Matrix (Fin n) (Fin n) ℂ) := g.2
      have h := Units.inv_eq_of_mul_eq_one_left (UpperTheory.Reformulated.B.Qk16.left_inv ε hg)
      rw [Function.comp_apply, Function.comp_apply, Units.embedProduct_apply, h]
    rw [heq]
    exact he
  · have hr : Set.range (fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g) =
        {A | A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A = UpperTheory.Reformulated.B.Qk16.Jm ε} := by
      ext A
      constructor
      · rintro ⟨g, rfl⟩
        exact g.2
      · intro hA
        have h := UpperTheory.Reformulated.B.Qk16.left_inv ε (A := A) hA
        exact ⟨⟨⟨A, _, mul_eq_one_comm.mp h, h⟩, hA⟩, rfl⟩
    rw [hr]
    exact isClosed_eq
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
end UpperTheory.Reformulated.B.Qk16
