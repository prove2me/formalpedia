-- Prove2me | solution 1 for P2M_GlobalTheory_isLeast_schurComplement___c6fe192388c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:54:28.02348+00:00
-- url     : https://prove2.me/submissions/d9e17f80-2270-41de-a9bc-7894dfc87905

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {m n : Type*}
variable [Fintype n] [DecidableEq n]
variable [Fintype m] [DecidableEq m]
omit [DecidableEq n]
namespace GlobalTheory
theorem _root_.solution {G : Matrix (m ⊕ n) (m ⊕ n) ℂ} (hG : G.PosDef) (v : n → ℂ) :
    IsLeast (range fun u : m → ℂ => (star (Sum.elim u v) ⬝ᵥ G *ᵥ Sum.elim u v).re)
      (star v ⬝ᵥ schurComplement₁₁ G *ᵥ v).re := by
  have h11 : (G.toBlocks₁₁).PosDef := hG.submatrix Sum.inl_injective
  let _ := h11.isUnit.invertible
  have h21 : G.toBlocks₂₁ = (G.toBlocks₁₂)ᴴ := by
    ext i j; exact (hG.1.apply _ _).symm
  have key : ∀ u : m → ℂ, star (Sum.elim u v) ⬝ᵥ G *ᵥ Sum.elim u v =
      star (u + (G.toBlocks₁₁⁻¹ * G.toBlocks₁₂) *ᵥ v) ⬝ᵥ
        G.toBlocks₁₁ *ᵥ (u + (G.toBlocks₁₁⁻¹ * G.toBlocks₁₂) *ᵥ v) +
        star v ⬝ᵥ schurComplement₁₁ G *ᵥ v := by
    intro u
    have := schur_complement_eq₁₁ G.toBlocks₁₂ G.toBlocks₂₂ u v h11.1
    rw [← h21, fromBlocks_toBlocks] at this
    simpa only [dotProduct_mulVec, schurComplement₁₁] using this
  refine ⟨⟨-((G.toBlocks₁₁⁻¹ * G.toBlocks₁₂) *ᵥ v), ?_⟩, ?_⟩
  · simp only [key]
    simp
  · rintro _ ⟨u, rfl⟩
    simp only [key, Complex.add_re, le_add_iff_nonneg_left]
    exact (Complex.nonneg_iff.1 (h11.posSemidef.dotProduct_mulVec_nonneg _)).1
end GlobalTheory
