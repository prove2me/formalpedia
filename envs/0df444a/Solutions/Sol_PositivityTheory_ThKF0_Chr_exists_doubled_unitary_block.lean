-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.exists_doubled_unitary_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:41.243222+00:00
-- url     : https://prove2.me/submissions/10d9b19a-eb63-472d-a490-56202a14bfc0

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_DoublingGramFromBlocks
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ExistsDoubledUnitaryBlock
import Theorems.Thm_P2M_PositivityTheory_ThK_SiegelT_map_one__a6a1ccb9bfd7


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM PositivityTheory.ThK.SiegelT
variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β β₁ ν κ κ₁ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype β₁] [DecidableEq β₁]
  [Fintype ν] [DecidableEq ν] [Fintype κ] [Fintype κ₁] {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E}
  {JA : Matrix α α E} {J : Matrix β β E} {J₁ : Matrix β₁ β₁ E} {ι : Matrix β β₁ E} {X : Matrix β ν E}
  {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}
omit [Invertible (2 : R)]
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution {J : Matrix β β E} (g : UG c J) : ∃ gd : UG c (dbl J),
    ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 := by
  refine ⟨⟨⟨fromBlocks (g : GL β E).1 0 0 1, fromBlocks ((g : GL β E)⁻¹).1 0 0 1, ?_, ?_⟩, ?_⟩, rfl⟩
  · rw [fromBlocks_multiply, Units.mul_inv]; simp
  · rw [fromBlocks_multiply, Units.inv_mul]; simp
  · have hp' : ((g : GL β E) : Matrix β β E)ᵀ * J * ((g : GL β E) : Matrix β β E).map c = J := g.2
    show (fromBlocks (g : GL β E).1 0 0 1)ᵀ * dbl J * (fromBlocks (g : GL β E).1 0 0 1).map c = dbl J
    simp only [dbl, fromBlocks_transpose, fromBlocks_map, Matrix.map_zero _ (map_zero c), map_one', fromBlocks_multiply]
    simp [hp']
end PositivityTheory.ThKF0.Chr
