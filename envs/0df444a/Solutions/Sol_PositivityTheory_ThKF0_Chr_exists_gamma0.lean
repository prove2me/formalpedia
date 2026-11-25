-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.exists_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:38.386264+00:00
-- url     : https://prove2.me/submissions/ab32b731-6e51-445b-b668-cba169d2e07f

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAlg
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_DoublingGramFromBlocks
import Theorems.Thm_PositivityTheory_ThKF0_Chr_eta_sq
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
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {β β₁ μ ν : Type} [Fintype β] [DecidableEq β] [Fintype β₁] [DecidableEq β₁] [Fintype μ] [DecidableEq μ]
  [Fintype ν] [DecidableEq ν]
variable {J : Matrix β β E} {J₁ : Matrix β₁ β₁ E} {H : Matrix μ μ E} {ι : Matrix β β₁ E} {Z : Matrix β μ E}
  {π : Matrix β₁ β E} {ρ : Matrix μ β E}
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution (η : ℤˣ) : ∃ γ : UG c (dbl (hyp ν η : Matrix _ _ E)), γ.1.1 * (diagCols (ν ⊕ ν) : Matrix _ _ E) =
    dd2 (fromRows (1 : Matrix ν ν E) (0 : Matrix ν ν E)) * (fromBlocks 1 0 0 (((η : ℤ) : E) • 1) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) := by
  set a : E := ((η : ℤ) : E) with ha
  have h2 : a * a = 1 := eta_sq η
  have hca : (a • (1 : Matrix ν ν E)).map c = a • 1 := by
    ext i j; by_cases h : i = j <;> simp [h, ha, Matrix.one_apply]
  have hm1 : (-1 : Matrix ν ν E).map c = -1 := by rw [Matrix.map_neg _ (map_neg c), map_one']
  have hz : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
  let g : Matrix ((ν ⊕ ν) ⊕ (ν ⊕ ν)) ((ν ⊕ ν) ⊕ (ν ⊕ ν)) E :=
    fromBlocks (fromBlocks 1 0 0 1) (fromBlocks 0 0 0 (-1)) (fromBlocks 0 0 (-1) 0) (fromBlocks 0 (a • 1) 1 0)
  let g' : Matrix ((ν ⊕ ν) ⊕ (ν ⊕ ν)) ((ν ⊕ ν) ⊕ (ν ⊕ ν)) E :=
    fromBlocks (fromBlocks 1 0 0 1) (fromBlocks 0 0 (a • 1) 0) (fromBlocks 1 0 0 0) (fromBlocks 0 1 (a • 1) 0)
  refine ⟨⟨⟨g, g', ?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [g, g', fromBlocks_multiply, fromBlocks_add, ← fromBlocks_one, ← fromBlocks_zero]
    simp [smul_smul, h2]
  · simp only [g, g', fromBlocks_multiply, fromBlocks_add, ← fromBlocks_one, ← fromBlocks_zero]
    simp [smul_smul, h2]
  · show gᵀ * _ * g.map c = _
    simp only [g, hyp, ← ha, dbl, fromBlocks_transpose, fromBlocks_map, map_one', hm1, hz, hca, fromBlocks_neg, ← fromBlocks_zero,
      fromBlocks_multiply, fromBlocks_add]
    simp [smul_smul, h2]
  · show g * diagCols (E := E) (ν ⊕ ν) = _
    simp only [g, diagCols, fromBlocks_mul_fromRows, Matrix.mul_one, fromBlocks_add, fromBlocks_multiply]
    ext ((i | i) | (i | i)) (j | j) <;> simp
end PositivityTheory.ThKF0.Chr
