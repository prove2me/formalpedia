-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockTrdeg_proof_71d40a4eb56d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:24:08.397395+00:00
-- url     : https://prove2.me/submissions/7f1dd0b8-29c2-4577-b799-cb73ce5d6f44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsBlockTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PBlockTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockTrdeg_algebraicIndependent_forgotten_1e622b88ee59

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 Algebra Cardinal
open GroundTheory.Heights₂.Heights.BlockTrdeg
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open scoped Classical
namespace GroundTheory.Heights₂.Heights.BlockTrdeg
theorem _root_.solution : Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' L _ _ φ hκv hP hker
  obtain ⟨hκ, -, hv, -⟩ := hκv
  choose i hi using fun k : Forgotten κ ↦ hP.2.2 k.1
  set A := adjoin ℚ (Set.range fun p : Σ k, ι k ↦ φ (X (v p))) with hAdef
  set B := adjoin ℚ (Set.range fun q : Σ k', ι' k' ↦ φ (X q)) with hBdef
  have : FaithfulSMul ℚ A :=
    (faithfulSMul_iff_algebraMap_injective ℚ A).mpr (algebraMap ℚ A).injective
  obtain ⟨τ, x, hx⟩ := exists_isTranscendenceBasis' ℚ A
  set b₀ : τ → L := A.val ∘ x with hb₀def
  have hb₀ : AlgebraicIndependent ℚ b₀ := hx.1.map' Subtype.val_injective
  have hSA : adjoin ℚ (Set.range b₀) ≤ A := adjoin_le (Set.range_subset_iff.mpr fun j ↦ (x j).2)
  have he := algebraicIndependent_forgotten hv hP.2.1 hP.1 hker i hi _ hSA
  have hind : AlgebraicIndependent ℚ (Sum.elim (fun k : Forgotten κ ↦ φ (X ⟨k.1, i k⟩)) b₀) :=
    hb₀.sumElim he
  have hAB : A ≤ B := adjoin_mono (Set.range_subset_iff.mpr fun p ↦ ⟨v p, rfl⟩)
  have hmem : ∀ j, Sum.elim (fun k : Forgotten κ ↦ φ (X ⟨k.1, i k⟩)) b₀ j ∈ B := by
    rintro (k | j)
    · exact subset_adjoin ⟨_, rfl⟩
    · exact hAB (x j).2
  have hy : AlgebraicIndependent ℚ (fun j ↦ (⟨_, hmem j⟩ : B)) := AlgebraicIndependent.of_comp B.val hind
  have hle := hy.cardinalMk_le_trdeg
  have hcard : ((Fintype.card K' - Fintype.card K : ℕ) : Cardinal) = #(Forgotten κ) := by
    rw [Cardinal.mk_fintype, Fintype.card_subtype_compl, Set.card_range_of_injective hκ]
  rw [← hx.cardinalMk_eq_trdeg, hcard, add_comm, ← lift_id #(Forgotten κ), ← lift_id #τ, ← mk_sum]
  exact hle
end GroundTheory.Heights₂.Heights.BlockTrdeg
