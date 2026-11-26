-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.manuscript_cosetRelGen_elementaryAbelian_card_cast_eq_gammaR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:05:23.340888+00:00
-- url     : https://prove2.me/submissions/3cf2b1e0-ed8a-411a-8a20-7a3f3b626d99

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_card_generatingFrames_fin_zmod_cast_eq_gammaR
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
import Theorems.Thm_SharpIntermediateSubgroupBounds_natFloor_indexLog
import Theorems.Thm_SharpIntermediateSubgroupBounds_rawRelGen_card_eq_cosetRelGen_card_mul_cardH_pow
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.escapeBranchProduct_cons
attribute [local simp] SharpIntermediateSubgroupBounds.natFloor_indexLog



set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open Filter
noncomputable section
attribute [local instance] SharpIntermediateSubgroupBounds.manuscriptSubgroupIntervalFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution
    (p r : ℕ) [Fact p.Prime] :
    (Nat.card (CosetRelGen
      (⊥ : Subgroup (ElementaryAbelianGroup p r)) ⊤ r) : ℝ) =
      (p : ℝ) ^ (r * r) * gammaR (p : ℝ) r := by
  have hraw := rawRelGen_card_eq_cosetRelGen_card_mul_cardH_pow
    (G := ElementaryAbelianGroup p r)
    (H := (⊥ : Subgroup (ElementaryAbelianGroup p r))) (K := ⊤) bot_le r
  have hcard : Nat.card (CosetRelGen
      (⊥ : Subgroup (ElementaryAbelianGroup p r)) ⊤ r) =
      Nat.card (GeneratingFramesFinZMod p r) := by
    calc
      Nat.card (CosetRelGen
          (⊥ : Subgroup (ElementaryAbelianGroup p r)) ⊤ r) =
          Nat.card (RawRelGen
            (⊥ : Subgroup (ElementaryAbelianGroup p r)) ⊤ r) := by
        simpa using hraw.symm
      _ = Nat.card (GeneratingFramesFinZMod p r) :=
        Nat.card_congr (manuscript_rawRelGenEquivGeneratingFrames p r)
  rw [hcard]
  exact card_generatingFrames_fin_zmod_cast_eq_gammaR p r
end SharpIntermediateSubgroupBounds
