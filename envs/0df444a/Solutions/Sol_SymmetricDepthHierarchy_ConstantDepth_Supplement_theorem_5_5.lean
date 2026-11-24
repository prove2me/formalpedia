-- Prove2me | solution 1 for SymmetricDepthHierarchy.ConstantDepth.Supplement.theorem_5_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T15:17:16.729825+00:00
-- url     : https://prove2.me/submissions/402f1233-760c-4ef8-aadb-08d484cdced3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Branching
import Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_theorem_C_10

set_option autoImplicit false
open scoped Classical
noncomputable section

open SymmetricDepthHierarchy.ConstantDepth.Supplement in
/-- containment: symVAC ⊆ symVP (drop the depth bound). -/
theorem symVAC_subset_symVP_aux (K : Type) [Field K] : symVAC K ⊆ symVP K := by
  rintro p ⟨k, hk, hinv, c, N, h⟩
  refine ⟨hinv, c, N, fun n hn hN => ?_⟩
  obtain ⟨m, C, hw, hs, hc, hP⟩ := h n hn hN
  exact ⟨m, C, hw, hs, hc, hP.1⟩

open SymmetricDepthHierarchy.ConstantDepth.Supplement in
theorem solution (K : Type) [Field K] [CharZero K] : symVAC K ⊂ symVP K := by
  obtain ⟨_, _, _, _, _, _, p, hP, hA, _⟩ := theorem_C_10 K
  exact Set.ssubset_iff_subset_ne.mpr ⟨symVAC_subset_symVP_aux K, fun h => hA (h ▸ hP)⟩
