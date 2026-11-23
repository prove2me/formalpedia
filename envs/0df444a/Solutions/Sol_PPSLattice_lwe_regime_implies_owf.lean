-- Prove2me | solution 1 for PPSLattice.lwe_regime_implies_owf
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:56:12.265814+00:00
-- url     : https://prove2.me/submissions/7c989d10-d3f5-4c67-be95-46a6691c06a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PPSLattice_LWERegime
import Definitions.Def_PPSLattice_LWEHard
import Definitions.Def_PPSLattice_PPS_Efficient
import Definitions.Def_PPSLattice_PPS_Correct
import Definitions.Def_PPSLattice_PPS_FullyCompact
import Definitions.Def_PPSLattice_PPS_ModeInd
import Definitions.Def_PPSLattice_PPS_PayloadHiding
import Definitions.Def_PPSLattice_PPS_PkUniform
import Definitions.Def_PPSLattice_OWFExists
import Definitions.Def_PPSLattice_OWFInvProb
import Theorems.Thm_PPSLattice_lwe_regime_one_way_candidate
import Theorems.Thm_PPSLattice_owf_negligible_of_lwe_bound

set_option autoImplicit false
open QAlgorithms.Complexity
open PPSLattice

theorem solution (ε : ℝ) (q χ : ℕ → ℕ)
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (hreg : LWERegime ε q χ)
    (hLWE : LWEHard q χ) : OWFExists := by
  obtain ⟨f, hf, hbound⟩ := lwe_regime_one_way_candidate ε q χ hε hreg
  refine ⟨f, hf, ?_⟩
  intro I hI
  exact owf_negligible_of_lwe_bound q χ hLWE f hbound I hI
