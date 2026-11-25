-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_LemmaC_proof_883e0fff4247
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:40:09.329534+00:00
-- url     : https://prove2.me/submissions/22ceb018-eb00-4eab-b22d-79e8457dad6e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltFrob
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PLemmaC
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_eq_frobDim_2ce7df01df95
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrobeniusRectangleBound_intersectionNumber_baseChange_3a98f7db5654


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace LemmaC
theorem _root_.solution (h1 : FrobeniusDimensionFormula.Statement) : LemmaC.Statement := by
  intro r a nu hnu
  have hsum : Antitone (fun i => a + nu i) := fun i j hij => Nat.add_le_add_left (hnu hij) a
  have hrect : Antitone (rectangle r a) := fun _ _ _ => le_rfl
  have hb := GroundTheory.Heights₂.Heights.FrobeniusRectangleBound.intersectionNumber_baseChange r a nu hnu
  rw [← numStandardTable_eq_frobDim h1 _ hsum, ← numStandardTable_eq_frobDim h1 nu hnu,
    show (fun _ : Fin r => a) = rectangle r a from rfl,
    ← numStandardTable_eq_frobDim h1 _ hrect] at hb
  exact_mod_cast hb
end LemmaC
end GroundTheory.Heights₂.Heights.RestTerms
