-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_mu_pow_fib_0c2c6eb9bcfd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:37:42.907125+00:00
-- url     : https://prove2.me/submissions/eb09614a-6bb2-481f-9a15-d5ccd64229fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_tri_add_4de604ce2a7b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_smallBlockMu_16ace27c6226
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_fibreClass_79caf4ba8a5c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (hV : VandermondeOfHomogeneous.Statement) (f r a : ℕ)
    (c : SmallBlock) :
    (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c).IsHomogeneous
      (topDegree f (r + a)) := by
  have h := ((isHomogeneous_smallBlockMu f r a c).pow (f * (r * a))).mul
    (isHomogeneous_fibreClass hV f r a c)
  convert h using 1
  rw [topDegree, tri_add]
  ring
end GroundTheory.Heights₂.Heights.RestTerms.Top
