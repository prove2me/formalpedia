-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.toE_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:58.212339+00:00
-- url     : https://prove2.me/submissions/23bae414-0cec-4a38-89b9-40b4845ca895

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_toE_continuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (NormedSpace.exp X) =
      NormedSpace.exp (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X) := by

  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.map_exp _ (toE_continuous n) X
end ReciprocityTheory.ChartRestriction.DS
