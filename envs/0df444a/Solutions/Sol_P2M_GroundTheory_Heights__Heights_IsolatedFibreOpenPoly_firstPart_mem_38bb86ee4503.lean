-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_firstPart_mem_38bb86ee4503
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:18:06.461863+00:00
-- url     : https://prove2.me/submissions/cc2e17c7-cd78-4bd8-a1ea-7ca4c2c358fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpenPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreOpenPoly
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphSubst_rename_56826dea6eef

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
open MvPolynomial Topology Filter Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
theorem _root_.solution {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) :
    firstPart z ∈ zeroSet P := by
  intro q hq
  have h := hz (rename (Fin.castAdd d) q) (by
    show graphSubst p (rename (Fin.castAdd d) q) ∈ P
    rw [graphSubst_rename]
    exact hq)
  rw [eval_rename] at h
  exact h
end GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
