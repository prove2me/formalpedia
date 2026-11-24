-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_natAdd_of_mem_4bb9909352d8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:39.718946+00:00
-- url     : https://prove2.me/submissions/418b3274-2af0-4d74-9237-a6dae973392a

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
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) (i : Fin d) :
    z (Fin.natAdd n i) = eval (firstPart z) (p i) := by
  have h := hz (X (Fin.natAdd n i) - rename (Fin.castAdd d) (p i)) (by
    show graphSubst p (X (Fin.natAdd n i) - rename (Fin.castAdd d) (p i)) ∈ P
    rw [map_sub, graphSubst_rename, graphSubst, aeval_X, Fin.append_right, sub_self]
    exact P.zero_mem)
  rw [map_sub, eval_X, eval_rename, sub_eq_zero] at h
  exact h
end GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
