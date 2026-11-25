-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_exists_rows_eq_5673bfa09b10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:35.234154+00:00
-- url     : https://prove2.me/submissions/37b6b04f-b67d-461b-8903-9f217f346918

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericProjectionFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) (A : Matrix (Fin d) (Fin n) ℂ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, (F * U).submatrix s id = A := by
  refine ⟨star F * Matrix.of (Function.extend s (fun i => A i) 0), ?_⟩
  rw [← Matrix.mul_assoc, mem_unitaryGroup_iff.mp hF, Matrix.one_mul]
  ext i j
  simp [hs.extend_apply]
end GroundTheory.Heights₂.Heights.ComplexSets
