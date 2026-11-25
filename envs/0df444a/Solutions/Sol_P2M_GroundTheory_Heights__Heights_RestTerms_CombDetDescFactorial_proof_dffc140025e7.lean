-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombDetDescFactorial_proof_dffc140025e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:34:07.689036+00:00
-- url     : https://prove2.me/submissions/f61ca5d5-a97e-4964-bd39-9f406de4343a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombDetDescFactorial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_vandermondeOf_eq_det_1456c8f3d73e


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
open Comb Equiv
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CombDetDescFactorial
theorem _root_.solution : CombDetDescFactorial.Statement := by
  intro m l
  rw [vandermondeOf_eq_det]

  set v : Fin m → ℚ := fun i => (l i : ℚ)
  have hA : (Matrix.of fun i j : Fin m => ((l i).descFactorial (stair m j) : ℚ)) =
      (Matrix.of fun i j : Fin m => (descPochhammer ℚ (j : ℕ)).eval (v i)).submatrix
        id Fin.revPerm := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, id, Fin.revPerm_apply, v,
      descPochhammer_eval_eq_descFactorial, stair]
    rw [Fin.val_rev]
    congr 2
    omega
  have hB : (Matrix.of fun i j : Fin m => v i ^ (m - 1 - (j : ℕ))) =
      (Matrix.vandermonde v).submatrix id Fin.revPerm := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, id, Fin.revPerm_apply, Fin.val_rev,
      Matrix.vandermonde_apply]
    congr 1
    omega
  rw [hA, hB, Matrix.det_permute', Matrix.det_permute',
    Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v
      (fun j => descPochhammer ℚ (j : ℕ))
      (fun j => descPochhammer_natDegree ℚ _)
      (fun j => monic_descPochhammer ℚ _)]
end CombDetDescFactorial
end GroundTheory.Heights₂.Heights.RestTerms
