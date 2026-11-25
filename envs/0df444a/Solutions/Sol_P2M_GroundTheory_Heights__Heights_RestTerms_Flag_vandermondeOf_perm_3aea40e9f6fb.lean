-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_vandermondeOf_perm_3aea40e9f6fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:52:23.969592+00:00
-- url     : https://prove2.me/submissions/bcf146c1-1bef-4148-a90f-dae89dfb7a0d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_vandermondeOf_eq_det_c2f7ea43a739

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
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R)
    (σ : Equiv.Perm (Fin m)) :
    vandermondeOf (fun i => v (σ i)) = (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * vandermondeOf v := by
  rw [vandermondeOf_eq_det, vandermondeOf_eq_det]
  have : Matrix.vandermonde (fun i => -v (σ i)) =
      (Matrix.vandermonde (fun i => -v i)).submatrix σ id := by
    ext i j; rfl
  rw [this, Matrix.det_permute]
end GroundTheory.Heights₂.Heights.RestTerms.Flag
