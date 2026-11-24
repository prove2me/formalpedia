-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchJTMatrixDetAtRoots_proof_4064d62d2596
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:04:32.719808+00:00
-- url     : https://prove2.me/submissions/6475bcd6-7b06-4fdd-b26f-3e9d943f34f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchJTMatrixDetAtRoots
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_staircase_eq_vandermondeOf_202c942a4a9b


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
namespace SchJTMatrixDetAtRoots
theorem _root_.solution (h1 : SchRootOfUnityBialternant.Statement)
    (h2 : SchRootOfUnityRowsPerm.Statement) (h3 : SchRootOfUnityRowsEq.Statement)
    (h4 : SchHookResidues.Statement) (h5 : SchNonHookResidues.Statement)
    (h6 : SchRootOfUnityVandermondeNe.Statement) : SchJTMatrixDetAtRoots.Statement := by
  intro k nu hk hanti hsum
  have hV := h6 k hk
  have hB := h1 k nu hk

  have hstair : (Matrix.of fun i j : Fin k =>
      rootOfUnity k ^ ((j : ℕ) * (k - 1 - (i : ℕ)))).det =
      vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ)) := by
    rw [← Schur.det_pow_staircase_eq_vandermondeOf (fun j : Fin k => rootOfUnity k ^ (j : ℕ))]
    congr 1
    ext i j
    simp [Matrix.of_apply, pow_mul]
  split_ifs with hhook
  · obtain ⟨π, hres, hsign⟩ := h4 k nu hk hanti hsum hhook
    have hP := h2 k (fun i => nu i + (k - 1 - (i : ℕ))) π hk hres
    rw [hstair] at hP
    have hP' : (Matrix.of fun i j : Fin k =>
        rootOfUnity k ^ ((j : ℕ) * (nu i + (k - 1 - (i : ℕ))))).det =
        (((Equiv.Perm.sign π : ℤ) : ℂ)) *
          vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ)) := hP
    rw [hB] at hP'
    have := mul_right_cancel₀ hV hP'
    rw [this, hsign]
    push_cast
    rfl
  · obtain ⟨i, i', hne, hres⟩ := h5 k nu hk hanti hsum hhook
    have hZ : (Matrix.of fun i j : Fin k =>
        rootOfUnity k ^ ((j : ℕ) * (nu i + (k - 1 - (i : ℕ))))).det = 0 :=
      h3 k (fun i => nu i + (k - 1 - (i : ℕ))) i i' hne hres
    rw [hB] at hZ
    exact (mul_eq_zero.mp hZ).resolve_right hV
end SchJTMatrixDetAtRoots
end GroundTheory.Heights₂.Heights.RestTerms
