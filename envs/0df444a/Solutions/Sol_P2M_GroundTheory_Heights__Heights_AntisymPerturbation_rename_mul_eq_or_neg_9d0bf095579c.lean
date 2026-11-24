-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymPerturbation_rename_mul_eq_or_neg_9d0bf095579c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:14.538339+00:00
-- url     : https://prove2.me/submissions/f0489734-fe04-4916-90c5-e06e7fca7bc7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymPerturbation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymPerturbation
variable {T : Type} [Fintype T] [DecidableEq T] {N j : ℕ}
omit [Fintype T] [DecidableEq T]
namespace GroundTheory.Heights₂.Heights.AntisymPerturbation
theorem _root_.solution {R : MvPolynomial (T × Fin N) ℝ} {σ ρ : Equiv.Perm (T × Fin N)}
    (hσ : rename σ R = R ∨ rename σ R = -R) (hρ : rename ρ R = R ∨ rename ρ R = -R) :
    rename ⇑(σ * ρ) R = R ∨ rename ⇑(σ * ρ) R = -R := by
  rw [Equiv.Perm.coe_mul, ← rename_rename]
  rcases hρ with h | h
  · rw [h]; exact hσ
  · rw [h, map_neg]
    rcases hσ with h' | h'
    · right; rw [h']
    · left; rw [h', neg_neg]
end GroundTheory.Heights₂.Heights.AntisymPerturbation
