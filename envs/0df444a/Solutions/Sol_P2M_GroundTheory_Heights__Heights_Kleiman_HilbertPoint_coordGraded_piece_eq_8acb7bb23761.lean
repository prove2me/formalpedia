-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_coordGraded_piece_eq_8acb7bb23761
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:21:54.028349+00:00
-- url     : https://prove2.me/submissions/cb8efe9c-fe12-48ec-875e-9251e4731ee0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
variable {y : Fin (N + 1) → Ω} {j : Fin (N + 1)}
namespace GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
theorem _root_.solution (hj : y j ≠ 0) (n : ℕ) :
    (coordGraded k y).piece (n : ℤ) = (affPiece k y j n).map (LinearMap.mulLeft k (y j ^ n)) := by
  rw [show (coordGraded k y).piece (n : ℤ) = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ),
    f.IsHomogeneous e ∧ (e : ℤ) = n ∧ z = aeval y f} from rfl, affPiece, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨f, e, hf, he, rfl⟩
    have hen : e = n := by exact_mod_cast he
    subst hen
    refine ⟨aeval (aff y j) f, ⟨f, hf, rfl⟩, ?_⟩
    rw [LinearMap.mulLeft_apply, aff_def, aeval_div_of_isHomogeneous hf]
    field_simp
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨f, n, hf, rfl, ?_⟩
    rw [LinearMap.mulLeft_apply, aff_def, aeval_div_of_isHomogeneous hf]
    field_simp
end GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
