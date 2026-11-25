-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_isZariskiOpen_of_local_8b9b0416d030
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:51:52.743719+00:00
-- url     : https://prove2.me/submissions/753d6ed4-13b8-4003-954f-deebd01abd4f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen

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
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution {U : Set (Matrix (Fin d) (Fin n) ℂ)}
    (H : ∀ A₀ ∈ U, ∃ p : MvPolynomial (Fin d × Fin n) ℂ,
      eval (fun ij : Fin d × Fin n => A₀ ij.1 ij.2) p ≠ 0 ∧
        ∀ A : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => A ij.1 ij.2) p ≠ 0 → A ∈ U) :
    IsZariskiOpen U := by
  refine ⟨{p | ∀ A : Matrix (Fin d) (Fin n) ℂ,
    eval (fun ij : Fin d × Fin n => A ij.1 ij.2) p ≠ 0 → A ∈ U}, ?_⟩
  ext A
  constructor
  · intro hA
    obtain ⟨p, hp, hpU⟩ := H A hA
    exact ⟨p, hpU, hp⟩
  · rintro ⟨p, hpU, hp⟩
    exact hpU A hp
end GroundTheory.Heights₂.Heights.ComplexSets
