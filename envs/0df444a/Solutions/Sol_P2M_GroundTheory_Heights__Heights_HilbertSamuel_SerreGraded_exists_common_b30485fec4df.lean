-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_exists_common_b30485fec4df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:32.47884+00:00
-- url     : https://prove2.me/submissions/1cac7f35-7773-431d-b2b3-c4c0900abf92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSerreGraded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
open Polynomial
variable {Ω : Type} [Field Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
variable [Algebra (MvPolynomial (Fin q) ℤ) (Polynomial Ω)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
theorem _root_.solution {ι : Type*} (s : Finset ι) (P : ι → ℕ → Prop)
    (h : ∀ i ∈ s, ∃ D, ∀ D', D ≤ D' → P i D') : ∃ D, ∀ i ∈ s, P i D := by
  classical
  choose! f hf using h
  exact ⟨s.sup f, fun i hi => hf i hi _ (Finset.le_sup hi)⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
