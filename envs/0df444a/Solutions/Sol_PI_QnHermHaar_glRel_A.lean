-- Prove2me | solution 1 for PI.QnHermHaar.glRel_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:08:56.720904+00:00
-- url     : https://prove2.me/submissions/a2b24f3d-d581-4d4c-ada7-3f5d675e7d91

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SmoothLevZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnOfEq
import Theorems.Thm_PI_QnHermHaar_repOn_of_eq
import Theorems.Thm_PI_QnHermHaar_Gen_A_ext
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_mul
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_sub
import Theorems.Thm_PI_QnHermHaar_repE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset MeasureTheory
open scoped ContDiff
noncomputable section
namespace PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Gen
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {μ : Measure (Mt k r)}
private theorem eq_of_repOn_of_agree_on_test (H : Hyp k r z z' i μ) {S T : A (hI H)}
    {Φ Ψ : (Mx k r → ℂ) → Mx k r → ℂ} (hS : RepOn (hI H) S Φ) (hT : RepOn (hI H) T Ψ)
    (e : ∀ f, TestF k r i f → ∀ g ∈ Glev k r i, Φ f g = Ψ f g) : S = T :=
  A_ext (hI H) fun f hf => by
    rw [(hS f hf).2, (hT f hf).2]
    exact mk'_eq_of_eqOn (hI H) (Glev k r i) (hG H) (hS f hf).1 (hT f hf).1 (e f hf)
private theorem repOn_ite' (H : Hyp k r z z' i μ) (p : Prop) [Decidable p] {T : A (hI H)}
    {Φ : (Mx k r → ℂ) → Mx k r → ℂ} (hT : RepOn (hI H) T Φ) :
    RepOn (hI H) (if p then T else 0) (fun f g => if p then Φ f g else 0) := by
  by_cases hp : p
  · simp only [if_pos hp]
    exact hT
  · simp only [if_neg hp]
    have h0 := repOn_sub _ hT hT
    rw [sub_self] at h0
    exact repOn_of_eq h0 fun f => funext fun g => by simp
end PI.QnHermHaar
end
end

set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Gen
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {μ : Measure (Mt k r)}
namespace PI.QnHermHaar
theorem _root_.solution (H : Hyp k r z z' i μ) : GlRel (EA H) := by
  intro a b c d
  refine eq_of_repOn_of_agree_on_test H (repOn_sub _ (repOn_mul _ (repE H a b) (repE H c d)) (repOn_mul _ (repE H c d) (repE H a b)))
    (repOn_sub _ (repOn_ite' H (b = c) (repE H a d)) (repOn_ite' H (d = a) (repE H c b))) fun f hf g hg => ?_
  exact H.Gl ℂ k r i Set.univ a b c d f isOpen_univ hf.1 g ⟨hg, Set.mem_univ _⟩
end PI.QnHermHaar
