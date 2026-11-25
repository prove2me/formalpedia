-- Prove2me | solution 1 for PI.QnHermHaar.starE_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:26.928752+00:00
-- url     : https://prove2.me/submissions/c91082f2-ba53-4729-89db-ed7a6cdd9023

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SmoothLevZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnOfEq
import Theorems.Thm_PI_QnHermHaar_Gen_A_ext
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_smul
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_sum
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_toA
import Theorems.Thm_PI_QnHermHaar_Gen_star_toA
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
theorem _root_.solution (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) :
    star (EA H a b) = ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EA H c d := by
  have hL : RepOn (hI H) (star (EA H a b)) (EOp' k r i a b) := by
    show RepOn (hI H) (star (toA (hI H) (hG H) (adjOp_E H a b))) _
    rw [star_toA]
    exact repOn_toA _ _ _
  have hR : RepOn (hI H) (∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EA H c d)
      (fun f => ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EOp k r i c d f) :=
    repOn_sum _ _ fun c _ => repOn_sum _ _ fun d _ => repOn_smul _ _ (repE H c d)
  refine eq_of_repOn_of_agree_on_test H hL hR fun f _ g _ => ?_
  simp only [EOp'_eq]
end PI.QnHermHaar
