-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.good_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:00:09.129202+00:00
-- url     : https://prove2.me/submissions/2a8534ff-0072-45ca-a50c-16b94390e36a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_SmoothClassInFiniteOrder
import Theorems.Thm_PI_ComplexConjugateDerivative_ss_add
import Theorems.Thm_PI_ComplexConjugateDerivative_ss_smul
import Theorems.Thm_PI_ComplexConjugateDerivative_ss_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.ComplexConjugateDerivative
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.ComplexConjugateDerivative
theorem _root_.solution {Φ : (B.Mat k r → E) → (B.Mat k r → E)} (hΦ : Good Φ) {N : ℕ} (c : Fin N → ℝ)
    (h : Fin N → B.Mat k r → E) (hh : ∀ i, SS k r (h i)) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    Φ (∑ i, c i • h i) g = ∑ i, c i • Φ (h i) g := by
  have h0 : Φ 0 g = 0 := by
    have := hΦ.2.2 0 0 ss_zero g hg
    simpa only [zero_smul] using this
  have key : ∀ s : Finset (Fin N),
      SS k r (∑ i ∈ s, c i • h i) ∧ Φ (∑ i ∈ s, c i • h i) g = ∑ i ∈ s, c i • Φ (h i) g := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact ⟨ss_zero, h0⟩
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine ⟨ss_add (ss_smul _ (hh a)) ih.1, ?_⟩
      rw [hΦ.2.1 _ _ (ss_smul _ (hh a)) ih.1 g hg, hΦ.2.2 _ _ (hh a) g hg, ih.2]
  exact (key univ).2
end PI.ComplexConjugateDerivative
