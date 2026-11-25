-- Prove2me | solution 1 for PI.QnRT.w_uh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:34:13.436609+00:00
-- url     : https://prove2.me/submissions/d861d019-1776-474f-b389-ae73c389ff98

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Theorems.Thm_PI_QnRT_tau_e
import Theorems.Thm_PI_QnRT_tau_es
import Theorems.Thm_PI_QnRT_sgn_e
import Theorems.Thm_PI_QnRT_sgn_es
import Theorems.Thm_PI_QnRT_w_col_e
import Theorems.Thm_PI_QnRT_w_col_es
import Theorems.Thm_PI_QnRT_w_col_other
import Theorems.Thm_PI_QnRT_w_row_e
import Theorems.Thm_PI_QnRT_w_row_es
import Theorems.Thm_PI_QnRT_w_row_other
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace PI.QnRT
variable {k r : ℕ}
private lemma tau_val_lemma (i : Fin (2 * r + k + 1)) :
    (WeylGroupFacts.tau k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := rfl
private lemma tau_tau_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.tau k r (WeylGroupFacts.tau k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  simp only [tau_val_lemma]
  split_ifs <;> omega
private lemma sgn_tau_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r (WeylGroupFacts.tau k r i) = WeylGroupFacts.sgn k r i := by
  have hi := i.isLt
  unfold WeylGroupFacts.sgn
  simp only [tau_val_lemma]
  split_ifs <;> first | rfl | omega
private lemma hpk_eq_lemma (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = WeylGroupFacts.tau k r i then WeylGroupFacts.sgn k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk WeylGroupFacts.sgn
  simp only [Fin.ext_iff, tau_val_lemma]
  split_ifs <;> first | rfl | omega | norm_num
private lemma hpk_col_lemma (x y : Fin (2 * r + k + 1)) :
    Hpk k r x y = if x = WeylGroupFacts.tau k r y then WeylGroupFacts.sgn k r y else 0 := by
  rw [hpk_eq_lemma]
  by_cases h : x = WeylGroupFacts.tau k r y
  · subst h
    simp [tau_tau_lemma, sgn_tau_lemma]
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    rw [h', tau_tau_lemma]
private lemma conjTranspose_mul_Hpk_mul_apply (A : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (Aᴴ * Hpk k r * A) p q = ∑ y, star (A (WeylGroupFacts.tau k r y) p) * WeylGroupFacts.sgn k r y * A y q := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, hpk_col_lemma, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
end PI.QnRT
end
end

set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.QnRT
variable {k r : ℕ}
namespace PI.QnRT
theorem _root_.solution (l : Fin r) (a : ℂ) (ha : a ≠ 0) : w1 k r l a ∈ UH (Hpk k r) := by
  show (w1 k r l a)ᴴ * Hpk k r * w1 k r l a = Hpk k r
  ext p q
  rw [conjTranspose_mul_Hpk_mul_apply, hpk_col_lemma]
  by_cases hq1 : q = eI k r l
  · subst hq1
    simp only [w_col_e, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, tau_es, sgn_es, w_row_e, tau_e, sgn_e]
    by_cases hp : p = esI k r l
    · rw [if_pos hp, if_pos hp, mul_one]
      first
        | rw [star_inv₀, star_star, inv_mul_cancel₀ ha]
        | rw [star_inv', star_star, inv_mul_cancel₀ ha]
    · simp [hp]
  by_cases hq2 : q = esI k r l
  · subst hq2
    simp only [w_col_es, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, tau_e, sgn_e, w_row_es, tau_es, sgn_es]
    by_cases hp : p = eI k r l
    · rw [if_pos hp, if_pos hp, mul_one]
      exact mul_inv_cancel₀ (star_ne_zero.mpr ha)
    · simp [hp]
  have hcol : ∀ x, w1 k r l a x q = if x = q then 1 else 0 := fun x => w_col_other l a x q hq1 hq2
  simp only [hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have ht1 : WeylGroupFacts.tau k r q ≠ eI k r l := fun h => hq2 (by rw [← tau_tau_lemma q, h, tau_e])
  have ht2 : WeylGroupFacts.tau k r q ≠ esI k r l := fun h => hq1 (by rw [← tau_tau_lemma q, h, tau_es])
  rw [w_row_other l a _ p ht1 ht2]
  by_cases h : p = WeylGroupFacts.tau k r q
  · subst h
    simp
  · have h' : WeylGroupFacts.tau k r q ≠ p := Ne.symm h
    simp [h, h']
end PI.QnRT
