-- Prove2me | solution 1 for PI.QnRT.conj_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:10:57.22819+00:00
-- url     : https://prove2.me/submissions/4b17974e-f6ac-45fe-95cb-6cca87b41b36

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_SecondHermitianPartDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
open scoped ContDiff
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
private lemma sgn_sq_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r i * WeylGroupFacts.sgn k r i = 1 := by
  unfold WeylGroupFacts.sgn
  split_ifs <;> norm_num
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
private lemma single_ct_lemma (a b : Fin (2 * r + k + 1)) (c : ℂ) :
    (Matrix.single a b c)ᴴ = Matrix.single b a (star c) := by
  ext x y
  rw [Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.single_apply]
  by_cases h : a = y ∧ b = x
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩), star_zero]
private lemma conj_single_lemma (A B : Mx k r) (a b : Fin (2 * r + k + 1)) (c : ℂ)
    (p q : Fin (2 * r + k + 1)) : (A * Matrix.single a b c * B) p q = A p a * c * B b q := by
  simp only [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
end PI.QnRT
end
end

set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.QnRT
variable {k r : ℕ}
namespace PI.QnRT
theorem _root_.solution (x : Fin (2 * r + k + 1)) :
    Hpk k r * (single x x (1 : ℂ))ᴴ * Hpk k r =
      single (WeylGroupFacts.tau k r x) (WeylGroupFacts.tau k r x) 1 := by
  rw [single_ct_lemma, star_one]
  ext p q
  rw [conj_single_lemma, hpk_eq_lemma, hpk_col_lemma, Matrix.single_apply]
  by_cases hp : p = WeylGroupFacts.tau k r x
  · subst hp
    by_cases hq : q = WeylGroupFacts.tau k r x
    · subst hq
      simp [tau_tau_lemma, sgn_tau_lemma, sgn_sq_lemma]
    · have hq' : x ≠ WeylGroupFacts.tau k r q := fun h => hq (by rw [h, tau_tau_lemma])
      simp [hq', Ne.symm hq]
  · have hp' : x ≠ WeylGroupFacts.tau k r p := fun h => hp (by rw [h, tau_tau_lemma])
    simp [hp', Ne.symm hp]
end PI.QnRT
