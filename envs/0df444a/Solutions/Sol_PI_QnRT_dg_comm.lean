-- Prove2me | solution 1 for PI.QnRT.dg_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:11:02.881989+00:00
-- url     : https://prove2.me/submissions/0bac5f09-c8ea-4af3-897f-5f3bb92f8b14

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Theorems.Thm_PI_QnRT_tau_e
import Theorems.Thm_PI_QnRT_tau_es
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
private lemma sgn_ne_zero' (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r i ≠ 0 := by
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
private lemma conjTranspose_mul_Hpk_mul_apply (A : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (Aᴴ * Hpk k r * A) p q = ∑ y, star (A (WeylGroupFacts.tau k r y) p) * WeylGroupFacts.sgn k r y * A y q := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, hpk_col_lemma, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
private lemma apply_eq_ite_of_mulVec_bvec_eq (g : Mx k r) (v : Fin (2 * r + k + 1)) (h : g *ᵥ bvec v = bvec v)
    (q : Fin (2 * r + k + 1)) : g q v = if q = v then 1 else 0 := by
  have h' := congrFun h q
  simp only [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h'
  exact h'
private lemma apply_eq_ite_of_isometry_of_tau_column (g : Mx k r) (hg : gᴴ * Hpk k r * g = Hpk k r) (p : Fin (2 * r + k + 1))
    (h : ∀ q, g q (WeylGroupFacts.tau k r p) = if q = WeylGroupFacts.tau k r p then 1 else 0) (q : Fin (2 * r + k + 1)) :
    g p q = if p = q then 1 else 0 := by
  have e := congrFun (congrFun hg q) (WeylGroupFacts.tau k r p)
  rw [conjTranspose_mul_Hpk_mul_apply, hpk_col_lemma, tau_tau_lemma] at e
  simp only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, tau_tau_lemma] at e
  have hs := sgn_ne_zero' (k := k) (r := r) (WeylGroupFacts.tau k r p)
  by_cases hpq : p = q
  · subst hpq
    rw [if_pos rfl] at e
    have h1 : star (g p p) = 1 := mul_right_cancel₀ hs (e.trans (one_mul _).symm)
    have h2 := congrArg star h1
    rw [star_star, star_one] at h2
    simp [h2]
  · rw [if_neg (Ne.symm hpq)] at e
    have h1 : star (g p q) = 0 := (mul_eq_zero.mp e).resolve_right hs
    rw [if_neg hpq]
    exact star_eq_zero.mp h1
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
theorem _root_.solution (l : Fin r) (u v : ℂ) (g₁ : Mx k r) (hg : g₁ ∈ Glev k r l.succ) :
    dg l u v * g₁ = g₁ * dg l u v := by
  have hl := l.isLt
  simp only [Glev, Set.mem_setOf_eq] at hg
  obtain ⟨hU, hfix⟩ := hg
  have hU' : g₁ᴴ * Hpk k r * g₁ = Hpk k r := hU
  have hfe := hfix l (by simp)
  have ce := apply_eq_ite_of_mulVec_bvec_eq g₁ _ hfe.1
  have ces := apply_eq_ite_of_mulVec_bvec_eq g₁ _ hfe.2
  have re : ∀ q, g₁ (eI k r l) q = if eI k r l = q then 1 else 0 :=
    apply_eq_ite_of_isometry_of_tau_column g₁ hU' _ (by rw [tau_e]; exact ces)
  have res : ∀ q, g₁ (esI k r l) q = if esI k r l = q then 1 else 0 :=
    apply_eq_ite_of_isometry_of_tau_column g₁ hU' _ (by rw [tau_es]; exact ce)
  unfold dg
  ext p q
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hp1 : p = eI k r l
  · subst hp1
    rw [re q]
    by_cases hq : eI k r l = q
    · subst hq
      simp [mul_comm]
    · simp [hq]
  by_cases hp2 : p = esI k r l
  · subst hp2
    rw [res q]
    by_cases hq : esI k r l = q
    · subst hq
      simp [mul_comm]
    · simp [hq]
  by_cases hq1 : q = eI k r l
  · subst hq1
    rw [ce p]
    simp [hp1]
  by_cases hq2 : q = esI k r l
  · subst hq2
    rw [ces p]
    simp [hp2]
  simp [hp1, hp2, hq1, hq2]
end PI.QnRT
