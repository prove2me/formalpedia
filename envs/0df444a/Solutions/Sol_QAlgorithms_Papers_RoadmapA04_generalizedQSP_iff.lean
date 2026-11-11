-- Prove2me | solution 1 for QAlgorithms.Papers.RoadmapA04.generalizedQSP_iff
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T16:14:56.796569+00:00
-- url     : https://prove2.me/submissions/ed69d531-0166-4da9-a1f3-2a2d4dfb398c

import Definitions.Def_QAlgorithms_Defs_GeneralizedQSP
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Separation.Connected
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

set_option autoImplicit false
noncomputable section

/- Inlined helper source: P060_Reverse.lean -/

/-!
P060 focused gate. Generic polynomial foundations only; no mission definitions
are replaced here. Drafted against pinned Mathlib source. Until a successful
compiler log is recorded, this file is an uncompiled proof draft.
-/

noncomputable section

open Polynomial
open scoped ComplexConjugate

namespace Prove2Me.S12.GQSP

/-- Reversal at the requested bound, including any leading zero coefficients. -/
def reverseConj (d : ℕ) (P : Polynomial ℂ) : Polynomial ℂ :=
  (P.map (starRingEnd ℂ)).reflect d

theorem reverseConj_natDegree_le {d : ℕ} {P : Polynomial ℂ}
    (hP : P.natDegree ≤ d) : (reverseConj d P).natDegree ≤ d := by
  exact Polynomial.natDegree_reflect_le.trans
    (max_le le_rfl (Polynomial.natDegree_map_le.trans hP))

theorem reverseConj_eval_circle {d : ℕ} (P : Polynomial ℂ)
    (hP : P.natDegree ≤ d) (z : Circle) :
    (reverseConj d P).eval (z : ℂ) = (z : ℂ) ^ d * conj (P.eval (z : ℂ)) := by
  letI : Invertible ((z : ℂ)⁻¹) := invertibleOfNonzero (inv_ne_zero z.coe_ne_zero)
  have hinv : (z : ℂ)⁻¹ = conj (z : ℂ) := z.coe_inv_eq_conj
  have hmap : (P.map (starRingEnd ℂ)).eval ((z : ℂ)⁻¹) =
      conj (P.eval (z : ℂ)) := by
    rw [hinv, Polynomial.eval_map_apply]
  have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) ((z : ℂ)⁻¹) d
    (P.map (starRingEnd ℂ)) (Polynomial.natDegree_map_le.trans hP)
  simp only [Polynomial.eval₂_id, invOf_eq_inv, inv_inv] at h
  rw [hmap] at h
  change (reverseConj d P).eval (z : ℂ) * ((z : ℂ)⁻¹) ^ d =
    conj (P.eval (z : ℂ)) at h
  have hpow : ((z : ℂ)⁻¹) ^ d * (z : ℂ) ^ d = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ z.coe_ne_zero, one_pow]
  calc
    (reverseConj d P).eval (z : ℂ) =
        ((reverseConj d P).eval (z : ℂ) * ((z : ℂ)⁻¹) ^ d) * (z : ℂ) ^ d := by
      rw [mul_assoc, hpow, mul_one]
    _ = conj (P.eval (z : ℂ)) * (z : ℂ) ^ d :=
      congrArg (fun t : ℂ => t * (z : ℂ) ^ d) h
    _ = (z : ℂ) ^ d * conj (P.eval (z : ℂ)) := mul_comm _ _

theorem circle_infinite : Infinite Circle := by
  have hp : IsPreconnected (Set.range (fun t : ℝ => Circle.exp t)) :=
    isPreconnected_range Circle.exp.continuous
  have hnon : (Set.range (fun t : ℝ => Circle.exp t)).Nontrivial := by
    refine ⟨1, ?_, Circle.exp Real.pi, ?_, ?_⟩
    · exact ⟨0, Circle.exp_zero⟩
    · exact ⟨Real.pi, rfl⟩
    · exact Circle.exp_pi_ne_one.symm
  exact Set.infinite_univ_iff.mp
    ((hp.infinite_of_nontrivial hnon).mono (Set.subset_univ _))

theorem norm_identity_complex {p q : ℂ}
    (h : ‖p‖ ^ 2 + ‖q‖ ^ 2 = 1) : p * conj p + q * conj q = 1 := by
  rw [Complex.mul_conj p, Complex.mul_conj q, ← Complex.ofReal_add,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h, Complex.ofReal_one]

/-- The polynomial identity is valid at the requested degree bound, even when
both top coefficients vanish. -/
theorem reverseConj_identity {d : ℕ} (P Q : Polynomial ℂ)
    (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    (hunit : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1) :
    P * reverseConj d P + Q * reverseConj d Q = X ^ d := by
  apply Polynomial.eq_of_infinite_eval_eq
  letI : Infinite Circle := circle_infinite
  refine (Set.infinite_range_of_injective (α := Circle)
    (f := fun z : Circle => (z : ℂ)) Circle.coe_injective).mono ?_
  rintro z ⟨w, rfl⟩
  change (P * reverseConj d P + Q * reverseConj d Q).eval (w : ℂ) =
    (X ^ d : Polynomial ℂ).eval (w : ℂ)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X]
  rw [reverseConj_eval_circle P hP w, reverseConj_eval_circle Q hQ w]
  have hc := norm_identity_complex (hunit (w : ℂ) w.norm_coe)
  calc
    P.eval (w : ℂ) * ((w : ℂ) ^ d * conj (P.eval (w : ℂ))) +
        Q.eval (w : ℂ) * ((w : ℂ) ^ d * conj (Q.eval (w : ℂ))) =
        (w : ℂ) ^ d * (P.eval (w : ℂ) * conj (P.eval (w : ℂ)) +
          Q.eval (w : ℂ) * conj (Q.eval (w : ℂ))) := by
      rw [mul_left_comm (P.eval (w : ℂ)), mul_left_comm (Q.eval (w : ℂ)),
        ← mul_add]
    _ = (w : ℂ) ^ d := by rw [hc, mul_one]

theorem constant_top_orthogonality {n : ℕ} (P Q : Polynomial ℂ)
    (hP : P.natDegree ≤ n + 1) (hQ : Q.natDegree ≤ n + 1)
    (hunit : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1) :
    P.coeff 0 * conj (P.coeff (n + 1)) +
      Q.coeff 0 * conj (Q.coeff (n + 1)) = 0 := by
  have hc := congrArg (fun F : Polynomial ℂ => F.coeff 0)
    (reverseConj_identity P Q hP hQ hunit)
  simpa [reverseConj, Polynomial.mul_coeff_zero, Polynomial.coeff_reflect,
    Polynomial.revAt_zero, Polynomial.coeff_X_pow] using hc

end Prove2Me.S12.GQSP


/- Inlined helper source: P060_DegreeLowering.lean -/

/-!
P060 focused gate: constructive cancellation of the constant and top terms,
including simultaneous vanishing of both top terms. Generic foundations only.
This source is a draft until accompanied by a successful compiler log.
-/

noncomputable section

open Polynomial
open scoped ComplexConjugate

namespace Prove2Me.S12.GQSP

def pairScale (x y : ℂ) : ℂ :=
  (Real.sqrt (Complex.normSq x + Complex.normSq y) : ℝ)

theorem pairScale_conj (x y : ℂ) : conj (pairScale x y) = pairScale x y := by
  simp [pairScale]

theorem pairScale_ne_zero {x y : ℂ} (hxy : x ≠ 0 ∨ y ≠ 0) : pairScale x y ≠ 0 := by
  have hs : 0 < Complex.normSq x + Complex.normSq y := by
    rcases hxy with hx | hy
    · exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr hx) (Complex.normSq_nonneg y)
    · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg x) (Complex.normSq_pos.mpr hy)
  have ht : Real.sqrt (Complex.normSq x + Complex.normSq y) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hs)
  exact Complex.ofReal_ne_zero.mpr ht

theorem pairScale_square (x y : ℂ) :
    pairScale x y * pairScale x y = x * conj x + y * conj y := by
  rw [Complex.mul_conj x, Complex.mul_conj y, ← Complex.ofReal_add]
  change (Real.sqrt (Complex.normSq x + Complex.normSq y) : ℂ) *
    (Real.sqrt (Complex.normSq x + Complex.normSq y) : ℂ) =
      ((Complex.normSq x + Complex.normSq y : ℝ) : ℂ)
  rw [← Complex.ofReal_mul,
    Real.mul_self_sqrt (add_nonneg (Complex.normSq_nonneg x) (Complex.normSq_nonneg y))]

theorem pairScale_normalizes {x y : ℂ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    (x / pairScale x y) * conj (x / pairScale x y) +
      (y / pairScale x y) * conj (y / pairScale x y) = 1 := by
  have ht := pairScale_ne_zero hxy
  simp only [map_div₀, pairScale_conj]
  rw [div_mul_div_comm, div_mul_div_comm, ← add_div, ← pairScale_square,
    div_self (mul_ne_zero ht ht)]

theorem conjugate_ne_zero {x : ℂ} (hx : x ≠ 0) : conj x ≠ 0 := by
  intro hc
  apply hx
  simpa only [map_zero, Complex.conj_conj] using congrArg (starRingEnd ℂ) hc

/-- A normalized direction can simultaneously kill the constant coefficient in
the first inverse-rotated component and the top coefficient in the second.
The construction deliberately handles both top coefficients being zero. -/
theorem exists_rotation_kills_ends (p₀ q₀ ptop qtop : ℂ)
    (horth : p₀ * conj ptop + q₀ * conj qtop = 0) :
    ∃ a b : ℂ, a * conj a + b * conj b = 1 ∧
      conj a * p₀ + conj b * q₀ = 0 ∧ b * ptop - a * qtop = 0 := by
  by_cases htop : ptop = 0 ∧ qtop = 0
  · by_cases hconst : p₀ = 0 ∧ q₀ = 0
    · exact ⟨1, 0, by simp, by simp [hconst.1, hconst.2], by simp [htop.2]⟩
    · have hxy : conj q₀ ≠ 0 ∨ -(conj p₀) ≠ 0 := by
        by_cases hp : p₀ = 0
        · exact Or.inl (conjugate_ne_zero (fun hq => hconst ⟨hp, hq⟩))
        · exact Or.inr (neg_ne_zero.mpr (conjugate_ne_zero hp))
      refine ⟨conj q₀ / pairScale (conj q₀) (-conj p₀),
        -conj p₀ / pairScale (conj q₀) (-conj p₀),
        pairScale_normalizes hxy, ?_, ?_⟩
      · simp only [map_div₀, pairScale_conj, map_neg, Complex.conj_conj]
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
          neg_mul, mul_comm q₀ p₀, add_neg_cancel, zero_div]
      · simp [htop.1, htop.2]
  · have hxy : ptop ≠ 0 ∨ qtop ≠ 0 := by
      by_cases hp : ptop = 0
      · exact Or.inr (fun hq => htop ⟨hp, hq⟩)
      · exact Or.inl hp
    refine ⟨ptop / pairScale ptop qtop, qtop / pairScale ptop qtop,
      pairScale_normalizes hxy, ?_, ?_⟩
    · simp only [map_div₀, pairScale_conj]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
        mul_comm (conj ptop) p₀, mul_comm (conj qtop) q₀, horth, zero_div]
    · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div,
        mul_comm qtop ptop, sub_self, zero_div]

def rotateFirst (a b : ℂ) (P Q : Polynomial ℂ) : Polynomial ℂ :=
  C (conj a) * P + C (conj b) * Q

def rotateSecond (a b : ℂ) (P Q : Polynomial ℂ) : Polynomial ℂ :=
  C b * P - C a * Q

theorem degree_lowering_of_end_cancellation {n : ℕ} (P Q : Polynomial ℂ)
    (hP : P.natDegree ≤ n + 1) (hQ : Q.natDegree ≤ n + 1) (a b : ℂ)
    (hzero : conj a * P.coeff 0 + conj b * Q.coeff 0 = 0)
    (htop : b * P.coeff (n + 1) - a * Q.coeff (n + 1) = 0) :
    (rotateFirst a b P Q).divX.natDegree ≤ n ∧
      (rotateSecond a b P Q).natDegree ≤ n ∧
      X * (rotateFirst a b P Q).divX = rotateFirst a b P Q := by
  have hA : (rotateFirst a b P Q).natDegree ≤ n + 1 :=
    Polynomial.natDegree_add_le_of_degree_le
      ((Polynomial.natDegree_C_mul_le _ _).trans hP)
      ((Polynomial.natDegree_C_mul_le _ _).trans hQ)
  have hB : (rotateSecond a b P Q).natDegree ≤ n + 1 := by
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le ((Polynomial.natDegree_C_mul_le _ _).trans hP)
        ((Polynomial.natDegree_C_mul_le _ _).trans hQ))
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
    simpa only [Nat.add_sub_cancel] using Nat.sub_le_sub_right hA 1
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    by_cases hkn : k = n + 1
    · subst k
      simpa [rotateSecond] using htop
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (hB.trans_lt (lt_of_le_of_ne (Nat.succ_le_of_lt hk) (Ne.symm hkn)))
  · have hA0 : (rotateFirst a b P Q).coeff 0 = 0 := by
      simpa [rotateFirst] using hzero
    simpa only [hA0, map_zero, add_zero] using
      Polynomial.X_mul_divX_add (rotateFirst a b P Q)

/-- An unconditional choice of normalized coefficients and lowered polynomials
from endpoint orthogonality; neither top coefficient is assumed nonzero. -/
theorem exists_degree_lowering {n : ℕ} (P Q : Polynomial ℂ)
    (hP : P.natDegree ≤ n + 1) (hQ : Q.natDegree ≤ n + 1)
    (horth : P.coeff 0 * conj (P.coeff (n + 1)) +
      Q.coeff 0 * conj (Q.coeff (n + 1)) = 0) :
    ∃ a b : ℂ, a * conj a + b * conj b = 1 ∧
      (rotateFirst a b P Q).divX.natDegree ≤ n ∧
      (rotateSecond a b P Q).natDegree ≤ n ∧
      X * (rotateFirst a b P Q).divX = rotateFirst a b P Q := by
  obtain ⟨a, b, hab, hzero, htop⟩ := exists_rotation_kills_ends
    (P.coeff 0) (Q.coeff 0) (P.coeff (n + 1)) (Q.coeff (n + 1)) horth
  exact ⟨a, b, hab, degree_lowering_of_end_cancellation P Q hP hQ a b hzero htop⟩

theorem rotation_reconstruct_first (a b : ℂ) (P Q : Polynomial ℂ)
    (hab : a * conj a + b * conj b = 1) :
    C a * rotateFirst a b P Q + C (conj b) * rotateSecond a b P Q = P := by
  ext k
  simp only [rotateFirst, rotateSecond, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul]
  calc
    a * (conj a * P.coeff k + conj b * Q.coeff k) +
        conj b * (b * P.coeff k - a * Q.coeff k) =
        (a * conj a + b * conj b) * P.coeff k := by ring
    _ = P.coeff k := by rw [hab, one_mul]

theorem rotation_reconstruct_second (a b : ℂ) (P Q : Polynomial ℂ)
    (hab : a * conj a + b * conj b = 1) :
    C b * rotateFirst a b P Q - C (conj a) * rotateSecond a b P Q = Q := by
  ext k
  simp only [rotateFirst, rotateSecond, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul]
  calc
    b * (conj a * P.coeff k + conj b * Q.coeff k) -
        conj a * (b * P.coeff k - a * Q.coeff k) =
        (a * conj a + b * conj b) * Q.coeff k := by ring
    _ = Q.coeff k := by rw [hab, one_mul]

theorem rotation_preserves_conjugate_sum (a b p q : ℂ)
    (hab : a * conj a + b * conj b = 1) :
    (conj a * p + conj b * q) * conj (conj a * p + conj b * q) +
      (b * p - a * q) * conj (b * p - a * q) = p * conj p + q * conj q := by
  simp only [map_add, map_sub, map_mul, Complex.conj_conj]
  calc
    _ = (a * conj a + b * conj b) * (p * conj p + q * conj q) := by ring
    _ = p * conj p + q * conj q := by rw [hab, one_mul]

theorem rotation_preserves_norm (a b p q : ℂ)
    (hab : a * conj a + b * conj b = 1) :
    ‖conj a * p + conj b * q‖ ^ 2 + ‖b * p - a * q‖ ^ 2 =
      ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
  have h := rotation_preserves_conjugate_sum a b p q hab
  simp only [Complex.mul_conj, ← Complex.ofReal_add, Complex.normSq_eq_norm_sq] at h
  exact Complex.ofReal_injective h

/-- A full generic unitary degree step: both lowered degree bounds, recovery of
the original pair, and the same unit-circle norm identity. The remaining bridge
to the mission is the exact real-angle convention for `gqspRotation`. -/
theorem exists_unitary_degree_step {n : ℕ} (P Q : Polynomial ℂ)
    (hP : P.natDegree ≤ n + 1) (hQ : Q.natDegree ≤ n + 1)
    (horth : P.coeff 0 * conj (P.coeff (n + 1)) +
      Q.coeff 0 * conj (Q.coeff (n + 1)) = 0)
    (hunit : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1) :
    ∃ (a b : ℂ) (R S : Polynomial ℂ),
      a * conj a + b * conj b = 1 ∧ R.natDegree ≤ n ∧ S.natDegree ≤ n ∧
      P = C a * (X * R) + C (conj b) * S ∧
      Q = C b * (X * R) - C (conj a) * S ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖R.eval z‖ ^ 2 + ‖S.eval z‖ ^ 2 = 1 := by
  obtain ⟨a, b, hab, hR, hS, hfactor⟩ := exists_degree_lowering P Q hP hQ horth
  refine ⟨a, b, (rotateFirst a b P Q).divX, rotateSecond a b P Q,
    hab, hR, hS, ?_, ?_, ?_⟩
  · rw [hfactor]
    exact (rotation_reconstruct_first a b P Q hab).symm
  · rw [hfactor]
    exact (rotation_reconstruct_second a b P Q hab).symm
  · intro z hz
    have hnorm : ‖(rotateFirst a b P Q).eval z‖ =
        ‖((rotateFirst a b P Q).divX).eval z‖ := by
      have heval := congrArg (Polynomial.eval z) hfactor
      have hevalnorm := congrArg (fun c : ℂ => ‖c‖) heval
      simpa only [Polynomial.eval_mul, Polynomial.eval_X, norm_mul, hz, one_mul]
        using hevalnorm.symm
    have hrot : ‖(rotateFirst a b P Q).eval z‖ ^ 2 +
        ‖(rotateSecond a b P Q).eval z‖ ^ 2 = ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 := by
      simpa only [rotateFirst, rotateSecond, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_C] using
        rotation_preserves_norm a b (P.eval z) (Q.eval z) hab
    rw [hnorm] at hrot
    exact hrot.trans (hunit z hz)

end Prove2Me.S12.GQSP


/- Inlined helper source: P060_PhaseBridge.lean -/

/-!
Scalar phase bridge for P060's literal rotation convention. No mission object
is redefined. Draft pending compilation with the other focused gate sources.
-/

noncomputable section
open scoped ComplexConjugate

namespace Prove2Me.S12.GQSP

def phase (t : ℝ) : ℂ := Complex.exp (Complex.I * (t : ℂ))

theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal t

theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp only [phase, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem phase_conj (t : ℝ) : conj (phase t) = phase (-t) := by
  simp only [phase, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal, Complex.ofReal_neg, neg_mul, mul_neg]

theorem phase_polar (z : ℂ) : (‖z‖ : ℂ) * phase z.arg = z := by
  unfold phase
  rw [mul_comm Complex.I]
  exact Complex.norm_mul_exp_arg_mul_I z

theorem phase_conjugate_polar (z : ℂ) : (‖z‖ : ℂ) * phase (-z.arg) = conj z := by
  have h := congrArg (starRingEnd ℂ) (phase_polar z)
  simpa only [map_mul, Complex.conj_ofReal, phase_conj] using h

/-- A generic normalized two-component complex direction has the exact
`gqspRotation theta phi 0` convention after multiplying the two input
components by independent phases. The formulas also cover zero components. -/
theorem real_angle_factorization (a b : ℂ)
    (hnorm : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    ∃ theta phi : ℝ, ∃ u v : ℂ, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      a = phase phi * (Real.cos theta : ℂ) * u ∧
      conj b = phase phi * (Real.sin theta : ℂ) * v ∧
      b = (Real.sin theta : ℂ) * u ∧
      conj a = (Real.cos theta : ℂ) * v := by
  have ha2 : ‖a‖ ^ 2 ≤ 1 := by
    rw [← hnorm]
    exact le_add_of_nonneg_right (sq_nonneg ‖b‖)
  have ha1 : ‖a‖ ≤ 1 := by
    simpa only [abs_of_nonneg (norm_nonneg a)] using
      (sq_le_one_iff_abs_le_one ‖a‖).mp ha2
  have hcos : Real.cos (Real.arccos ‖a‖) = ‖a‖ :=
    Real.cos_arccos ((neg_nonpos.mpr (zero_le_one : (0 : ℝ) ≤ 1)).trans
      (norm_nonneg a)) ha1
  have hsquare : 1 - ‖a‖ ^ 2 = ‖b‖ ^ 2 := by
    apply sub_eq_iff_eq_add.mpr
    rw [add_comm]
    exact hnorm.symm
  have hsin : Real.sin (Real.arccos ‖a‖) = ‖b‖ := by
    rw [Real.sin_arccos, hsquare, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg b)]
  have hphase1 : phase (a.arg - b.arg) * phase b.arg = phase a.arg := by
    rw [← phase_add, sub_add_cancel]
  have hphase2 : phase (a.arg - b.arg) * phase (-a.arg) = phase (-b.arg) := by
    rw [← phase_add]
    congr 1
    ring
  refine ⟨Real.arccos ‖a‖, a.arg - b.arg, phase b.arg, phase (-a.arg),
    phase_norm _, phase_norm _, ?_, ?_, ?_, ?_⟩
  · symm
    rw [hcos, mul_right_comm (phase (a.arg - b.arg)) (‖a‖ : ℂ) (phase b.arg),
      hphase1, mul_comm]
    exact phase_polar a
  · symm
    rw [hsin, mul_right_comm (phase (a.arg - b.arg)) (‖b‖ : ℂ) (phase (-a.arg)),
      hphase2, mul_comm]
    exact phase_conjugate_polar b
  · rw [hsin]
    exact (phase_polar b).symm
  · rw [hcos]
    exact (phase_conjugate_polar a).symm

end Prove2Me.S12.GQSP


/- Inlined helper source: P060_ExactStep_body.lean -/
/-!
Assembly body: requires P060_Reverse, P060_DegreeLowering, and P060_PhaseBridge.
No proof holes. No mission definitions are replaced. P060_Gate.lean combines
these sources into a single directly compilable file.
-/

namespace Prove2Me.S12.GQSP

/-- The literal scalar-polynomial recurrence for the mission's final
`gqspRotation theta phi 0` followed by its signal factor. -/
theorem exact_real_angle_degree_step {n : ℕ} (P Q : Polynomial ℂ)
    (hP : P.natDegree ≤ n + 1) (hQ : Q.natDegree ≤ n + 1)
    (hunit : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1) :
    ∃ theta phi : ℝ, ∃ R S : Polynomial ℂ,
      R.natDegree ≤ n ∧ S.natDegree ≤ n ∧
      P = Polynomial.C (phase phi * (Real.cos theta : ℂ)) * (Polynomial.X * R) +
        Polynomial.C (phase phi * (Real.sin theta : ℂ)) * S ∧
      Q = Polynomial.C (Real.sin theta : ℂ) * (Polynomial.X * R) -
        Polynomial.C (Real.cos theta : ℂ) * S ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖R.eval z‖ ^ 2 + ‖S.eval z‖ ^ 2 = 1 := by
  obtain ⟨a, b, R, S, hab, hR, hS, hPrec, hQrec, hRS⟩ :=
    exists_unitary_degree_step P Q hP hQ
      (constant_top_orthogonality P Q hP hQ hunit) hunit
  have hnorm : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := by
    apply Complex.ofReal_injective
    simpa only [Complex.mul_conj, ← Complex.ofReal_add, Complex.normSq_eq_norm_sq,
      Complex.ofReal_one] using hab
  obtain ⟨theta, phi, u, v, hu, hv, ha, hbc, hb, hac⟩ :=
    real_angle_factorization a b hnorm
  refine ⟨theta, phi, Polynomial.C u * R, Polynomial.C v * S,
    (Polynomial.natDegree_C_mul_le _ _).trans hR,
    (Polynomial.natDegree_C_mul_le _ _).trans hS, ?_, ?_, ?_⟩
  · rw [hPrec, ha, hbc]
    simp only [map_mul]
    ring
  · rw [hQrec, hb, hac]
    simp only [map_mul]
    ring
  · intro z hz
    simpa only [Polynomial.eval_mul, Polynomial.eval_C, norm_mul, hu, hv, one_mul]
      using hRS z hz

end Prove2Me.S12.GQSP


/- Inlined helper source: P060_PolyPair_body.lean -/
/-! Auxiliary scalar-polynomial recursion for the unchanged P060 sequence.
Append after the phase declaration. This does not replace any mission definition.
-/

noncomputable section

namespace Prove2Me.S12.GQSP

open Polynomial

/-- The exact first-column polynomial recurrence, with the last angle acting
on the left and the initial lambda used only at depth zero. -/
def qspPolyPair : (d : ℕ) → (Fin (d + 1) → ℝ) → (Fin (d + 1) → ℝ) → ℝ →
    Polynomial ℂ × Polynomial ℂ
  | 0, theta, phi, lam =>
      (C (phase (lam + phi 0) * (Real.cos (theta 0) : ℂ)),
       C (phase lam * (Real.sin (theta 0) : ℂ)))
  | d + 1, theta, phi, lam =>
      let prev := qspPolyPair d (fun j => theta j.castSucc) (fun j => phi j.castSucc) lam
      let t := theta (Fin.last (d + 1))
      let p := phi (Fin.last (d + 1))
      (C (phase p * (Real.cos t : ℂ)) * (X * prev.1) +
        C (phase p * (Real.sin t : ℂ)) * prev.2,
       C (Real.sin t : ℂ) * (X * prev.1) - C (Real.cos t : ℂ) * prev.2)

@[simp] theorem qspPolyPair_zero (theta phi : Fin 1 → ℝ) (lam : ℝ) :
    qspPolyPair 0 theta phi lam =
      (C (phase (lam + phi 0) * (Real.cos (theta 0) : ℂ)),
       C (phase lam * (Real.sin (theta 0) : ℂ))) := rfl

theorem qspPolyPair_succ (d : ℕ) (theta phi : Fin (d + 1 + 1) → ℝ) (lam : ℝ) :
    qspPolyPair (d + 1) theta phi lam =
      let prev := qspPolyPair d (fun j => theta j.castSucc) (fun j => phi j.castSucc) lam
      let t := theta (Fin.last (d + 1))
      let p := phi (Fin.last (d + 1))
      (C (phase p * (Real.cos t : ℂ)) * (X * prev.1) +
        C (phase p * (Real.sin t : ℂ)) * prev.2,
       C (Real.sin t : ℂ) * (X * prev.1) - C (Real.cos t : ℂ) * prev.2) := rfl

end Prove2Me.S12.GQSP

end

/- Inlined helper source: P060_Synthesis_body.lean -/
/-! Reverse synthesis through the auxiliary exact polynomial recurrence.
Requires the checked degree-step/phase gate and P060_PolyPair_body.lean.
Draft until accompanied by a successful canonical compiler log.
-/

noncomputable section

namespace Prove2Me.S12.GQSP

open Polynomial

/-- Exact depth-zero angles, including either zero component. The lower entry
has phase lambda, as in the literal mission rotation. -/
theorem constant_real_angles (p q : ℂ)
    (hnorm : ‖p‖ ^ 2 + ‖q‖ ^ 2 = 1) :
    ∃ theta phi lam : ℝ,
      p = phase (lam + phi) * (Real.cos theta : ℂ) ∧
      q = phase lam * (Real.sin theta : ℂ) := by
  obtain ⟨theta, phi, u, v, hu, _hv, hp, _hqc, hq, _hpc⟩ :=
    real_angle_factorization p q hnorm
  have huarg : phase u.arg = u := by
    simpa only [hu, Complex.ofReal_one, one_mul] using phase_polar u
  refine ⟨theta, phi, u.arg, ?_, ?_⟩
  · rw [phase_add, huarg]
    calc
      p = phase phi * (Real.cos theta : ℂ) * u := hp
      _ = u * phase phi * (Real.cos theta : ℂ) := by ac_rfl
  · rw [huarg]
    exact hq.trans (mul_comm _ _)

/-- A degree-zero normalized pair is represented by one literal initial
rotation. No nonzero coefficient hypothesis is used. -/
theorem synthesize_degree_zero (P Q : Polynomial ℂ)
    (hP : P.natDegree ≤ 0) (hQ : Q.natDegree ≤ 0)
    (hunit : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1) :
    ∃ theta phi : Fin 1 → ℝ, ∃ lam : ℝ,
      qspPolyPair 0 theta phi lam = (P, Q) := by
  have hPc : P = C (P.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hP
  have hQc : Q = C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hQ
  have hnorm : ‖P.coeff 0‖ ^ 2 + ‖Q.coeff 0‖ ^ 2 = 1 := by
    have h := hunit 1 (norm_one : ‖(1 : ℂ)‖ = 1)
    rw [hPc, hQc] at h
    simpa only [Polynomial.eval_C] using h
  obtain ⟨theta, phi, lam, hp, hq⟩ := constant_real_angles (P.coeff 0) (Q.coeff 0) hnorm
  refine ⟨fun _ => theta, fun _ => phi, lam, ?_⟩
  simp only [qspPolyPair_zero]
  rw [← hp, ← hq, ← hPc, ← hQc]

/-- Reverse synthesis with exactly d signal factors. The degree step handles
leading zero coefficients, so padding to the requested d is built into the
induction rather than inferred from a generic top-degree argument. -/
theorem synthesize_polynomial_pair (d : ℕ) (P Q : Polynomial ℂ)
    (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    (hunit : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1) :
    ∃ theta phi : Fin (d + 1) → ℝ, ∃ lam : ℝ,
      qspPolyPair d theta phi lam = (P, Q) := by
  induction d generalizing P Q with
  | zero => exact synthesize_degree_zero P Q hP hQ hunit
  | succ d ih =>
    obtain ⟨thetaLast, phiLast, R, S, hR, hS, hp, hq, hRS⟩ :=
      exact_real_angle_degree_step P Q hP hQ hunit
    obtain ⟨theta, phi, lam, hprev⟩ := ih R S hR hS hRS
    refine ⟨Fin.snoc theta thetaLast, Fin.snoc phi phiLast, lam, ?_⟩
    rw [qspPolyPair_succ]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, hprev]
    exact Prod.ext hp.symm hq.symm

end Prove2Me.S12.GQSP

end


/- Inlined helper source: P060_MatrixTransport_body.lean -/
/-! Transport the auxiliary polynomial recursion to the unchanged matrix sequence. -/

namespace Prove2Me.S12.GQSP

open QAlgorithms Polynomial
open scoped Matrix Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gqspSequence_succ (d : ℕ) (theta phi : Fin (d + 1 + 1) → ℝ)
    (lam : ℝ) (U : Matrix ι ι ℂ) :
    gqspSequence theta phi lam U =
      (Matrix.kronecker
        (gqspRotation (theta (Fin.last (d + 1))) (phi (Fin.last (d + 1))) 0) 1 *
          gqspSignal U) *
      gqspSequence (fun j : Fin (d + 1) => theta j.castSucc)
        (fun j : Fin (d + 1) => phi j.castSucc) lam U := by
  unfold gqspSequence orderedProd
  rw [List.ofFn_succ', List.concat_eq_append, List.reverse_concat,
    List.prod_cons, mul_assoc]
  rfl

theorem kronecker_one_mul_entry (A : Matrix Bool Bool ℂ)
    (B : Matrix (Bool × ι) (Bool × ι) ℂ) (a b : Bool) (i j : ι) :
    (Matrix.kronecker A (1 : Matrix ι ι ℂ) * B) (a, i) (b, j) =
      A a false * B (false, i) (b, j) + A a true * B (true, i) (b, j) := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Matrix.one_apply, mul_ite, ite_mul, add_comm]

theorem signal_mul_false_entry (U : Matrix ι ι ℂ)
    (B : Matrix (Bool × ι) (Bool × ι) ℂ) (b : Bool) (i j : ι) :
    (gqspSignal U * B) (false, i) (b, j) =
      ∑ k, U i k * B (false, k) (b, j) := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, gqspSignal]

theorem signal_mul_true_entry (U : Matrix ι ι ℂ)
    (B : Matrix (Bool × ι) (Bool × ι) ℂ) (b : Bool) (i j : ι) :
    (gqspSignal U * B) (true, i) (b, j) = B (true, i) (b, j) := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, gqspSignal, Matrix.one_apply]

theorem step_mul_false_entry (theta phi : ℝ) (U : Matrix ι ι ℂ)
    (B : Matrix (Bool × ι) (Bool × ι) ℂ) (b : Bool) (i j : ι) :
    ((Matrix.kronecker (gqspRotation theta phi 0) (1 : Matrix ι ι ℂ) * gqspSignal U) * B)
        (false, i) (b, j) =
      (phase phi * (Real.cos theta : ℂ)) * (∑ k, U i k * B (false, k) (b, j)) +
        (phase phi * (Real.sin theta : ℂ)) * B (true, i) (b, j) := by
  rw [mul_assoc, kronecker_one_mul_entry, signal_mul_false_entry, signal_mul_true_entry]
  simp [gqspRotation, phase]

theorem step_mul_true_entry (theta phi : ℝ) (U : Matrix ι ι ℂ)
    (B : Matrix (Bool × ι) (Bool × ι) ℂ) (b : Bool) (i j : ι) :
    ((Matrix.kronecker (gqspRotation theta phi 0) (1 : Matrix ι ι ℂ) * gqspSignal U) * B)
        (true, i) (b, j) =
      (Real.sin theta : ℂ) * (∑ k, U i k * B (false, k) (b, j)) -
        (Real.cos theta : ℂ) * B (true, i) (b, j) := by
  rw [mul_assoc, kronecker_one_mul_entry, signal_mul_false_entry, signal_mul_true_entry]
  simp [gqspRotation, sub_eq_add_neg]

theorem matrix_aeval_C_mul (U : Matrix ι ι ℂ) (a : ℂ) (P : Polynomial ℂ) :
    Polynomial.aeval U (C a * P) = a • Polynomial.aeval U P := by
  rw [map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul]

theorem matrix_aeval_X_mul (U : Matrix ι ι ℂ) (P : Polynomial ℂ) :
    Polynomial.aeval U (X * P) = U * Polynomial.aeval U P := by
  rw [map_mul, Polynomial.aeval_X]

theorem qspPolyPair_matrix_column (d : ℕ) (theta phi : Fin (d + 1) → ℝ)
    (lam : ℝ) (U : Matrix ι ι ℂ) (i j : ι) :
    gqspSequence theta phi lam U (false, i) (false, j) =
        (Polynomial.aeval U (qspPolyPair d theta phi lam).1) i j ∧
      gqspSequence theta phi lam U (true, i) (false, j) =
        (Polynomial.aeval U (qspPolyPair d theta phi lam).2) i j := by
  induction d generalizing i j with
  | zero =>
    constructor <;>
      simp [gqspSequence, orderedProd, qspPolyPair, gqspRotation, phase,
        Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
        Matrix.kronecker_apply, Matrix.one_apply, mul_ite, mul_comm]
  | succ d ih =>
    let th : Fin (d + 1) → ℝ := fun k => theta k.castSucc
    let ph : Fin (d + 1) → ℝ := fun k => phi k.castSucc
    have htop : ∀ a b, gqspSequence th ph lam U (false, a) (false, b) =
        (Polynomial.aeval U (qspPolyPair d th ph lam).1) a b :=
      fun a b => (ih th ph a b).1
    have hbottom : ∀ a b, gqspSequence th ph lam U (true, a) (false, b) =
        (Polynomial.aeval U (qspPolyPair d th ph lam).2) a b :=
      fun a b => (ih th ph a b).2
    dsimp only [th, ph] at htop hbottom
    rw [gqspSequence_succ, qspPolyPair_succ]
    change _ = _ ∧ _ = _
    constructor
    · rw [step_mul_false_entry]
      simp only [map_add]
      rw [matrix_aeval_C_mul, matrix_aeval_C_mul, matrix_aeval_X_mul]
      simp_rw [htop, hbottom]
      rfl
    · rw [step_mul_true_entry]
      simp only [map_sub]
      rw [matrix_aeval_C_mul, matrix_aeval_C_mul, matrix_aeval_X_mul]
      simp_rw [htop, hbottom]
      rfl

end Prove2Me.S12.GQSP


/- Inlined helper source: P060_RotationNorm_body.lean -/
/-! The scalar norm identity for the mission's lambda=0 rotation convention.
Append after the checked P060_Gate.lean declarations. -/

namespace Prove2Me.S12.GQSP

open scoped ComplexConjugate

theorem forward_rotation_norm (t p : ℝ) (x y : ℂ) :
    ‖phase p * (Real.cos t : ℂ) * x + phase p * (Real.sin t : ℂ) * y‖ ^ 2 +
      ‖(Real.sin t : ℂ) * x - (Real.cos t : ℂ) * y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have hab : (Real.cos t : ℂ) * conj (Real.cos t : ℂ) +
      (Real.sin t : ℂ) * conj (Real.sin t : ℂ) = 1 := by
    simpa only [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_add,
      pow_two, Complex.ofReal_one] using
      congrArg (fun r : ℝ => (r : ℂ)) (Real.cos_sq_add_sin_sq t)
  have hfirst : phase p * (Real.cos t : ℂ) * x + phase p * (Real.sin t : ℂ) * y =
      phase p * ((Real.cos t : ℂ) * x + (Real.sin t : ℂ) * y) := by
    simp only [mul_add, mul_assoc]
  rw [hfirst, norm_mul, phase_norm, one_mul]
  simpa only [Complex.conj_ofReal] using
    rotation_preserves_norm (Real.cos t : ℂ) (Real.sin t : ℂ) x y hab

end Prove2Me.S12.GQSP


/- Inlined helper source: P060_ForwardScalar_body.lean -/
/-! Scalar probes for the exact P060 forward implication.
Requires the checked circle_infinite helper and the standard Matrix/aeval imports.
-/

namespace Prove2Me.S12.GQSP

theorem forward_scalar_unitary (z : ℂ) (hz : ‖z‖ = 1) :
    algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ) z ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext i j
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  subst j
  simp [Matrix.mul_apply, Matrix.star_apply, Matrix.algebraMap_matrix_apply,
    Matrix.one_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]

theorem forward_aeval_scalar (z : ℂ) (P : Polynomial ℂ) :
    (Polynomial.aeval (algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ) z) P)
      (0 : Fin 1) (0 : Fin 1) = P.eval z := by
  rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
  simp [Matrix.algebraMap_matrix_apply]

theorem forward_polynomial_eq_of_circle (P Q : Polynomial ℂ)
    (h : ∀ z : Circle, P.eval (z : ℂ) = Q.eval (z : ℂ)) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  letI : Infinite Circle := circle_infinite
  refine (Set.infinite_range_of_injective (α := Circle)
    (f := fun z : Circle => (z : ℂ)) Circle.coe_injective).mono ?_
  rintro z ⟨w, rfl⟩
  exact h w

end Prove2Me.S12.GQSP


/- Inlined helper source: P060_Forward_body.lean -/
/-!
Forward invariants and the exact universal-realization implication for P060.
Append after the checked gate, qspPolyPair, matrix-column transport, rotation
norm helper, and ForwardScalar helpers. No mission definition is replaced.
-/

noncomputable section

namespace Prove2Me.S12.GQSP

open Polynomial

theorem qspPolyPair_natDegree_le (d : ℕ) (theta phi : Fin (d + 1) → ℝ) (lam : ℝ) :
    (qspPolyPair d theta phi lam).1.natDegree ≤ d ∧
      (qspPolyPair d theta phi lam).2.natDegree ≤ d := by
  induction d with
  | zero =>
      simp only [qspPolyPair_zero, Polynomial.natDegree_C, le_refl, and_self]
  | succ d ih =>
      let prev := qspPolyPair d (fun j => theta j.castSucc) (fun j => phi j.castSucc) lam
      have hp := ih (fun j => theta j.castSucc) (fun j => phi j.castSucc)
      change prev.1.natDegree ≤ d ∧ prev.2.natDegree ≤ d at hp
      have hXP : (X * prev.1).natDegree ≤ d + 1 := by
        calc
          (X * prev.1).natDegree ≤ (X : Polynomial ℂ).natDegree + prev.1.natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ 1 + d := by
            simpa only [Polynomial.natDegree_X] using Nat.add_le_add_left hp.1 1
          _ = d + 1 := Nat.add_comm 1 d
      have hQ : prev.2.natDegree ≤ d + 1 := hp.2.trans (Nat.le_succ d)
      rw [qspPolyPair_succ]
      dsimp only
      refine ⟨Polynomial.natDegree_add_le_of_degree_le ?_ ?_, ?_⟩
      · exact (Polynomial.natDegree_C_mul_le _ _).trans hXP
      · exact (Polynomial.natDegree_C_mul_le _ _).trans hQ
      · exact (Polynomial.natDegree_sub_le _ _).trans
          (max_le ((Polynomial.natDegree_C_mul_le _ _).trans hXP)
            ((Polynomial.natDegree_C_mul_le _ _).trans hQ))

theorem qspPolyPair_norm_identity (d : ℕ) (theta phi : Fin (d + 1) → ℝ)
    (lam : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(qspPolyPair d theta phi lam).1.eval z‖ ^ 2 +
      ‖(qspPolyPair d theta phi lam).2.eval z‖ ^ 2 = 1 := by
  induction d with
  | zero =>
      simpa only [qspPolyPair_zero, Polynomial.eval_C, norm_mul, phase_norm, one_mul,
        Complex.norm_real, Real.norm_eq_abs, sq_abs] using
        Real.cos_sq_add_sin_sq (theta 0)
  | succ d ih =>
      rw [qspPolyPair_succ]
      dsimp only
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      rw [forward_rotation_norm]
      simpa only [norm_mul, hz, one_mul] using
        ih (fun j => theta j.castSucc) (fun j => phi j.castSucc)

open QAlgorithms

/-- The left-to-right implication retains the published quantifiers: the same
angles realize the prescribed pair in every positive finite dimension. Only
dimension one is needed to identify the scalar polynomials uniquely. -/
theorem generalizedQSP_forward (d : ℕ) (P Q : Polynomial ℂ)
    (hrealize : ∃ theta phi : Fin (d + 1) → ℝ, ∃ lam : ℝ,
      ∀ N : ℕ, 0 < N → ∀ U : Matrix (Fin N) (Fin N) ℂ,
        U ∈ Matrix.unitaryGroup (Fin N) ℂ → ∀ i j : Fin N,
          gqspSequence theta phi lam U (false, i) (false, j) =
            (Polynomial.aeval U P) i j ∧
          gqspSequence theta phi lam U (true, i) (false, j) =
            (Polynomial.aeval U Q) i j) :
    P.natDegree ≤ d ∧ Q.natDegree ≤ d ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1 := by
  obtain ⟨theta, phi, lam, hrealize⟩ := hrealize
  have heval (z : Circle) :
      P.eval (z : ℂ) = (qspPolyPair d theta phi lam).1.eval (z : ℂ) ∧
      Q.eval (z : ℂ) = (qspPolyPair d theta phi lam).2.eval (z : ℂ) := by
    let U : Matrix (Fin 1) (Fin 1) ℂ :=
      algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ) (z : ℂ)
    have hU : U ∈ Matrix.unitaryGroup (Fin 1) ℂ :=
      forward_scalar_unitary (z : ℂ) z.norm_coe
    have htarget := hrealize 1 (by decide) U hU 0 0
    have hcolumn := qspPolyPair_matrix_column d theta phi lam U (0 : Fin 1) (0 : Fin 1)
    constructor
    · simpa only [U, forward_aeval_scalar] using htarget.1.symm.trans hcolumn.1
    · simpa only [U, forward_aeval_scalar] using htarget.2.symm.trans hcolumn.2
  have hP : P = (qspPolyPair d theta phi lam).1 :=
    forward_polynomial_eq_of_circle P _ (fun z => (heval z).1)
  have hQ : Q = (qspPolyPair d theta phi lam).2 :=
    forward_polynomial_eq_of_circle Q _ (fun z => (heval z).2)
  rw [hP, hQ]
  have hdegree := qspPolyPair_natDegree_le d theta phi lam
  exact ⟨hdegree.1, hdegree.2, qspPolyPair_norm_identity d theta phi lam⟩

end Prove2Me.S12.GQSP

end


/- Inlined helper source: P060_Root_body.lean -/
open QAlgorithms

theorem solution (d : ℕ) (P Q : Polynomial ℂ) :
    (∃ theta phi : Fin (d + 1) → ℝ, ∃ lam : ℝ,
      ∀ N : ℕ, 0 < N → ∀ U : Matrix (Fin N) (Fin N) ℂ,
        U ∈ Matrix.unitaryGroup (Fin N) ℂ → ∀ i j : Fin N,
          gqspSequence theta phi lam U (false, i) (false, j) =
            (Polynomial.aeval U P) i j ∧
          gqspSequence theta phi lam U (true, i) (false, j) =
            (Polynomial.aeval U Q) i j) ↔
      P.natDegree ≤ d ∧ Q.natDegree ≤ d ∧
        ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1  := by
  constructor
  · intro hrealize
    exact Prove2Me.S12.GQSP.generalizedQSP_forward d P Q hrealize
  · rintro ⟨hP, hQ, hunit⟩
    obtain ⟨theta, phi, lam, hpair⟩ :=
      Prove2Me.S12.GQSP.synthesize_polynomial_pair d P Q hP hQ hunit
    refine ⟨theta, phi, lam, ?_⟩
    intro N _hN U _hU i j
    simpa only [hpair] using
      Prove2Me.S12.GQSP.qspPolyPair_matrix_column d theta phi lam U i j

#print axioms solution
