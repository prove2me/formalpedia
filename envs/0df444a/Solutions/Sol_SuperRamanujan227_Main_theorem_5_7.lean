-- Prove2me | solution 1 for SuperRamanujan227.Main.theorem_5_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:11:54.251543+00:00
-- url     : https://prove2.me/submissions/5a2e25f2-d342-4fb4-b4ed-f0e5f3d4e286

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Spectra
import Definitions.Def_SuperRamanujan227_Main_Jacobi
section
set_option autoImplicit false
open Polynomial

namespace SuperRamanujan227.Dev.Base
open SuperRamanujan227.Main

lemma alpha1_def (P : ℝ[X]) : kthLargestRoot P 1 = (P.roots.sort (· ≥ ·)).getD 0 0 := by
  simp [kthLargestRoot]

lemma sort_cons_form {P : ℝ[X]} (hne : P.roots ≠ 0) :
    ∃ a l, P.roots.sort (· ≥ ·) = a :: l := by
  have hlen : (P.roots.sort (· ≥ ·)).length ≠ 0 := by
    rw [Multiset.length_sort]; simpa using hne
  cases hl : P.roots.sort (· ≥ ·) with
  | nil => rw [hl] at hlen; simp at hlen
  | cons a l => exact ⟨a, l, rfl⟩

lemma alpha1_mem {P : ℝ[X]} (hne : P.roots ≠ 0) : kthLargestRoot P 1 ∈ P.roots := by
  rw [alpha1_def]
  obtain ⟨a, l, hl⟩ := sort_cons_form hne
  rw [hl]
  simp only [List.getD_cons_zero]
  rw [← Multiset.mem_sort (· ≥ ·), hl]
  simp

lemma le_alpha1 {P : ℝ[X]} (hne : P.roots ≠ 0) : ∀ r ∈ P.roots, r ≤ kthLargestRoot P 1 := by
  intro r hr
  rw [alpha1_def]
  obtain ⟨a, l, hl⟩ := sort_cons_form hne
  have hp := Multiset.pairwise_sort P.roots (· ≥ ·)
  rw [hl] at hp
  have hr' : r ∈ a :: l := by rw [← hl]; exact (Multiset.mem_sort (· ≥ ·)).mpr hr
  rw [hl]
  simp only [List.getD_cons_zero]
  rcases List.mem_cons.mp hr' with h | h
  · rw [h]
  · exact (List.pairwise_cons.mp hp).1 r h

lemma rr_roots_ne {P : ℝ[X]} (hP : RealRooted P) (h1 : 1 ≤ P.natDegree) : P.roots ≠ 0 := by
  intro h
  have := hP.2
  rw [h] at this
  simp at this
  omega

lemma prod_pos (s : Multiset ℝ) (x : ℝ) (hx : ∀ r ∈ s, r < x) :
    0 < (s.map (fun r => (X - C r : ℝ[X]))).prod.eval x ∧
      (s ≠ 0 → 0 < (derivative (s.map (fun r => (X - C r : ℝ[X]))).prod).eval x) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have hax : a < x := hx a (Multiset.mem_cons_self a s)
    have ih' := ih (fun r hr => hx r (Multiset.mem_cons_of_mem hr))
    obtain ⟨h1, h2⟩ := ih'
    simp only [Multiset.map_cons, Multiset.prod_cons]
    refine ⟨?_, fun _ => ?_⟩
    · simp only [eval_mul, eval_sub, eval_X, eval_C]
      exact mul_pos (by linarith) h1
    · rw [derivative_mul]
      simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, derivative_sub, derivative_X,
        derivative_C, sub_zero, eval_one, one_mul]
      by_cases hs : s = 0
      · subst hs; simp
      · have := h2 hs
        have := mul_pos (sub_pos.mpr hax) this
        nlinarith [h1]

lemma pos_beyond {P : ℝ[X]} (hP : RealRooted P) (x : ℝ) (hx : ∀ r ∈ P.roots, r < x) :
    0 < P.leadingCoeff * P.eval x ∧
      (1 ≤ P.natDegree → 0 < P.leadingCoeff * (derivative P).eval x) := by
  have hP0 := hP.1
  have hne : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP0
  have heq : P = C P.leadingCoeff * (P.roots.map (fun r => (X - C r : ℝ[X]))).prod :=
    (C_leadingCoeff_mul_prod_multiset_X_sub_C hP.2).symm
  obtain ⟨h1, h2⟩ := prod_pos P.roots x hx
  have hd0 : 1 ≤ P.natDegree → P.roots ≠ 0 := rr_roots_ne hP
  generalize (P.roots.map (fun r => (X - C r : ℝ[X]))).prod = Q at heq h1 h2
  generalize P.leadingCoeff = c at heq hne
  have hlc : 0 < c * c := mul_self_pos.mpr hne
  have hd0' : P.roots ≠ 0 → 0 < (derivative Q).eval x := h2
  constructor
  · rw [heq]
    simp only [eval_mul, eval_C]
    nlinarith
  · intro hd
    have h3 := h2 (hd0 hd)
    rw [heq, derivative_C_mul]
    simp only [eval_mul, eval_C]
    nlinarith

end SuperRamanujan227.Dev.Base
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57.PartJ
open SuperRamanujan227.Main
/-! ### `gbinom` -/
lemma gbinom_zero (N : ℝ) : gbinom N 0 = 1 := by simp [gbinom]

lemma gbinom_succ (N : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) * gbinom N (k + 1) = (N - k) * gbinom N k := by
  unfold gbinom
  rw [descPochhammer_succ_eval, Nat.factorial_succ]
  have h1 : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

lemma gbinom_pos (N : ℝ) (k : ℕ) (h : (k : ℝ) - 1 < N) : 0 < gbinom N k := by
  induction k with
  | zero => simp [gbinom_zero]
  | succ k ih =>
    have h' : (k : ℝ) - 1 < N := by push_cast at h; linarith
    have := ih h'
    have h2 := gbinom_succ N k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h3 : 0 < (N - k) * gbinom N k := mul_pos (by push_cast at h; linarith) this
    rw [← h2] at h3
    exact pos_of_mul_pos_right h3 hk.le

end SuperRamanujan227.Dev.K57.PartJ
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57
open SuperRamanujan227.Main
/-! Blueprint for Theorem 5.7 (Krasikov's bound, symmetric case), following Krasikov,
arXiv:math/0211190, Theorem 1 and Theorem 7. -/
/-! ## Part J: algebra of `jacobiSym` -/

end SuperRamanujan227.Dev.K57
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57.PartJ
open SuperRamanujan227.Main
/-! ### The basis `U^s V^(r-s)` -/
noncomputable def U : ℝ[X] := C (1 / 2 : ℝ) * (X - 1)

noncomputable def V : ℝ[X] := C (1 / 2 : ℝ) * (X + 1)

noncomputable def S (r : ℕ) (c : ℕ → ℝ) : ℝ[X] :=
  ∑ s ∈ Finset.range (r + 1), C (c s) * U ^ s * V ^ (r - s)

noncomputable def acoef (γ : ℝ) (r : ℕ) (s : ℕ) : ℝ :=
  gbinom ((r : ℝ) + γ) (r - s) * gbinom ((r : ℝ) + γ) s

lemma jac_eq_S (γ : ℝ) (r : ℕ) : jacobiSym γ r = S r (acoef γ r) := rfl

lemma dU : derivative U = C (1 / 2 : ℝ) := by simp [U]

lemma dV : derivative V = C (1 / 2 : ℝ) := by simp [V]

lemma evalU (x : ℝ) : U.eval x = (x - 1) / 2 := by simp [U]; ring

lemma evalV (x : ℝ) : V.eval x = (x + 1) / 2 := by simp [V]; ring

lemma X_eq : (X : ℝ[X]) = U + V := by
  simp only [U, V, ← mul_add]
  rw [show (X - 1 + (X + 1) : ℝ[X]) = C 2 * X by rw [C_ofNat]; ring, ← mul_assoc, ← C_mul]
  norm_num

lemma term_deriv (c : ℝ) (s t : ℕ) :
    derivative (C c * U ^ s * V ^ t) =
      C (c * s / 2) * U ^ (s - 1) * V ^ t + C (c * t / 2) * U ^ s * V ^ (t - 1) := by
  simp only [derivative_mul, derivative_C, derivative_pow, dU, dV, zero_mul, zero_add]
  simp only [C_mul, div_eq_mul_inv, map_natCast, map_one]
  rw [show (C (2 : ℝ)⁻¹) = C (1 / 2) by norm_num]
  ring

lemma S_ext (r : ℕ) (c d : ℕ → ℝ) (h : ∀ s ≤ r, c s = d s) : S r c = S r d := by
  unfold S
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [h s (by simp at hs; omega)]

lemma S_add (r : ℕ) (c d : ℕ → ℝ) : S r c + S r d = S r (fun s => c s + d s) := by
  unfold S
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [C_add]; ring

lemma C_mul_S (k : ℝ) (r : ℕ) (c : ℕ → ℝ) : C k * S r c = S r (fun s => k * c s) := by
  unfold S
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [C_mul]; ring

lemma U_mul_S (r : ℕ) (c : ℕ → ℝ) :
    U * S r c = S (r + 1) (fun s => if s = 0 then 0 else c (s - 1)) := by
  unfold S
  rw [Finset.sum_range_succ' _ (r + 1), Finset.mul_sum]
  simp only [if_true, map_zero, zero_mul, add_zero, Nat.add_one_ne_zero, if_false,
    Nat.add_sub_cancel, Nat.add_sub_add_right]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

lemma V_mul_S (r : ℕ) (c : ℕ → ℝ) :
    V * S r c = S (r + 1) (fun s => if s = r + 1 then 0 else c s) := by
  unfold S
  rw [Finset.sum_range_succ _ (r + 1), Finset.mul_sum]
  simp only [if_true, map_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s < r + 1 := Finset.mem_range.mp hs
  rw [if_neg (by omega), show r + 1 - s = (r - s) + 1 by omega, pow_succ]
  ring

lemma deriv_S (r : ℕ) (c : ℕ → ℝ) :
    derivative (S (r + 1) c) =
      S r (fun t => (c (t + 1) * ((t : ℝ) + 1) + c t * ((r + 1 - t : ℕ) : ℝ)) / 2) := by
  unfold S
  rw [derivative_sum]
  simp only [term_deriv]
  rw [Finset.sum_add_distrib, Finset.sum_range_succ' _ (r + 1),
    Finset.sum_range_succ (fun s => C (c s * ((r + 1 - s : ℕ) : ℝ) / 2) * U ^ s * V ^ (r + 1 - s - 1))]
  simp only [Nat.cast_zero, mul_zero, zero_div, map_zero, zero_mul, add_zero, Nat.sub_self,
    Nat.add_sub_cancel, Nat.add_sub_add_right, Nat.cast_add, Nat.cast_one]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show r + 1 - s - 1 = r - s by omega]
  rw [show C ((c (s + 1) * ((s : ℝ) + 1) + c s * ((r + 1 - s : ℕ) : ℝ)) / 2)
      = C (c (s + 1) * ((s : ℝ) + 1) / 2) + C (c s * ((r + 1 - s : ℕ) : ℝ) / 2) by
      rw [← C_add]; ring_nf]
  ring

/-! ### Evaluations -/
lemma eval_S (r : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    (S r c).eval x = ∑ s ∈ Finset.range (r + 1), c s * ((x - 1) / 2) ^ s * ((x + 1) / 2) ^ (r - s) := by
  simp [S, eval_finsetSum, evalU, evalV]

lemma acoef_pos (γ : ℝ) (hγ : -1 < γ) (r s : ℕ) (hs : s ≤ r) : 0 < acoef γ r s := by
  unfold acoef
  apply mul_pos
  · apply gbinom_pos
    have : ((r - s : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r s
    linarith
  · apply gbinom_pos
    have : (s : ℝ) ≤ r := by exact_mod_cast hs
    linarith

lemma acoef_symm (γ : ℝ) (r s : ℕ) (hs : s ≤ r) : acoef γ r (r - s) = acoef γ r s := by
  unfold acoef
  rw [Nat.sub_sub_self hs, mul_comm]

end SuperRamanujan227.Dev.K57.PartJ
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57
open SuperRamanujan227.Main

end SuperRamanujan227.Dev.K57
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57.PartJ
open SuperRamanujan227.Main
lemma jac_pos_of_one_le (γ : ℝ) (hγ : -1 < γ) (r : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    0 < (jacobiSym γ r).eval x := by
  rw [jac_eq_S, eval_S, Finset.sum_range_succ']
  have h0 := acoef_pos γ hγ r 0 (Nat.zero_le _)
  have hu : 0 ≤ (x - 1) / 2 := by linarith
  have hv : 0 < (x + 1) / 2 := by linarith
  apply add_pos_of_nonneg_of_pos
  · apply Finset.sum_nonneg
    intro i hi
    have := acoef_pos γ hγ r (i + 1) (by simp at hi; omega)
    positivity
  · simp only [pow_zero, mul_one, Nat.sub_zero]
    positivity

end SuperRamanujan227.Dev.K57.PartJ
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57
open SuperRamanujan227.Main
alias jac_pos_of_one_le := SuperRamanujan227.Dev.K57.PartJ.jac_pos_of_one_le

end SuperRamanujan227.Dev.K57
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57.PartJ
open SuperRamanujan227.Main
lemma jac_eval_neg (γ : ℝ) (r : ℕ) (x : ℝ) :
    (jacobiSym γ r).eval (-x) = (-1) ^ r * (jacobiSym γ r).eval x := by
  rw [jac_eq_S, eval_S, eval_S, Finset.mul_sum]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s ≤ r := by simp at hs; omega
  rw [show r + 1 - 1 - s = r - s by omega, acoef_symm γ r s hs', Nat.sub_sub_self hs']
  have e1 : (-x - 1) / 2 = -((x + 1) / 2) := by ring
  have e2 : (-x + 1) / 2 = -((x - 1) / 2) := by ring
  rw [e1, e2, neg_pow ((x + 1) / 2), neg_pow ((x - 1) / 2)]
  have : (-1 : ℝ) ^ r = (-1) ^ (r - s) * (-1) ^ s := by
    rw [← pow_add, Nat.sub_add_cancel hs']
  rw [this]
  ring

end SuperRamanujan227.Dev.K57.PartJ
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57
open SuperRamanujan227.Main

end SuperRamanujan227.Dev.K57
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57.PartJ
open SuperRamanujan227.Main
/-! ### Degree and leading coefficient -/
lemma term_eq (c : ℝ) (s t : ℕ) :
    C c * U ^ s * V ^ t = C (c * (1 / 2) ^ (s + t)) * ((X - C 1) ^ s * (X + C 1) ^ t) := by
  simp only [U, V, mul_pow, C_mul, C_pow, pow_add, map_one]
  ring

lemma monic_nd (s t : ℕ) :
    ((X - C (1 : ℝ)) ^ s * (X + C 1) ^ t).Monic ∧
      ((X - C (1 : ℝ)) ^ s * (X + C 1) ^ t).natDegree = s + t := by
  have h1 : ((X - C (1 : ℝ)) ^ s).Monic := (monic_X_sub_C 1).pow s
  have h2 : ((X + C (1 : ℝ)) ^ t).Monic := (monic_X_add_C 1).pow t
  refine ⟨h1.mul h2, ?_⟩
  rw [natDegree_mul h1.ne_zero h2.ne_zero, natDegree_pow, natDegree_pow, natDegree_X_sub_C,
    natDegree_X_add_C]
  ring

lemma natDegree_S_le (r : ℕ) (c : ℕ → ℝ) : (S r c).natDegree ≤ r := by
  unfold S
  apply natDegree_sum_le_of_forall_le
  intro s hs
  have hs' : s ≤ r := by simp at hs; omega
  rw [term_eq]
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [(monic_nd s (r - s)).2]
  omega

lemma coeff_S (r : ℕ) (c : ℕ → ℝ) :
    (S r c).coeff r = (∑ s ∈ Finset.range (r + 1), c s) * (1 / 2) ^ r := by
  unfold S
  rw [finsetSum_coeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s ≤ r := by simp at hs; omega
  rw [term_eq, coeff_C_mul, Nat.add_sub_cancel' hs']
  have h := monic_nd s (r - s)
  rw [Nat.add_sub_cancel' hs'] at h
  have : ((X - C (1 : ℝ)) ^ s * (X + C 1) ^ (r - s)).coeff r = 1 := by
    have h3 := h.1.coeff_natDegree; rwa [h.2] at h3
  rw [this, mul_one]

lemma coeff_jac_pos (γ : ℝ) (hγ : -1 < γ) (r : ℕ) : 0 < (jacobiSym γ r).coeff r := by
  rw [jac_eq_S, coeff_S]
  apply mul_pos _ (by positivity)
  apply Finset.sum_pos
  · intro s hs
    exact acoef_pos γ hγ r s (by simp at hs; omega)
  · exact ⟨0, by simp⟩

lemma jac_natDegree (γ : ℝ) (hγ : -1 < γ) (r : ℕ) : (jacobiSym γ r).natDegree = r :=
  natDegree_eq_of_le_of_coeff_ne_zero (by rw [jac_eq_S]; exact natDegree_S_le _ _)
    (coeff_jac_pos γ hγ r).ne'

end SuperRamanujan227.Dev.K57.PartJ
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57
open SuperRamanujan227.Main
alias jac_natDegree := SuperRamanujan227.Dev.K57.PartJ.jac_natDegree

end SuperRamanujan227.Dev.K57
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57.PartJ
open SuperRamanujan227.Main
lemma jac_leadingCoeff_pos (γ : ℝ) (hγ : -1 < γ) (r : ℕ) :
    0 < (jacobiSym γ r).leadingCoeff := by
  rw [leadingCoeff, jac_natDegree γ hγ r]
  exact coeff_jac_pos γ hγ r

end SuperRamanujan227.Dev.K57.PartJ
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57
open SuperRamanujan227.Main

end SuperRamanujan227.Dev.K57
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57.PartJ
open SuperRamanujan227.Main
/-! ### Derivative and the lowering identity -/
lemma jac_derivative (γ : ℝ) (r : ℕ) :
    derivative (jacobiSym γ (r + 1)) =
      C (((r : ℝ) + 2 * γ + 2) / 2) * jacobiSym (γ + 1) r := by
  rw [jac_eq_S, jac_eq_S, deriv_S, C_mul_S]
  apply S_ext
  intro t ht
  obtain ⟨j, rfl⟩ : ∃ j, r = t + j := ⟨r - t, by omega⟩
  have hN : ((t + j + 1 : ℕ) : ℝ) + γ = ((t + j : ℕ) : ℝ) + (γ + 1) := by push_cast; ring
  simp only [acoef, hN]
  rw [show t + j + 1 - (t + 1) = j by omega, show t + j + 1 - t = j + 1 by omega,
    show t + j - t = j by omega]
  have h1 := gbinom_succ (((t + j : ℕ) : ℝ) + (γ + 1)) t
  have h2 := gbinom_succ (((t + j : ℕ) : ℝ) + (γ + 1)) j
  push_cast at h1 h2 ⊢
  linear_combination (gbinom (↑t + ↑j + (γ + 1)) j / 2) * h1 +
    (gbinom (↑t + ↑j + (γ + 1)) t / 2) * h2

end SuperRamanujan227.Dev.K57.PartJ
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57
open SuperRamanujan227.Main

end SuperRamanujan227.Dev.K57
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57.PartJ
open SuperRamanujan227.Main
lemma term_lower (c : ℝ) (s t : ℕ) :
    (1 - X ^ 2) * derivative (C c * U ^ s * V ^ t) =
      V * (C (-2 * (s : ℝ) * c) * U ^ s * V ^ t) + U * (C (-2 * (t : ℝ) * c) * U ^ s * V ^ t) := by
  rw [term_deriv]
  apply Polynomial.funext
  intro x
  rcases s with _ | s <;> rcases t with _ | t <;>
    simp [evalU, evalV, pow_succ] <;> ring

lemma lower_S (m : ℕ) (c : ℕ → ℝ) :
    (1 - X ^ 2) * derivative (S m c) =
      V * S m (fun s => -2 * (s : ℝ) * c s) + U * S m (fun s => -2 * ((m - s : ℕ) : ℝ) * c s) := by
  unfold S
  rw [derivative_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [term_lower]

lemma S_sub (r : ℕ) (c d : ℕ → ℝ) : S r c - S r d = S r (fun s => c s - d s) := by
  unfold S
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [C_sub]; ring

lemma lowering (γ : ℝ) (m : ℕ) :
    (1 - X ^ 2) * derivative (jacobiSym (γ + 1) m) - C (2 * (γ + 1)) * X * jacobiSym (γ + 1) m
      = C (-2 * ((m : ℝ) + 1)) * jacobiSym γ (m + 1) := by
  rw [jac_eq_S, jac_eq_S, lower_S, X_eq]
  have e : ∀ A B P : ℝ[X], V * A + U * B - C (2 * (γ + 1)) * (U + V) * P
      = V * (A - C (2 * (γ + 1)) * P) + U * (B - C (2 * (γ + 1)) * P) := by intros; ring
  rw [e, C_mul_S, S_sub, S_sub, U_mul_S, V_mul_S, S_add, C_mul_S]
  apply S_ext
  intro s hs
  have hN : ((m + 1 : ℕ) : ℝ) + γ = (m : ℝ) + (γ + 1) := by push_cast; ring
  simp only [acoef, hN]
  set N : ℝ := (m : ℝ) + (γ + 1) with hNdef
  rcases s with _ | k
  · simp only [if_true, add_zero, Nat.sub_zero, gbinom_zero, Nat.cast_zero,
      show (0 : ℕ) ≠ m + 1 from (Nat.succ_ne_zero m).symm, if_false]
    have h := gbinom_succ N m
    simp only [mul_one]
    generalize gbinom N = B at h ⊢
    rw [hNdef] at h
    linear_combination 2 * h
  · rcases Nat.lt_or_ge k m with hk | hk
    · obtain ⟨j, rfl⟩ : ∃ j, m = k + 1 + j := ⟨m - (k + 1), by omega⟩
      simp only [show k + 1 ≠ k + 1 + j + 1 by omega, if_false, Nat.add_one_ne_zero,
        Nat.add_sub_cancel, show k + 1 + j - (k + 1) = j by omega,
        show k + 1 + j - k = j + 1 by omega, show k + 1 + j + 1 - (k + 1) = j + 1 by omega]
      have hj := gbinom_succ N j
      have hk' := gbinom_succ N k
      generalize gbinom N = B at hj hk' ⊢
      rw [hNdef] at hj hk'
      push_cast at hj hk' ⊢
      linear_combination (2 * B (k + 1)) * hj + (2 * B (j + 1)) * hk'
    · have hkm : k = m := by omega
      subst hkm
      simp only [if_true, Nat.add_one_ne_zero, if_false, zero_add, Nat.add_sub_cancel,
        Nat.sub_self, gbinom_zero, Nat.cast_zero]
      have h := gbinom_succ N k
      simp only [one_mul]
      generalize gbinom N = B at h ⊢
      rw [hNdef] at h
      linear_combination 2 * h

lemma jac_ode (γ : ℝ) (r : ℕ) :
    (1 - X ^ 2) * derivative (derivative (jacobiSym γ r))
      - C (2 * (γ + 1)) * X * derivative (jacobiSym γ r)
      + C ((r : ℝ) * ((r : ℝ) + 2 * γ + 1)) * jacobiSym γ r = 0 := by
  rcases r with _ | m
  · have h0 : derivative (jacobiSym γ 0) = 0 :=
      derivative_of_natDegree_zero (by
        have := natDegree_S_le 0 (acoef γ 0); rw [jac_eq_S]; omega)
    simp [h0]
  · have hL := lowering γ m
    have hlam : C (((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) + 2 * γ + 1))
        = -(C (((m : ℝ) + 2 * γ + 2) / 2) * C (-2 * ((m : ℝ) + 1))) := by
      rw [← C_mul, ← C_neg]; congr 1; push_cast; ring
    rw [jac_derivative, derivative_mul, derivative_C, zero_mul, zero_add]
    linear_combination C (((m : ℝ) + 2 * γ + 2) / 2) * hL + jacobiSym γ (m + 1) * hlam

end SuperRamanujan227.Dev.K57.PartJ
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57
open SuperRamanujan227.Main
alias jac_ode := SuperRamanujan227.Dev.K57.PartJ.jac_ode

end SuperRamanujan227.Dev.K57
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57.PartJ
open SuperRamanujan227.Main
/-! ### Real-rootedness -/
lemma alt_roots (T : Finset ℝ) : ∀ (f : ℝ → ℝ), Continuous f →
    (∀ p ∈ T, 0 < f p * (-1) ^ (T.filter (fun q => p < q)).card) →
    ∃ R : Finset ℝ, T.card ≤ R.card + 1 ∧
      ∀ x ∈ R, f x = 0 ∧ ∃ p ∈ T, ∃ q ∈ T, p < x ∧ x < q := by
  refine Finset.induction_on_max T ?_ ?_
  · intro f _ _; exact ⟨∅, by simp, by simp⟩
  · intro M T hM ih f hf hsign
    rcases T.eq_empty_or_nonempty with hT | hT
    · subst hT; exact ⟨∅, by simp, by simp⟩
    have hMT : M ∉ T := fun h => lt_irrefl M (hM M h)
    set M' := T.max' hT
    have hM'T : M' ∈ T := T.max'_mem hT
    have hM'lt : M' < M := hM M' hM'T
    have hfM : 0 < f M := by
      have := hsign M (Finset.mem_insert_self _ _)
      have hfilt : (insert M T).filter (fun q => M < q) = ∅ := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.notMem_empty, iff_false, not_and]
        rintro (rfl | hq) h
        · exact lt_irrefl _ h
        · exact lt_asymm h (hM q hq)
      rw [hfilt] at this; simpa using this
    have hfilt : ∀ p ∈ T, (insert M T).filter (fun q => p < q)
        = insert M (T.filter (fun q => p < q)) := by
      intro p hp
      rw [Finset.filter_insert, if_pos (hM p hp)]
    have hcard : ∀ p ∈ T, ((insert M T).filter (fun q => p < q)).card
        = (T.filter (fun q => p < q)).card + 1 := by
      intro p hp
      rw [hfilt p hp, Finset.card_insert_of_notMem]
      intro h; exact hMT (Finset.mem_filter.mp h).1
    have hfM' : f M' < 0 := by
      have := hsign M' (Finset.mem_insert_of_mem hM'T)
      rw [hcard M' hM'T] at this
      have h0 : (T.filter (fun q => M' < q)) = ∅ := by
        ext q
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_lt]
        intro hq; exact T.le_max' q hq
      rw [h0] at this; simp at this; linarith
    obtain ⟨x, hx, hfx⟩ : ∃ x ∈ Set.Ioo M' M, f x = 0 :=
      intermediate_value_Ioo hM'lt.le hf.continuousOn ⟨hfM', hfM⟩
    have hsign' : ∀ p ∈ T, 0 < (fun y => -f y) p * (-1) ^ (T.filter (fun q => p < q)).card := by
      intro p hp
      have := hsign p (Finset.mem_insert_of_mem hp)
      rw [hcard p hp, pow_succ] at this
      simp only; linarith
    obtain ⟨R, hRc, hR⟩ := ih (fun y => -f y) hf.neg hsign'
    have hxR : x ∉ R := by
      intro h
      obtain ⟨_, p, hp, q, hq, _, hxq⟩ := hR x h
      have := T.le_max' q hq
      linarith [hx.1]
    refine ⟨insert x R, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hMT, Finset.card_insert_of_notMem hxR]; omega
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact ⟨hfx, M', Finset.mem_insert_of_mem hM'T, M, Finset.mem_insert_self _ _, hx.1, hx.2⟩
      · obtain ⟨h1, p, hp, q, hq, hpy, hyq⟩ := hR y hy
        exact ⟨by simpa using h1, p, Finset.mem_insert_of_mem hp, q, Finset.mem_insert_of_mem hq,
          hpy, hyq⟩

lemma sign_prod (s : Finset ℝ) (y : ℝ) :
    0 < ((s.val.erase y).map (fun a => y - a)).prod * (-1) ^ (s.filter (fun q => y < q)).card := by
  have h1 : ((s.val.erase y).map (fun a => y - a)).prod = ∏ a ∈ s.erase y, (y - a) := by
    rw [Finset.prod_eq_multiset_prod, Finset.erase_val]
  have h2 : (-1 : ℝ) ^ (s.filter (fun q => y < q)).card
      = ∏ a ∈ s.erase y, (if y < a then (-1 : ℝ) else 1) := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]
    congr 2
    ext a
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨ha, hya⟩; exact ⟨⟨(ne_of_lt hya).symm, ha⟩, hya⟩
    · rintro ⟨⟨_, ha⟩, hya⟩; exact ⟨ha, hya⟩
  rw [h1, h2, ← Finset.prod_mul_distrib]
  apply Finset.prod_pos
  intro a ha
  have hne : a ≠ y := (Finset.mem_erase.mp ha).1
  split_ifs with h
  · linarith
  · have : a < y := lt_of_le_of_ne (not_lt.mp h) hne
    linarith

lemma roots_eq (p : ℝ[X]) (hp : p ≠ 0) (s : Finset ℝ) (hcard : p.natDegree ≤ s.card)
    (h : ∀ y ∈ s, p.IsRoot y) : s.val = p.roots := by
  have hle : s.val ≤ p.roots :=
    (Multiset.le_iff_subset s.nodup).mpr fun y hy => (mem_roots hp).mpr (h y hy)
  exact Multiset.eq_of_le_of_card_le hle ((card_roots' p).trans hcard)

lemma jac_ne_zero (γ : ℝ) (hγ : -1 < γ) (r : ℕ) : jacobiSym γ r ≠ 0 := by
  intro h
  have := jac_leadingCoeff_pos γ hγ r
  rw [h, leadingCoeff_zero] at this
  exact lt_irrefl _ this

lemma claim (m : ℕ) : ∀ γ : ℝ, -1 < γ → ∃ s : Finset ℝ, s.card = m ∧
    ∀ y ∈ s, (jacobiSym γ m).IsRoot y ∧ -1 < y ∧ y < 1 := by
  induction m with
  | zero => intro γ _; exact ⟨∅, by simp, by simp⟩
  | succ m ih =>
    intro γ hγ
    have hγ1 : -1 < γ + 1 := by linarith
    obtain ⟨s, hsc, hs⟩ := ih (γ + 1) hγ1
    set h := jacobiSym (γ + 1) m with hh
    set g := jacobiSym γ (m + 1) with hg
    have hh0 : h ≠ 0 := jac_ne_zero _ hγ1 m
    have hdeg : h.natDegree = m := jac_natDegree _ hγ1 m
    have hroots : s.val = h.roots :=
      roots_eq h hh0 s (by omega) fun y hy => (hs y hy).1
    have hcr : Multiset.card h.roots = h.natDegree := by
      rw [← hroots, hdeg]; exact hsc
    have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hcr
    have hlc : 0 < h.leadingCoeff := jac_leadingCoeff_pos _ hγ1 m
    -- derivative of h at its roots
    have hder : ∀ y ∈ s, (derivative h).eval y
        = h.leadingCoeff * ((s.val.erase y).map (fun a => y - a)).prod := by
      intro y hy
      have hy' : y ∈ h.roots := by rw [← hroots]; exact hy
      conv_lhs => rw [← hfac]
      rw [derivative_C_mul, eval_mul, eval_C, eval_multiset_prod_X_sub_C_derivative hy', hroots]
    -- g at the roots of h
    have hlow := lowering γ m
    have hgy : ∀ y ∈ s, g.eval y
        = -((1 - y ^ 2) * (derivative h).eval y) / (2 * ((m : ℝ) + 1)) := by
      intro y hy
      have := congrArg (fun P => P.eval y) hlow
      simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_one, eval_C] at this
      rw [(hs y hy).1.eq_zero] at this
      field_simp
      linarith
    -- the sign pattern
    set T : Finset ℝ := insert (-1) (insert 1 s) with hT
    have h1s : (1 : ℝ) ∉ s := fun h1 => lt_irrefl _ (hs 1 h1).2.2
    have hm1s : (-1 : ℝ) ∉ insert 1 s := by
      rw [Finset.mem_insert]; rintro (h | h)
      · norm_num at h
      · exact lt_irrefl _ (hs (-1) h).2.1
    have hTcard : T.card = m + 2 := by
      rw [hT, Finset.card_insert_of_notMem hm1s, Finset.card_insert_of_notMem h1s, hsc]
    have hg1 : 0 < g.eval 1 := jac_pos_of_one_le γ hγ (m + 1) 1 le_rfl
    have hsign : ∀ p ∈ T, 0 < g.eval p * (-1) ^ (T.filter (fun q => p < q)).card := by
      intro p hp
      rw [hT, Finset.mem_insert, Finset.mem_insert] at hp
      rcases hp with rfl | rfl | hp
      · have hf : T.filter (fun q => (-1 : ℝ) < q) = insert 1 s := by
          rw [hT, Finset.filter_insert, if_neg (lt_irrefl _), Finset.filter_insert,
            if_pos (by norm_num), Finset.filter_true_of_mem (fun y hy => (hs y hy).2.1)]
        rw [hf, Finset.card_insert_of_notMem h1s, hsc]
        have := jac_eval_neg γ (m + 1) 1
        rw [← hg] at this
        rw [this, mul_comm, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
        norm_num; exact hg1
      · have hf : T.filter (fun q => (1 : ℝ) < q) = ∅ := by
          rw [hT, Finset.filter_insert, if_neg (by norm_num), Finset.filter_insert,
            if_neg (lt_irrefl _), Finset.filter_false_of_mem (fun y hy => not_lt.mpr (hs y hy).2.2.le)]
        rw [hf]; simpa using hg1
      · have hf : T.filter (fun q => p < q) = insert 1 (s.filter (fun q => p < q)) := by
          rw [hT, Finset.filter_insert, if_neg (by linarith [(hs p hp).2.1]), Finset.filter_insert,
            if_pos (hs p hp).2.2]
        rw [hf, Finset.card_insert_of_notMem (fun h1 => h1s (Finset.mem_filter.mp h1).1), pow_succ,
          hgy p hp, hder p hp]
        have hsp := sign_prod s p
        have hy2 : 0 < 1 - p ^ 2 := by nlinarith [(hs p hp).2.1, (hs p hp).2.2]
        have hm : (0 : ℝ) < 2 * ((m : ℝ) + 1) := by positivity
        have key : -((1 - p ^ 2) * (h.leadingCoeff * ((s.val.erase p).map (fun a => p - a)).prod))
            / (2 * ((m : ℝ) + 1)) * ((-1) ^ (s.filter (fun q => p < q)).card * (-1))
            = ((1 - p ^ 2) * h.leadingCoeff / (2 * ((m : ℝ) + 1))) *
              (((s.val.erase p).map (fun a => p - a)).prod * (-1) ^ (s.filter (fun q => p < q)).card) := by
          ring
        rw [key]
        exact mul_pos (by positivity) hsp
    obtain ⟨R, hRc, hR⟩ := alt_roots T (fun x => g.eval x) g.continuous hsign
    have hTb : ∀ p ∈ T, -1 ≤ p ∧ p ≤ 1 := by
      intro p hp
      rw [hT, Finset.mem_insert, Finset.mem_insert] at hp
      rcases hp with rfl | rfl | hp
      · norm_num
      · norm_num
      · exact ⟨(hs p hp).2.1.le, (hs p hp).2.2.le⟩
    have hRb : ∀ x ∈ R, g.IsRoot x ∧ -1 < x ∧ x < 1 := by
      intro x hx
      obtain ⟨h0, p, hp, q, hq, hpx, hxq⟩ := hR x hx
      exact ⟨h0, by linarith [(hTb p hp).1], by linarith [(hTb q hq).2]⟩
    have hg0 : g ≠ 0 := jac_ne_zero γ hγ (m + 1)
    have hgdeg : g.natDegree = m + 1 := jac_natDegree γ hγ (m + 1)
    have hRle : R.card ≤ m + 1 := by
      have hle : R.val ≤ g.roots :=
        (Multiset.le_iff_subset R.nodup).mpr fun y hy => (mem_roots hg0).mpr (hRb y hy).1
      have := (Multiset.card_le_card hle).trans (card_roots' g)
      rw [hgdeg] at this; exact this
    exact ⟨R, by omega, hRb⟩

theorem jac_realRooted (γ : ℝ) (hγ : -1 < γ) (r : ℕ) :
    RealRooted (jacobiSym γ r) ∧ ∀ x ∈ (jacobiSym γ r).roots, -1 < x ∧ x < 1 := by
  obtain ⟨s, hsc, hs⟩ := claim r γ hγ
  have h0 := jac_ne_zero γ hγ r
  have hdeg := jac_natDegree γ hγ r
  have hroots : s.val = (jacobiSym γ r).roots :=
    roots_eq _ h0 s (by omega) fun y hy => (hs y hy).1
  refine ⟨⟨h0, ?_⟩, ?_⟩
  · rw [← hroots, hdeg]; exact hsc
  · intro x hx
    rw [← hroots] at hx
    exact (hs x hx).2

end SuperRamanujan227.Dev.K57.PartJ
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57
open SuperRamanujan227.Main
alias jac_realRooted := SuperRamanujan227.Dev.K57.PartJ.jac_realRooted

end SuperRamanujan227.Dev.K57
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57.PartK
open SuperRamanujan227.Main
open SuperRamanujan227.Dev.Base
/-- Laguerre expression `p'(x)^2 - p(x) p''(x)`. -/
noncomputable def Lg (p : ℝ[X]) (x : ℝ) : ℝ :=
  (p.derivative.eval x) ^ 2 - p.eval x * (p.derivative.derivative.eval x)

lemma Lg_mul (p q : ℝ[X]) (x : ℝ) :
    Lg (p * q) x = (q.eval x) ^ 2 * Lg p x + (p.eval x) ^ 2 * Lg q x := by
  simp only [Lg, derivative_mul, derivative_add, eval_add, eval_mul]
  ring

lemma Lg_X_sub_C (a x : ℝ) : Lg (X - C a) x = 1 := by
  simp [Lg]

lemma Lg_C (a x : ℝ) : Lg (C a) x = 0 := by
  simp [Lg]

lemma Lg_prod_nonneg (s : Multiset ℝ) (x : ℝ) :
    0 ≤ Lg (s.map (fun r => (X - C r : ℝ[X]))).prod x := by
  induction s using Multiset.induction_on with
  | empty => simp [Lg]
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [Lg_mul, Lg_X_sub_C]
    positivity

/-- The pure real optimization step. -/
lemma opt (lam k c z P Q R B : ℝ) (hlam : 0 < lam) (hk : 0 < k ^ 2)
    (hzc : z < c) (hc1 : c < 1) (hcm : -1 < c)
    (h : (1 - c ^ 2) ^ 2 ≤ (c - z) ^ 2 * (lam * (1 - c ^ 2) - k ^ 2 * c ^ 2))
    (hP : P = 4 * (lam + k ^ 2)) (hQ : Q = 4 * lam) (hR : R = Real.sqrt (P * Q))
    (hB : B = R / P) :
    z < B - 3 * (1 - B ^ 2) ^ ((2 : ℝ) / 3) * (2 * R) ^ (-(1 : ℝ) / 3) := by
  have hPpos : 0 < P := by rw [hP]; positivity
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hRpos : 0 < R := by rw [hR]; exact Real.sqrt_pos.mpr (mul_pos hPpos hQpos)
  have hR2 : R ^ 2 = P * Q := by rw [hR]; exact Real.sq_sqrt (by positivity)
  have hBpos : 0 < B := by rw [hB]; positivity
  have hPB : P * B = R := by rw [hB]; field_simp
  have hB2 : P * B ^ 2 = Q := by
    have : P * (P * B ^ 2) = P * Q := by rw [← hR2, ← hPB]; ring
    exact mul_left_cancel₀ hPpos.ne' this
  have hB1 : B ^ 2 < 1 := by
    have : P * B ^ 2 < P * 1 := by rw [hB2, hP, hQ]; nlinarith
    exact lt_of_mul_lt_mul_left this hPpos.le
  have hN : lam * (1 - c ^ 2) - k ^ 2 * c ^ 2 = P / 4 * (B ^ 2 - c ^ 2) := by
    have e : P * B ^ 2 = 4 * lam := by rw [hB2, hQ]
    rw [hP] at e ⊢
    linear_combination (-1/4 : ℝ) * e
  rw [hN] at h
  have h1c : 0 < 1 - c ^ 2 := by nlinarith
  have hd : 0 < c - z := by linarith
  have hNpos : 0 < B ^ 2 - c ^ 2 := by
    by_contra hcon
    push Not at hcon
    have : (c - z) ^ 2 * (P / 4 * (B ^ 2 - c ^ 2)) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hcon
    nlinarith [pow_pos h1c 2]
  have hcB : c < B := by nlinarith
  have hcB' : 0 < B + c := by nlinarith
  obtain ⟨ε, hε⟩ : ∃ ε, ε = B - c := ⟨_, rfl⟩
  have hεpos : 0 < ε := by linarith
  obtain ⟨M, hM⟩ : ∃ M, M = 1 - B ^ 2 := ⟨_, rfl⟩
  have hMpos : 0 < M := by linarith
  obtain ⟨d, hdd⟩ : ∃ d, d = c - z := ⟨_, rfl⟩
  rw [← hdd] at h
  have hd' : 0 < d := by rw [hdd]; linarith
  -- d^2 R ε > 2 M^2
  have hkey : 2 * M ^ 2 < d ^ 2 * R * ε := by
    have h1 : M ^ 2 ≤ (1 - c ^ 2) ^ 2 := by
      have : M ≤ 1 - c ^ 2 := by rw [hM]; linarith
      nlinarith
    have h2 : P / 4 * (B ^ 2 - c ^ 2) < R * ε / 2 := by
      rw [← hPB, hε]
      have : B ^ 2 - c ^ 2 = (B - c) * (B + c) := by ring
      rw [this]
      have : P / 4 * ((B - c) * (B + c)) - P * B * (B - c) / 2 = - (P / 4) * (B - c) * (B - c) := by
        ring
      have hq : 0 < P / 4 * (B - c) * (B - c) := by
        have : 0 < B - c := by linarith
        positivity
      linarith
    have hd2 : 0 < d ^ 2 := by positivity
    have h3 := mul_lt_mul_of_pos_left h2 hd2
    have h4 : d ^ 2 * (R * ε / 2) = d ^ 2 * R * ε / 2 := by ring
    linarith
  obtain ⟨t, ht⟩ : ∃ t, t = M ^ ((2 : ℝ) / 3) * (2 * R) ^ (-(1 : ℝ) / 3) := ⟨_, rfl⟩
  have htpos : 0 < t := by rw [ht]; positivity
  have ht3 : t ^ 3 * (2 * R) = M ^ 2 := by
    rw [ht, mul_pow]
    have e1 : (M ^ ((2 : ℝ) / 3)) ^ 3 = M ^ 2 := by
      rw [← Real.rpow_mul_natCast hMpos.le]
      norm_num
    have e2 : ((2 * R) ^ (-(1 : ℝ) / 3)) ^ 3 = (2 * R)⁻¹ := by
      rw [← Real.rpow_mul_natCast (by positivity), show (-(1:ℝ) / 3 * ((3 : ℕ) : ℝ)) = -1 by norm_num,
        Real.rpow_neg_one]
    rw [e1, e2]
    field_simp
  have hmain : 3 * t < ε + d := by
    by_contra hcon
    push Not at hcon
    -- AM-GM: ε (d/2)^2 ≤ ((ε + d)/3)^3
    have amgm : ε * (d / 2) ^ 2 ≤ ((ε + d) / 3) ^ 3 := by
      have e : ((ε + d) / 3) ^ 3 - ε * (d / 2) ^ 2 = (ε - d / 2) ^ 2 * (ε + 4 * d) / 27 := by ring
      have : 0 ≤ (ε - d / 2) ^ 2 * (ε + 4 * d) / 27 := by positivity
      linarith
    have h3 : ((ε + d) / 3) ^ 3 ≤ t ^ 3 := by
      apply pow_le_pow_left₀ (by positivity); linarith
    have h4 : ε * (d / 2) ^ 2 * (2 * R) ≤ t ^ 3 * (2 * R) :=
      mul_le_mul_of_nonneg_right (amgm.trans h3) (by positivity)
    rw [ht3] at h4
    have : ε * (d / 2) ^ 2 * (2 * R) = d ^ 2 * R * ε / 2 := by ring
    linarith
  have : z = B - ε - d := by rw [hε, hdd]; ring
  rw [this]
  have : 3 * (1 - B ^ 2) ^ ((2 : ℝ) / 3) * (2 * R) ^ (-(1 : ℝ) / 3) = 3 * t := by rw [ht, hM]; ring
  rw [this]
  linarith

theorem krasikov_abstract (f : ℝ[X]) (r : ℕ) (hr : 1 ≤ r) (γ : ℝ) (hγ : -1 < γ)
    (hrr : RealRooted f) (hdeg : f.natDegree = r)
    (hroots : ∀ x ∈ f.roots, -1 < x ∧ x < 1) (h1 : 0 < f.eval 1)
    (hode : (1 - X ^ 2) * derivative (derivative f) - C (2 * (γ + 1)) * X * derivative f
      + C ((r : ℝ) * ((r : ℝ) + 2 * γ + 1)) * f = 0) :
    let s : ℝ := 2 * γ + 1
    let ρ : ℝ := 2 * (r : ℝ) + 2 * γ + 1
    let R : ℝ := Real.sqrt ((ρ ^ 2 + 2 * s + 1) * (ρ ^ 2 - s ^ 2))
    let B : ℝ := R / (ρ ^ 2 + 2 * s + 1)
    kthLargestRoot f 1 <
      B - 3 * (1 - B ^ 2) ^ ((2 : ℝ) / 3) * (2 * R) ^ (-(1 : ℝ) / 3) := by
  intro s ρ R B
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = γ + 1 := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = (r : ℝ) * ((r : ℝ) + 2 * γ + 1) := ⟨_, rfl⟩
  have hkpos : 0 < k := by linarith
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlampos : 0 < lam := by rw [hlam]; apply mul_pos <;> linarith
  have hne : f.roots ≠ 0 := rr_roots_ne hrr (by omega)
  obtain ⟨z, hz⟩ : ∃ z, z = kthLargestRoot f 1 := ⟨_, rfl⟩
  have hzmem : z ∈ f.roots := hz ▸ alpha1_mem hne
  have hzle : ∀ y ∈ f.roots, y ≤ z := hz ▸ le_alpha1 hne
  rw [← hz]
  obtain ⟨hzm, hz1⟩ := hroots z hzmem
  -- leading coefficient positive
  have hlc : 0 < f.leadingCoeff := by
    have := (pos_beyond hrr 1 (fun y hy => (hroots y hy).2)).1
    by_contra hcon; push Not at hcon
    nlinarith
  -- factorization f = (X - C z) * g
  obtain ⟨S, hS⟩ : ∃ S, S = f.roots.erase z := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ[X], g = C f.leadingCoeff * (S.map (fun r => (X - C r : ℝ[X]))).prod :=
    ⟨_, rfl⟩
  have hfg : f = (X - C z) * g := by
    have := C_leadingCoeff_mul_prod_multiset_X_sub_C hrr.2
    rw [← Multiset.cons_erase hzmem] at this
    conv_lhs => rw [← this]
    rw [hg, hS, Multiset.map_cons, Multiset.prod_cons]
    ring
  have hLg : ∀ x, 0 ≤ Lg g x := by
    intro x
    rw [hg, Lg_mul, Lg_C]
    have := Lg_prod_nonneg S x
    positivity
  have hLf : ∀ x, (f.eval x) ^ 2 ≤ (x - z) ^ 2 * Lg f x := by
    intro x
    rw [hfg, Lg_mul, Lg_X_sub_C]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    have := hLg x
    nlinarith [mul_nonneg (sq_nonneg (x - z)) (mul_nonneg (sq_nonneg (x - z)) this)]
  -- positivity of g, g' beyond z
  have hgpos : ∀ x, z < x → 0 < g.eval x ∧ 0 ≤ (derivative g).eval x := by
    intro x hx
    have hSx : ∀ y ∈ S, y < x := fun y hy => lt_of_le_of_lt (hzle y (Multiset.mem_of_mem_erase (hS ▸ hy))) hx
    obtain ⟨p1, p2⟩ := prod_pos S x hSx
    rw [hg, derivative_C_mul]
    simp only [eval_mul, eval_C]
    refine ⟨mul_pos hlc p1, ?_⟩
    by_cases hS0 : S = 0
    · rw [hS0]; simp
    · exact (mul_pos hlc (p2 hS0)).le
  -- the function h
  let hfun : ℝ → ℝ := fun x => (1 - x ^ 2) * (derivative f).eval x - k * x * f.eval x
  have hcont : Continuous hfun := by
    show Continuous (fun x => (1 - x ^ 2) * (derivative f).eval x - k * x * f.eval x)
    have := (derivative f).continuous
    have := f.continuous
    fun_prop
  have hh1 : hfun 1 < 0 := by
    show (1 - 1 ^ 2) * (derivative f).eval 1 - k * 1 * f.eval 1 < 0
    nlinarith
  -- a point x0 ∈ (z, 1) with hfun x0 > 0
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = (1 - z) * (1 + z) / (4 * (k + 1)) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; apply div_pos <;> nlinarith
  have hδle : δ < (1 - z) / 2 := by
    rw [hδ, div_lt_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  obtain ⟨x0, hx0⟩ : ∃ x0, x0 = z + δ := ⟨_, rfl⟩
  have hx0z : z < x0 := by linarith
  have hx01 : x0 < 1 := by linarith
  have hhx0 : 0 < hfun x0 := by
    show 0 < (1 - x0 ^ 2) * (derivative f).eval x0 - k * x0 * f.eval x0
    obtain ⟨gp, gd⟩ := hgpos x0 hx0z
    have hf' : (derivative f).eval x0 = g.eval x0 + (x0 - z) * (derivative g).eval x0 := by
      rw [hfg, derivative_mul]; simp
    have hf : f.eval x0 = (x0 - z) * g.eval x0 := by rw [hfg]; simp
    rw [hf', hf]
    have hφ : 0 < (1 - x0 ^ 2) - k * x0 * (x0 - z) := by
      have e1 : (1 - z) / 2 ≤ 1 - x0 := by linarith
      have e2 : 1 + z ≤ 1 + x0 := by linarith
      have e3 : (1 - z) * (1 + z) / 2 ≤ 1 - x0 ^ 2 := by
        have : 1 - x0 ^ 2 = (1 - x0) * (1 + x0) := by ring
        rw [this]; nlinarith
      have e4 : k * x0 * (x0 - z) ≤ k * δ := by
        have : x0 - z = δ := by rw [hx0]; ring
        rw [this]
        have : k * x0 ≤ k := by nlinarith
        nlinarith
      have e5 : k * δ < (1 - z) * (1 + z) / 4 := by
        have : k * δ = (1 - z) * (1 + z) / 4 * (k / (k + 1)) := by
          rw [hδ]; field_simp
        rw [this]
        have : k / (k + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
        have : 0 < (1 - z) * (1 + z) / 4 := by nlinarith
        nlinarith
      have : 0 < (1 - z) * (1 + z) := by nlinarith
      linarith
    have h1x : 0 ≤ 1 - x0 ^ 2 := by
      have : 1 - x0 ^ 2 = (1 - x0) * (1 + x0) := by ring
      rw [this]; exact mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ (1 - x0 ^ 2) * ((x0 - z) * (derivative g).eval x0) :=
      mul_nonneg h1x (mul_nonneg (by linarith) gd)
    have e : (1 - x0 ^ 2) * (g.eval x0 + (x0 - z) * (derivative g).eval x0)
        - k * x0 * ((x0 - z) * g.eval x0)
        = g.eval x0 * ((1 - x0 ^ 2) - k * x0 * (x0 - z))
          + (1 - x0 ^ 2) * ((x0 - z) * (derivative g).eval x0) := by ring
    rw [e]
    have := mul_pos gp hφ
    linarith
  -- IVT
  obtain ⟨c, ⟨hcx0, hc1⟩, hc⟩ :=
    intermediate_value_Icc' hx01.le hcont.continuousOn ⟨hh1.le, hhx0.le⟩
  have hc1' : c < 1 := by
    rcases lt_or_eq_of_le hc1 with h | h
    · exact h
    · rw [h] at hc; linarith
  have hzc : z < c := by linarith
  have hcm : -1 < c := by linarith
  have hfc : 0 < f.eval c := by
    have := (hgpos c hzc).1
    rw [hfg]; simp only [eval_mul, eval_sub, eval_X, eval_C]
    exact mul_pos (by linarith) this
  -- the ODE at c
  have hodec := congrArg (eval c) hode
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_one, eval_zero] at hodec
  have hcdef : (1 - c ^ 2) * (derivative f).eval c = k * c * f.eval c := by
    have : (1 - c ^ 2) * (derivative f).eval c - k * c * f.eval c = 0 := hc
    linarith
  have hLc : (1 - c ^ 2) ^ 2 * Lg f c = (f.eval c) ^ 2 * (lam * (1 - c ^ 2) - k ^ 2 * c ^ 2) := by
    simp only [Lg]
    have e : (1 - c ^ 2) * (derivative (derivative f)).eval c
        = 2 * k * c * (derivative f).eval c - lam * f.eval c := by
      rw [hk, hlam]; linarith
    linear_combination ((1 - c ^ 2) * (derivative f).eval c - k * c * f.eval c) * hcdef
      + (-(f.eval c * (1 - c ^ 2))) * e
  have hineq : (1 - c ^ 2) ^ 2 ≤ (c - z) ^ 2 * (lam * (1 - c ^ 2) - k ^ 2 * c ^ 2) := by
    have h2 := hLf c
    have h3 : (1 - c ^ 2) ^ 2 * (f.eval c) ^ 2 ≤ (1 - c ^ 2) ^ 2 * ((c - z) ^ 2 * Lg f c) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : (1 - c ^ 2) ^ 2 * ((c - z) ^ 2 * Lg f c)
        = (f.eval c) ^ 2 * ((c - z) ^ 2 * (lam * (1 - c ^ 2) - k ^ 2 * c ^ 2)) := by
      linear_combination (c - z) ^ 2 * hLc
    rw [h4] at h3
    have hf2 : 0 < (f.eval c) ^ 2 := by positivity
    rw [mul_comm ((1 - c ^ 2) ^ 2)] at h3
    exact le_of_mul_le_mul_left h3 hf2
  exact opt lam k c z (ρ ^ 2 + 2 * s + 1) (ρ ^ 2 - s ^ 2) R B hlampos (by positivity)
    hzc hc1' hcm hineq (by simp only [ρ, s, hlam, hk]; ring) (by simp only [ρ, s, hlam]; ring)
    rfl rfl

end SuperRamanujan227.Dev.K57.PartK
end

section
set_option autoImplicit false
open Polynomial
namespace SuperRamanujan227.Dev.K57
open SuperRamanujan227.Main
/-! ## Part K: Krasikov's argument for an abstract polynomial solving the ODE -/
alias krasikov_abstract := SuperRamanujan227.Dev.K57.PartK.krasikov_abstract

/-! ## Assembly -/
theorem theorem_5_7_dev (r : ℕ) (hr : 1 ≤ r) (γ : ℝ) (hγ : -1 < γ) :
    let s : ℝ := 2 * γ + 1
    let ρ : ℝ := 2 * (r : ℝ) + 2 * γ + 1
    let R : ℝ := Real.sqrt ((ρ ^ 2 + 2 * s + 1) * (ρ ^ 2 - s ^ 2))
    let B : ℝ := R / (ρ ^ 2 + 2 * s + 1)
    kthLargestRoot (jacobiSym γ r) 1 <
      B - 3 * (1 - B ^ 2) ^ ((2 : ℝ) / 3) * (2 * R) ^ (-(1 : ℝ) / 3) :=
  krasikov_abstract (jacobiSym γ r) r hr γ hγ (jac_realRooted γ hγ r).1 (jac_natDegree γ hγ r)
    (jac_realRooted γ hγ r).2 (jac_pos_of_one_le γ hγ r 1 le_rfl) (jac_ode γ r)

end SuperRamanujan227.Dev.K57
end

namespace SuperRamanujan227.Main

theorem chk_theorem_5_7 (r : ℕ) (hr : 1 ≤ r) (γ : ℝ) (hγ : -1 < γ) :
    let s : ℝ := 2 * γ + 1
    let ρ : ℝ := 2 * (r : ℝ) + 2 * γ + 1
    let R : ℝ := Real.sqrt ((ρ ^ 2 + 2 * s + 1) * (ρ ^ 2 - s ^ 2))
    let B : ℝ := R / (ρ ^ 2 + 2 * s + 1)
    kthLargestRoot (jacobiSym γ r) 1 <
      B - 3 * (1 - B ^ 2) ^ ((2 : ℝ) / 3) * (2 * R) ^ (-(1 : ℝ) / 3) :=
  SuperRamanujan227.Dev.K57.theorem_5_7_dev r hr γ hγ

end SuperRamanujan227.Main

theorem solution : type_of% @SuperRamanujan227.Main.chk_theorem_5_7 := @SuperRamanujan227.Main.chk_theorem_5_7
