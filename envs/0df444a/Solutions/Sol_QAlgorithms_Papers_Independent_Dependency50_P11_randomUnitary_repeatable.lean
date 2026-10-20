-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P11.randomUnitary_repeatable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:53:07.571894+00:00
-- url     : https://prove2.me/submissions/d8cd38b3-cf3e-4358-95a4-2d95a34ab38e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11

noncomputable section

open scoped Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P11 in
open QAlgorithms.Papers.Independent.Information100.P23 (Operator) in
theorem g53h_RU_repeatable {d : ℕ} (E : Superop (Fin d) (Fin d)) (hRU : IsRandomUnitary E) :
    HasFiniteRepeatableImplementation E := by
  classical
  obtain ⟨k, p, V, hp, hsum, hEV⟩ := hRU
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hsum
    · exact h
  let Um : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ :=
    Matrix.of fun x y => if x.1 = y.1 then (V x.1 : Operator d) x.2 y.2 else 0
  have hVu : ∀ a, star (V a : Operator d) * (V a : Operator d) = 1 :=
    fun a => Matrix.mem_unitaryGroup_iff'.1 (V a).2
  have hUm : Um ∈ Matrix.unitaryGroup (Fin k × Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext ⟨a, i⟩ ⟨b, j⟩
    have e := congrFun (congrFun (hVu a) i) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Fintype.sum_prod_type, Um, Matrix.of_apply] at e ⊢
    by_cases hab : a = b
    · subst hab
      rw [Finset.sum_eq_single a (fun c _ hc => by simp [hc]) (by simp)]
      simp only [↓reduceIte]
      rw [e]
      simp [Matrix.one_apply, Prod.ext_iff]
    · rw [Finset.sum_eq_zero]
      · simp [Matrix.one_apply, Prod.ext_iff, hab]
      · intro c _
        apply Finset.sum_eq_zero; intro l _
        by_cases h1 : c = a
        · subst h1; simp [hab]
        · simp [h1]
  let xi : Operator k := Matrix.diagonal (fun a => (p a : ℂ))
  have hxi : IsDensityMatrix xi := by
    refine ⟨?_, ?_⟩
    · rw [Matrix.posSemidef_diagonal_iff]; intro a; exact_mod_cast (hp a).1
    · simp [xi, Matrix.trace_diagonal]; exact_mod_cast hsum
  let D : MemoryDevice d k := ⟨hk, ⟨Um, hUm⟩, xi, hxi⟩
  have hjoint : ∀ rho : Operator d, jointStep D xi rho =
      fun x y => if x.1 = y.1 then (p x.1 : ℂ) * ((V x.1 : Operator d) * rho * (V x.1 : Operator d)ᴴ) x.2 y.2
        else 0 := by
    intro rho
    ext ⟨a, i⟩ ⟨b, j⟩
    simp only [jointStep, D, Matrix.mul_apply, Fintype.sum_prod_type, Um, Matrix.of_apply, xi, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, star_zero]
    have inner : ∀ x x1, (∑ x_2, ∑ x_3, if x_2 = x then if a = x_2 then (V a : Operator d) i x_3 *
        ((p x_2 : ℂ) * rho x_3 x1) else 0 else 0) =
        if a = x then (p a : ℂ) * ∑ x_3, (V a : Operator d) i x_3 * rho x_3 x1 else 0 := by
      intro x x1
      rw [Finset.sum_eq_single x (fun c _ hc => by simp [hc]) (by simp)]
      by_cases h : a = x
      · subst h; simp [Finset.mul_sum]; apply Finset.sum_congr rfl; intro _ _; ring
      · simp [h]
    simp only [inner]
    by_cases hab : a = b
    · subst hab
      rw [Finset.sum_eq_single a (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
      simp only [↓reduceIte, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
      simp; ring
    · rw [if_neg hab]
      apply Finset.sum_eq_zero; intro x _
      apply Finset.sum_eq_zero; intro x1 _
      by_cases h : a = x
      · subst h; simp [Ne.symm hab]
      · simp [h]
  have htr : ∀ (a : Fin k) (rho : Operator d),
      ((V a : Operator d) * rho * (V a : Operator d)ᴴ).trace = rho.trace := by
    intro a rho
    rw [Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose, hVu a, one_mul]
  have hR : ∀ rho : Operator d, IsDensityMatrix rho → traceRight (jointStep D xi rho) = xi := by
    intro rho hrho
    ext a b
    simp only [traceRight, hjoint, Matrix.of_apply]
    by_cases hab : a = b
    · subst hab
      simp only [↓reduceIte]
      rw [← Finset.mul_sum]
      have := htr a rho
      have h2 := hrho.2
      simp only [Matrix.trace, Matrix.diag] at this h2
      rw [this, h2]
      simp [xi]
    · simp [hab, xi]
  have hL : ∀ rho : Operator d, traceLeft (jointStep D xi rho) = E rho := by
    intro rho
    ext i j
    simp only [traceLeft, hjoint, Matrix.of_apply, ↓reduceIte, hEV, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul]
  have hmem : ∀ input : ℕ → Operator d, (∀ j, IsDensityMatrix (input j)) →
      ∀ n, memoryState D input n = xi := by
    intro input hin n
    induction n with
    | zero => rfl
    | succ n ih =>
      show traceRight (jointStep D (memoryState D input n) (input n)) = xi
      rw [ih, hR _ (hin n)]
  refine ⟨k, D, fun n input hin j _ => ?_⟩
  unfold outputState
  rw [hmem input hin j, hL]

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P11

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

/-- Theorem 1, PDF p.3 (finite-memory conclusion on p.4): every finite random-unitary
channel has one finite device implementing every individual use on every product history. -/
theorem solution {d : ℕ} (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) (hRU : IsRandomUnitary E) :
    HasFiniteRepeatableImplementation E := by
  exact g53h_RU_repeatable E hRU



end

