-- Prove2me | solution 1 for WeilConjectures.zetaOfCounts_mul_prod_charpolyRev_of_trace_formula
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T23:46:23.830161+00:00
-- url     : https://prove2.me/submissions/8c234554-6def-4868-b755-3ce774b2286f

import Mathlib
import Definitions.Def_WeilConjectures_zetaFunction

namespace WCAux

open Matrix

section Jacobi

variable {K : Type*} [Field K] {d : Type*} [Fintype d] [DecidableEq d]

/-- The matrix geometric series `∑ T^m Φ^m`, with entries in `K⟦T⟧`. -/
noncomputable def geomMat (Φ : Matrix d d K) : Matrix d d (PowerSeries K) :=
  Matrix.of fun i j => PowerSeries.mk fun m => (Φ ^ m) i j

theorem one_sub_mul_geomMat (Φ : Matrix d d K) :
    (1 - (PowerSeries.X : PowerSeries K) • Φ.map (PowerSeries.C : K →+* PowerSeries K)) *
      geomMat Φ = 1 := by
  ext i j m
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.smul_mul, Matrix.smul_apply,
    smul_eq_mul, map_sub, Matrix.mul_apply]
  cases m with
  | zero =>
    simp [geomMat, Matrix.one_apply]
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, map_sum]
    simp only [geomMat, Matrix.of_apply, PowerSeries.coeff_mk, Matrix.map_apply,
      PowerSeries.coeff_C_mul]
    rw [pow_succ', Matrix.mul_apply, sub_self, Matrix.one_apply]
    split_ifs <;> simp

theorem trace_geomMat_mul (Φ : Matrix d d K) :
    Matrix.trace (geomMat Φ * Φ.map (PowerSeries.C : K →+* PowerSeries K)) =
      PowerSeries.mk fun m => (Φ ^ (m + 1)).trace := by
  ext m
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, PowerSeries.coeff_mk,
    geomMat, Matrix.of_apply, Matrix.map_apply, PowerSeries.coeff_mul_C, pow_succ]

/-- The coefficient of `S` in `p (T + S)` is `p'(T)`. -/
theorem coeff_one_eval₂_add (p : Polynomial K) :
    (Polynomial.eval₂ (Polynomial.C.comp (PowerSeries.C : K →+* PowerSeries K))
        (Polynomial.C (PowerSeries.X : PowerSeries K) + Polynomial.X) p).coeff 1 =
      PowerSeries.derivative K (p : PowerSeries K) := by
  have h1 : Polynomial.eval₂ (Polynomial.C.comp (PowerSeries.C : K →+* PowerSeries K))
        (Polynomial.C (PowerSeries.X : PowerSeries K) + Polynomial.X) p =
      (p.map (PowerSeries.C : K →+* PowerSeries K)).comp
        (Polynomial.C (PowerSeries.X : PowerSeries K) + Polynomial.X) := by
    rw [Polynomial.comp, Polynomial.eval₂_map]
  rw [h1]
  have h2 : ∀ q : Polynomial (PowerSeries K), q.coeff 1 = (Polynomial.derivative q).eval 0 := by
    intro q
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
    simp
  rw [h2, Polynomial.derivative_comp, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.derivative_map]
  simp only [Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_X,
    zero_add, Polynomial.eval_one, one_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, add_zero]
  rw [Polynomial.eval_map, Polynomial.eval₂_C_X_eq_coe, PowerSeries.derivative_coe]

/-- **Jacobi's formula** for `P(T) = det (1 - T Φ)`:
`P'(T) = - P(T) · ∑_{m ≥ 0} tr(Φ^{m+1}) T^m` in `K⟦T⟧`. -/
theorem derivative_charpolyRev (Φ : Matrix d d K) :
    PowerSeries.derivative K ((Φ.charpolyRev : Polynomial K) : PowerSeries K) =
      ((Φ.charpolyRev : Polynomial K) : PowerSeries K) *
        (-(PowerSeries.mk fun m => (Φ ^ (m + 1)).trace)) := by
  classical
  set R := PowerSeries K with hR
  set T : R := PowerSeries.X with hT
  set ΦR : Matrix d d R := Φ.map (PowerSeries.C : K →+* R) with hΦR
  set A : Matrix d d R := 1 - T • ΦR with hA
  set G : Matrix d d R := geomMat Φ with hG
  have hAG : A * G = 1 := one_sub_mul_geomMat Φ
  set ψ : Polynomial K →+* Polynomial R :=
    Polynomial.eval₂RingHom (Polynomial.C.comp (PowerSeries.C : K →+* R))
      (Polynomial.C T + Polynomial.X) with hψ
  -- `det A` is `P` viewed as a power series
  have hdetA : A.det = ((Φ.charpolyRev : Polynomial K) : PowerSeries K) := by
    have : A = (Polynomial.coeToPowerSeries.ringHom (R := K)).mapMatrix
        (1 - (Polynomial.X : Polynomial K) • Φ.map Polynomial.C) := by
      ext i j : 1
      simp [hA, hΦR, hT, Matrix.one_apply, apply_ite]
      all_goals exact mul_comm _ _
    rw [this, ← RingHom.map_det]
    rfl
  -- factorisation of `1 - (T + S) Φ`
  have hfac : ψ.mapMatrix (1 - (Polynomial.X : Polynomial K) • Φ.map Polynomial.C) =
      (Polynomial.C : R →+* Polynomial R).mapMatrix A *
        (1 + (Polynomial.X : Polynomial R) • (-(G * ΦR)).map Polynomial.C) := by
    have e1 : ψ.mapMatrix (1 - (Polynomial.X : Polynomial K) • Φ.map Polynomial.C) =
        1 - (Polynomial.C T + Polynomial.X) • (Polynomial.C : R →+* Polynomial R).mapMatrix ΦR := by
      ext i j : 1
      simp [hψ, hΦR, Matrix.one_apply, apply_ite]
      all_goals exact mul_comm _ _
    have e2 : (Polynomial.C : R →+* Polynomial R).mapMatrix A =
        1 - Polynomial.C T • (Polynomial.C : R →+* Polynomial R).mapMatrix ΦR := by
      ext i j : 1
      simp [hA, Matrix.one_apply, apply_ite]
    have e3 : (-(G * ΦR)).map (Polynomial.C : R → Polynomial R) =
        -((Polynomial.C : R →+* Polynomial R).mapMatrix G *
          (Polynomial.C : R →+* Polynomial R).mapMatrix ΦR) := by
      rw [← map_mul (Polynomial.C : R →+* Polynomial R).mapMatrix G ΦR, ← map_neg]
      rfl
    have e4 : (Polynomial.C : R →+* Polynomial R).mapMatrix A *
        (Polynomial.C : R →+* Polynomial R).mapMatrix G = 1 := by
      rw [← map_mul, hAG, map_one]
    rw [e1, e3, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_neg, ← Matrix.mul_assoc,
      e4, Matrix.one_mul, e2, add_smul]
    simp only [smul_neg]
    abel
  have hdet : ψ Φ.charpolyRev = Polynomial.C A.det *
      (1 + (Polynomial.X : Polynomial R) • (-(G * ΦR)).map Polynomial.C).det := by
    rw [Matrix.charpolyRev, RingHom.map_det, hfac, Matrix.det_mul, ← RingHom.map_det]
  have hcoeff : (ψ Φ.charpolyRev).coeff 1 = A.det * Matrix.trace (-(G * ΦR)) := by
    rw [hdet, Polynomial.coeff_C_mul, Matrix.coeff_det_one_add_X_smul_one]
  have hJ := coeff_one_eval₂_add (K := K) Φ.charpolyRev
  have hψP : ψ Φ.charpolyRev =
      Polynomial.eval₂ (Polynomial.C.comp (PowerSeries.C : K →+* PowerSeries K))
        (Polynomial.C (PowerSeries.X : PowerSeries K) + Polynomial.X) Φ.charpolyRev := rfl
  rw [← hJ, ← hψP, hcoeff, hdetA, Matrix.trace_neg, trace_geomMat_mul]

end Jacobi

section ODE

variable {K : Type*} [Field K] [CharZero K]

/-- Uniqueness for the linear equation `Y' = Y g` in `K⟦T⟧`. -/
theorem ode_unique (Y U g : PowerSeries K)
    (hY : PowerSeries.derivative K Y = Y * g) (hU : PowerSeries.derivative K U = U * g)
    (h0 : PowerSeries.constantCoeff Y = PowerSeries.constantCoeff U) : Y = U := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simpa using h0
    | succ n =>
      have h1 := congrArg (PowerSeries.coeff n) hY
      have h2 := congrArg (PowerSeries.coeff n) hU
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at h1 h2
      have h4 : PowerSeries.coeff (n + 1) Y * ((n : K) + 1) =
          PowerSeries.coeff (n + 1) U * ((n : K) + 1) := by
        rw [h1, h2]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [ih p.1 (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp; omega)]
      exact mul_right_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n) h4

omit [CharZero K] in
/-- Logarithmic derivative of a finite product. -/
theorem derivative_prod {ι : Type*} (t : Finset ι) (f g : ι → PowerSeries K)
    (h : ∀ i ∈ t, PowerSeries.derivative K (f i) = f i * g i) :
    PowerSeries.derivative K (∏ i ∈ t, f i) = (∏ i ∈ t, f i) * ∑ i ∈ t, g i := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz,
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi)), h a (Finset.mem_insert_self a t)]
    simp only [smul_eq_mul]
    ring

end ODE

/-- **Rational expression of the zeta series from a trace formula.**
If `N_m = ∑_{i ∈ s} (-1)^i tr(Φ_i^m)` for all `m ≥ 1`, then
`Z · ∏_{i even} det(1 - T Φ_i) = ∏_{i odd} det(1 - T Φ_i)`. -/
theorem zetaOfCounts_map_mul_prod {K : Type*} [Field K] [CharZero K] (N : ℕ → ℕ) (s : Finset ℕ)
    (d : ℕ → ℕ) (Φ : (i : ℕ) → Matrix (Fin (d i)) (Fin (d i)) K)
    (htr : ∀ m : ℕ, 0 < m → (N m : K) = ∑ i ∈ s, (-1 : K) ^ i * ((Φ i) ^ m).trace) :
    PowerSeries.map (algebraMap ℚ K) (WeilConjectures.zetaOfCounts N) *
        ∏ i ∈ s.filter Even, (((Φ i).charpolyRev : Polynomial K) : PowerSeries K) =
      ∏ i ∈ s.filter Odd, (((Φ i).charpolyRev : Polynomial K) : PowerSeries K) := by
  set L : PowerSeries K :=
    PowerSeries.mk fun m => if m = 0 then (0 : K) else (N m : K) / (m : K) with hL
  have hL0 : PowerSeries.constantCoeff L = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hL, PowerSeries.coeff_mk, if_pos rfl]
  have hLs : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero' hL0
  set F : PowerSeries K := (PowerSeries.exp K).subst L with hF
  -- the zeta series over `K` is `exp L`
  have hmap : PowerSeries.map (algebraMap ℚ K) (WeilConjectures.zetaOfCounts N) = F := by
    have h0 : PowerSeries.HasSubst
        (PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else (N m : ℚ) / (m : ℚ)) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, if_pos rfl])
    have e1 : PowerSeries.map (algebraMap ℚ K) (WeilConjectures.zetaOfCounts N) =
        (PowerSeries.map (algebraMap ℚ K) (PowerSeries.exp ℚ)).subst
          (PowerSeries.map (algebraMap ℚ K)
            (PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else (N m : ℚ) / (m : ℚ))) :=
      PowerSeries.map_subst h0 _
    have e2 : PowerSeries.map (algebraMap ℚ K)
        (PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else (N m : ℚ) / (m : ℚ)) = L := by
      ext m
      rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, hL, PowerSeries.coeff_mk]
      split_ifs with hm
      · simp
      · simp
    rw [e1, e2, PowerSeries.map_exp]
  -- derivative of `L`
  set τ : ℕ → PowerSeries K := fun i => PowerSeries.mk fun m => ((Φ i) ^ (m + 1)).trace with hτ
  have hdL : PowerSeries.derivative K L =
      (∑ i ∈ s.filter Even, τ i) - ∑ i ∈ s.filter Odd, τ i := by
    ext m
    have hm : ((m : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    rw [PowerSeries.coeff_derivative, hL, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero m),
      map_sub, map_sum, map_sum]
    simp only [hτ, PowerSeries.coeff_mk]
    have h1 : (N (m + 1) : K) / ((m + 1 : ℕ) : K) * ((m : K) + 1) = (N (m + 1) : K) := by
      push_cast
      field_simp
    rw [h1, htr (m + 1) (Nat.succ_pos m), ← Finset.sum_filter_add_sum_filter_not s Even]
    have hodd : s.filter (fun i => ¬ Even i) = s.filter Odd :=
      Finset.filter_congr fun i _ => Nat.not_even_iff_odd
    rw [hodd, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2.neg_one_pow, one_mul]
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2.neg_one_pow, neg_one_mul]
  have hP : ∀ i, PowerSeries.derivative K (((Φ i).charpolyRev : Polynomial K) : PowerSeries K) =
      (((Φ i).charpolyRev : Polynomial K) : PowerSeries K) * (-(τ i)) :=
    fun i => derivative_charpolyRev (Φ i)
  have hdE := derivative_prod (s.filter Even)
    (fun i => (((Φ i).charpolyRev : Polynomial K) : PowerSeries K)) (fun i => -(τ i))
    (fun i _ => hP i)
  have hdO := derivative_prod (s.filter Odd)
    (fun i => (((Φ i).charpolyRev : Polynomial K) : PowerSeries K)) (fun i => -(τ i))
    (fun i _ => hP i)
  have hdF : PowerSeries.derivative K F = F * PowerSeries.derivative K L := by
    rw [hF, PowerSeries.derivative_subst hLs, PowerSeries.derivative_exp]
  have hF0 : PowerSeries.constantCoeff F = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hF, PowerSeries.coeff_subst' hLs,
      finsum_eq_single _ 0]
    · simp
    · intro e he
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hL0, zero_pow he, smul_zero]
  have hP0 : ∀ i, PowerSeries.constantCoeff
      (((Φ i).charpolyRev : Polynomial K) : PowerSeries K) = 1 := by
    intro i
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  rw [hmap]
  refine ode_unique _ _ (∑ i ∈ s.filter Odd, -(τ i)) ?_ hdO ?_
  · rw [Derivation.leibniz, hdE, hdF, hdL]
    simp only [smul_eq_mul, Finset.sum_neg_distrib]
    ring
  · rw [map_mul, map_prod, map_prod, hF0, one_mul]
    rw [Finset.prod_congr rfl (fun i _ => hP0 i), Finset.prod_congr rfl (fun i _ => hP0 i)]
    simp

end WCAux

open WeilConjectures

theorem solution {K : Type*} [Field K]
    [CharZero K] (N : ℕ → ℕ) (s : Finset ℕ) (d : ℕ → ℕ)
    (Φ : (i : ℕ) → Matrix (Fin (d i)) (Fin (d i)) K)
    (htr : ∀ m : ℕ, 0 < m → (N m : K) = ∑ i ∈ s, (-1 : K) ^ i * ((Φ i) ^ m).trace) :
    PowerSeries.map (algebraMap ℚ K) (zetaOfCounts N) *
        ∏ i ∈ s.filter Even, (((Φ i).charpolyRev : Polynomial K) : PowerSeries K) =
      ∏ i ∈ s.filter Odd, (((Φ i).charpolyRev : Polynomial K) : PowerSeries K) :=
  WCAux.zetaOfCounts_map_mul_prod N s d Φ htr
