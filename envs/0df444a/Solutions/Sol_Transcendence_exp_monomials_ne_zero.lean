-- Prove2me | solution 1 for Transcendence.exp_monomials_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T09:17:26.579303+00:00
-- url     : https://prove2.me/submissions/2db6f352-0009-4cf7-b090-65ca30e02206

import Mathlib
import Theorems.Thm_FourExp_expPoly_ne_zero

/-!
# Non-vanishing of exponential polynomials in several variables

The frequencies `ω_t = Σ tᵢ xᵢ` are pairwise distinct (`ℚ`-independence). The direction
`u = (θ^{e(ν)})_ν`, with `θ` outside the roots of finitely many non-zero polynomials, keeps the
numbers `⟨ω_t, u⟩` pairwise distinct and has `u_{k₀} ≠ 0`. On the line `a ↦ a • u` the function
is a one-variable exponential polynomial, non-zero somewhere by `FourExp.expPoly_ne_zero`. An
entire function with a non-zero value has a non-zero derivative at `0` (Taylor series), and that
derivative is `iteratedFDeriv ℂ k F 0 (u, …, u)`.
-/

namespace ExpMonomialsNeZero

open Polynomial

/-- The frequencies `t ↦ Σᵢ tᵢ xᵢ` are injective when the `xᵢ` are `ℚ`-independent. -/
theorem freq_injective {ι : Type*} [Fintype ι] {d₁ T₁ : ℕ} (x : Fin d₁ → ι → ℂ)
    (hx : LinearIndependent ℚ x) :
    Function.Injective (fun (t : Fin d₁ → Fin (T₁ + 1)) (ν : ι) =>
      ∑ i, ((t i : ℕ) : ℂ) * x i ν) := by
  intro t t' h
  have h0 : ∑ i, (((t i : ℕ) : ℚ) - ((t' i : ℕ) : ℚ)) • x i = 0 := by
    funext ν
    have hν := congrFun h ν
    simp only [Finset.sum_apply, Pi.smul_apply, Rat.smul_def, Pi.zero_apply, Rat.cast_sub,
      Rat.cast_natCast, sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hν
  have h1 := Fintype.linearIndependent_iff.mp hx _ h0
  funext i
  apply Fin.ext
  exact_mod_cast sub_eq_zero.mp (h1 i)

/-- The polynomial `Σ_ν v_ν X^{e(ν)}`, along the enumeration `e` of `ι`. -/
noncomputable def linePoly {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℂ[X] :=
  ∑ ν, C (v ν) * X ^ (Fintype.equivFin ι ν : ℕ)

theorem eval_linePoly {ι : Type*} [Fintype ι] (v : ι → ℂ) (θ : ℂ) :
    (linePoly v).eval θ = ∑ ν, v ν * θ ^ (Fintype.equivFin ι ν : ℕ) := by
  simp [linePoly, eval_finsetSum]

theorem linePoly_ne_zero {ι : Type*} [Fintype ι] {v : ι → ℂ} (hv : v ≠ 0) :
    linePoly v ≠ 0 := by
  classical
  intro h
  apply hv
  funext ν
  have h' := congrArg (fun f : ℂ[X] => f.coeff (Fintype.equivFin ι ν : ℕ)) h
  simpa [linePoly, finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj] using h'

/-- A direction `u` with `u k₀ ≠ 0` along which distinct frequencies stay distinct. -/
theorem exists_direction {ι : Type*} [Fintype ι] {T : Type*} [Fintype T]
    (ω : T → ι → ℂ) (hω : Function.Injective ω) (k₀ : ι) :
    ∃ u : ι → ℂ, u k₀ ≠ 0 ∧ Function.Injective (fun t => ∑ ν, ω t ν * u ν) := by
  classical
  let S : Finset (T × T) := Finset.univ.filter (fun pr => pr.1 ≠ pr.2)
  let Q : ℂ[X] := X * ∏ pr ∈ S, linePoly (ω pr.1 - ω pr.2)
  have hQ : Q ≠ 0 := by
    refine mul_ne_zero X_ne_zero (Finset.prod_ne_zero_iff.mpr fun pr hpr => ?_)
    refine linePoly_ne_zero (sub_ne_zero.mpr fun h => ?_)
    exact (Finset.mem_filter.mp hpr).2 (hω h)
  obtain ⟨θ, hθ⟩ : ∃ θ, Q.eval θ ≠ 0 := by
    by_contra h
    exact hQ (Polynomial.funext fun r => by
      by_contra hr
      exact h ⟨r, by simpa using hr⟩)
  have hθ' : θ ≠ 0 ∧ ∀ pr ∈ S, (linePoly (ω pr.1 - ω pr.2)).eval θ ≠ 0 := by
    have h := hθ
    simp only [Q, eval_mul, eval_X, eval_prod] at h
    exact ⟨left_ne_zero_of_mul h, Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h)⟩
  refine ⟨fun ν => θ ^ (Fintype.equivFin ι ν : ℕ), pow_ne_zero _ hθ'.1, fun t t' h => ?_⟩
  by_contra hne
  have hmem : (t, t') ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
  apply hθ'.2 _ hmem
  rw [eval_linePoly]
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr h

/-- The `n`-th derivative at `0` of `a ↦ F (a • u)` is `iteratedFDeriv ℂ n F 0 (u, …, u)`. -/
theorem iteratedDeriv_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → ℂ} (u : E) (n : ℕ) (hF : ContDiff ℂ n F) :
    iteratedDeriv n (fun a : ℂ => F (a • u)) 0 = iteratedFDeriv ℂ n F 0 (fun _ => u) := by
  have hcomp : (fun a : ℂ => F (a • u)) = F ∘ ContinuousLinearMap.toSpanSingleton ℂ u := by
    funext a
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  rw [hcomp, iteratedDeriv_eq_iteratedFDeriv,
    ContinuousLinearMap.iteratedFDeriv_comp_right _ hF _ le_rfl]
  simp

/-- An entire function with a non-zero value has a non-zero derivative at `0`. -/
theorem exists_iteratedDeriv_ne_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g) {w : ℂ}
    (hw : g w ≠ 0) : ∃ n, iteratedDeriv n g 0 ≠ 0 := by
  by_contra h
  apply hw
  rw [← Complex.taylorSeries_eq_of_entire' (c := 0) (z := w) hg]
  have h0 : ∀ n, iteratedDeriv n g 0 = 0 := fun n => by
    by_contra hn
    exact h ⟨n, hn⟩
  simp [h0]

end ExpMonomialsNeZero

theorem solution {ι : Type*} [Fintype ι] {d₁ : ℕ} (x : Fin d₁ → ι → ℂ)
    (hx : LinearIndependent ℚ x) (k₀ : ι) {T₀ T₁ : ℕ}
    (p : Fin (T₀ + 1) × (Fin d₁ → Fin (T₁ + 1)) → ℂ) (hp : p ≠ 0) :
    ∃ k : ℕ, iteratedFDeriv ℂ k (fun z : ι → ℂ => ∑ l, p l * (z k₀ ^ (l.1 : ℕ) *
      Complex.exp (∑ ν, (∑ i, ((l.2 i : ℕ) : ℂ) * x i ν) * z ν))) 0 ≠ 0 := by
  classical
  set F : (ι → ℂ) → ℂ := fun z => ∑ l, p l * (z k₀ ^ (l.1 : ℕ) *
      Complex.exp (∑ ν, (∑ i, ((l.2 i : ℕ) : ℂ) * x i ν) * z ν)) with hFdef
  let ω : (Fin d₁ → Fin (T₁ + 1)) → ι → ℂ := fun t ν => ∑ i, ((t i : ℕ) : ℂ) * x i ν
  have hω : Function.Injective ω := ExpMonomialsNeZero.freq_injective x hx
  obtain ⟨u, hu0, hu⟩ := ExpMonomialsNeZero.exists_direction ω hω k₀
  have hFc : ∀ n : ℕ, ContDiff ℂ n F := fun n => by
    rw [hFdef]
    fun_prop
  have hFd : Differentiable ℂ F := by
    rw [hFdef]
    fun_prop
  have hg : Differentiable ℂ (fun a : ℂ => F (a • u)) := by fun_prop
  let E := Fintype.equivFin (Fin d₁ → Fin (T₁ + 1))
  obtain ⟨w, hw⟩ := FourExp.expPoly_ne_zero (fun _ => T₀ + 1)
    (fun j => ∑ ν, ω (E.symm j) ν * u ν) (hu.comp E.symm.injective)
    (fun j i => p (i, E.symm j) * u k₀ ^ (i : ℕ)) (by
      obtain ⟨l, hl⟩ := Function.ne_iff.mp hp
      refine ⟨E l.2, l.1, mul_ne_zero ?_ (pow_ne_zero _ hu0)⟩
      simpa using hl)
  have hw' : ∑ t, ∑ τ : Fin (T₀ + 1), p (τ, t) * u k₀ ^ (τ : ℕ) * w ^ (τ : ℕ) *
      Complex.exp ((∑ ν, ω t ν * u ν) * w) ≠ 0 := by
    rw [← E.symm.sum_comp (fun t => ∑ τ : Fin (T₀ + 1), p (τ, t) * u k₀ ^ (τ : ℕ) *
      w ^ (τ : ℕ) * Complex.exp ((∑ ν, ω t ν * u ν) * w))]
    exact hw
  have hFw : F (w • u) = ∑ t, ∑ τ : Fin (T₀ + 1), p (τ, t) * u k₀ ^ (τ : ℕ) * w ^ (τ : ℕ) *
      Complex.exp ((∑ ν, ω t ν * u ν) * w) := by
    rw [hFdef]
    dsimp only
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun τ _ => ?_
    have hexp : (∑ ν, (∑ i, ((t i : ℕ) : ℂ) * x i ν) * (w • u) ν) =
        (∑ ν, ω t ν * u ν) * w := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun ν _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, ω]
      ring
    rw [hexp, Pi.smul_apply, smul_eq_mul, mul_pow]
    ring
  obtain ⟨n, hn⟩ := ExpMonomialsNeZero.exists_iteratedDeriv_ne_zero hg (hFw ▸ hw')
  refine ⟨n, fun h0 => hn ?_⟩
  rw [ExpMonomialsNeZero.iteratedDeriv_line u n (hFc n), h0]
  simp
