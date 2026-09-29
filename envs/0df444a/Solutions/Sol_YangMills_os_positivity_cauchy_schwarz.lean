-- Prove2me | solution 1 for YangMills.os_positivity_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T19:59:18.334594+00:00
-- url     : https://prove2.me/submissions/f8b085b0-8b84-4030-a35d-6e091846bcfb

import Definitions.Def_YangMills_Wilson_lattice

open MeasureTheory Filter Topology Finset
open YangMills

/-- Appending two one-element tuples gives the corresponding two-element tuple. -/
private lemma append_one_one {α : Type*} (a b : α) : Fin.append ![a] ![b] = ![a, b] := by
  funext i
  fin_cases i <;> simp [Fin.append, Fin.addCases]

/-- Reflection positivity, specialised to two one-element families: the `2 × 2` Gram matrix
built from `f`, `g` and their time reflections defines a non-negative real quadratic form. -/
private lemma refl_pos_two (Q : OSTheory) (f g fθ gθ : TestFn)
    (hf : PosTime f) (hg : PosTime g)
    (hfθ : ∀ x : Spacetime, fθ x = f (timeReflect x))
    (hgθ : ∀ x : Spacetime, gθ x = g (timeReflect x)) (c₀ c₁ : ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧
      (starRingEnd ℂ) c₀ * c₀ * Q.S 2 ![fθ, f] + (starRingEnd ℂ) c₀ * c₁ * Q.S 2 ![fθ, g]
        + (starRingEnd ℂ) c₁ * c₀ * Q.S 2 ![gθ, f]
        + (starRingEnd ℂ) c₁ * c₁ * Q.S 2 ![gθ, g] = (r : ℂ) := by
  obtain ⟨r, hr0, hr⟩ :=
    Q.refl_pos 2 (fun _ => 1) ![![f], ![g]] ![![fθ], ![gθ]] ![c₀, c₁]
      (by
        intro j i
        fin_cases j <;> fin_cases i <;> simpa using ‹_›)
      (by
        intro j i x
        fin_cases j <;> fin_cases i <;> simp [hfθ x, hgθ x])
  refine ⟨r, hr0, ?_⟩
  rw [← hr]
  simp [Fin.sum_univ_two, append_one_one]
  ring

theorem solution (Q : OSTheory) (f g fθ gθ : TestFn)
    (hf : PosTime f) (hg : PosTime g)
    (hfθ : ∀ x : Spacetime, fθ x = f (timeReflect x))
    (hgθ : ∀ x : Spacetime, gθ x = g (timeReflect x)) :
    ‖Q.S 2 ![fθ, g]‖ ≤ Real.sqrt (Q.S 2 ![fθ, f]).re * Real.sqrt (Q.S 2 ![gθ, g]).re := by
  set A := Q.S 2 ![fθ, f] with hAdef
  set B := Q.S 2 ![fθ, g] with hBdef
  set C := Q.S 2 ![gθ, f] with hCdef
  set D := Q.S 2 ![gθ, g] with hDdef
  have key := refl_pos_two Q f g fθ gθ hf hg hfθ hgθ
  -- the Gram form is real and non-negative for every choice of coefficients
  have hre : ∀ c₀ c₁ : ℂ, 0 ≤ ((starRingEnd ℂ) c₀ * c₀ * A + (starRingEnd ℂ) c₀ * c₁ * B
      + (starRingEnd ℂ) c₁ * c₀ * C + (starRingEnd ℂ) c₁ * c₁ * D).re := by
    intro c₀ c₁
    obtain ⟨r, hr0, hr⟩ := key c₀ c₁
    rw [hr]
    simpa using hr0
  have him : ∀ c₀ c₁ : ℂ, ((starRingEnd ℂ) c₀ * c₀ * A + (starRingEnd ℂ) c₀ * c₁ * B
      + (starRingEnd ℂ) c₁ * c₀ * C + (starRingEnd ℂ) c₁ * c₁ * D).im = 0 := by
    intro c₀ c₁
    obtain ⟨r, _, hr⟩ := key c₀ c₁
    rw [hr]
    simp
  -- the diagonal entries are non-negative reals
  have hA0 : 0 ≤ A.re := by simpa using hre 1 0
  have hAim : A.im = 0 := by simpa using him 1 0
  have hD0 : 0 ≤ D.re := by simpa using hre 0 1
  have hDim : D.im = 0 := by simpa using him 0 1
  -- hermitian symmetry of the off-diagonal entries
  have h11 := him 1 1
  have h1I := him 1 Complex.I
  simp [Complex.add_im, Complex.mul_im, hAim, hDim] at h11 h1I
  have hCim : C.im = -B.im := by linarith
  have hCre : C.re = B.re := by linarith
  -- positivity of the quadratic polynomial obtained from the coefficients `(t, -conj B)`
  have hquad : ∀ t : ℝ, 0 ≤ A.re * (t * t) + (-2 * (B.re ^ 2 + B.im ^ 2)) * t
      + (B.re ^ 2 + B.im ^ 2) * D.re := by
    intro t
    have h := hre (t : ℂ) (-(starRingEnd ℂ) B)
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im, hAim, hDim, hCim, hCre] at h
    nlinarith [h]
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  have hnormsq : ‖B‖ ^ 2 = B.re ^ 2 + B.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hkey : ‖B‖ ^ 2 ≤ A.re * D.re := by
    rcases eq_or_lt_of_le (by positivity : (0:ℝ) ≤ B.re ^ 2 + B.im ^ 2) with hm | hm
    · rw [hnormsq, ← hm]
      positivity
    · rw [hnormsq]
      nlinarith [hdisc, hm]
  calc ‖B‖ = Real.sqrt (‖B‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (A.re * D.re) := Real.sqrt_le_sqrt hkey
    _ = Real.sqrt A.re * Real.sqrt D.re := Real.sqrt_mul hA0 _
