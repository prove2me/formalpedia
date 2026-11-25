-- Prove2me | solution 1 for TrigPolyZeroCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:32:17.637572+00:00
-- url     : https://prove2.me/submissions/b0eb0232-2f5b-4679-9978-ac0438ff338d

module
public import Definitions.Def_PHarmonicPoly_TrigPolyToComplexPoly
public import Definitions.Def_PHarmonicPoly_TrigPolySmooth
public import Definitions.Def_PHarmonicPoly_TrigPolyZeroCount
public import Theorems.Thm_TrigPolySmooth
public import Theorems.Thm_TrigPolyToComplexPoly


set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution {m : ℕ} {T : ℝ → ℝ} (hT : TrigPolyLe m T)
    (hTne : ∃ s : ℝ, T s ≠ 0)
    {t₀ : ℝ} {Z : Finset ℝ}
    (hZmem : ∀ z ∈ Z, z ∈ Set.Ico t₀ (t₀ + 2 * Real.pi))
    (hZzero : ∀ z ∈ Z, T z = 0)
    {t₁ : ℝ} (ht₁mem : t₁ ∈ Set.Ico t₀ (t₀ + 2 * Real.pi)) (ht₁notZ : t₁ ∉ Z)
    (ht₁zero : T t₁ = 0) (ht₁deriv : deriv T t₁ = 0) :
    Z.card + 2 ≤ 2 * m := by
  classical
  obtain ⟨Q, hdeg, heval⟩ := TrigPolyToComplexPoly hT
  obtain ⟨s, hs⟩ := hTne
  have hQne : Q ≠ 0 := by
    intro h0
    have h := heval s
    rw [h0] at h
    simp only [Polynomial.eval_zero] at h
    have hTs : ((T s : ℝ) : ℂ) ≠ 0 := by
      simpa using hs
    exact (mul_ne_zero (Complex.exp_ne_zero ((m : ℂ) * (s : ℂ) * Complex.I)) hTs) h.symm
  have hnd : Q.natDegree ≤ 2 * m := Polynomial.natDegree_le_iff_degree_le.mpr hdeg
  have hinj : ∀ x y : ℝ, x ∈ Set.Ico t₀ (t₀ + 2 * Real.pi) →
      y ∈ Set.Ico t₀ (t₀ + 2 * Real.pi) →
      Complex.exp ((x : ℂ) * Complex.I) = Complex.exp ((y : ℂ) * Complex.I) → x = y := by
    intro x y hx hy hxy
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hxy
    have h2 : (x : ℂ) * Complex.I
        = ((y : ℂ) + (k : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
      rw [hk]
      ring
    have h3 : (x : ℂ) = (y : ℂ) + (k : ℂ) * (2 * (Real.pi : ℂ)) :=
      mul_right_cancel₀ Complex.I_ne_zero h2
    have h4 : x = y + (k : ℝ) * (2 * Real.pi) := by
      have hc : ((x : ℝ) : ℂ) = ((y + (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
        push_cast
        linear_combination h3
      exact Complex.ofReal_inj.mp hc
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have h2pi : (0 : ℝ) < 2 * Real.pi := by linarith
    have hkr1 : (k : ℝ) < 1 := by
      have hb : (k : ℝ) * (2 * Real.pi) < 1 * (2 * Real.pi) := by
        have := hx.2
        have := hy.1
        linarith
      exact lt_of_mul_lt_mul_right hb (le_of_lt h2pi)
    have hkr2 : (-1 : ℝ) < (k : ℝ) := by
      have hb : (-1 : ℝ) * (2 * Real.pi) < (k : ℝ) * (2 * Real.pi) := by
        have := hx.1
        have := hy.2
        linarith
      exact lt_of_mul_lt_mul_right hb (le_of_lt h2pi)
    have hk0 : k = 0 := by
      have c1 : k < 1 := by exact_mod_cast hkr1
      have c2 : (-1 : ℤ) < k := by exact_mod_cast hkr2
      omega
    rw [hk0] at h4
    simpa using h4
  have hroot : ∀ z : ℝ, T z = 0 → Q.IsRoot (Complex.exp ((z : ℂ) * Complex.I)) := by
    intro z hz
    have h := heval z
    rw [hz] at h
    simpa [Polynomial.IsRoot] using h
  have hre : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) (((1 : ℝ) : ℂ)) t₁ :=
    (hasDerivAt_id t₁).ofReal_comp
  have hcurve : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((t₁ : ℂ) * Complex.I) * Complex.I) t₁ := by
    have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I)
        (((1 : ℝ) : ℂ) * Complex.I) t₁ := hre.mul_const Complex.I
    simpa using hlin.cexp
  have hFderiv : HasDerivAt
      (fun t : ℝ => Polynomial.eval (Complex.exp ((t : ℂ) * Complex.I)) Q)
      ((Complex.exp ((t₁ : ℂ) * Complex.I) * Complex.I) •
        Polynomial.eval (Complex.exp ((t₁ : ℂ) * Complex.I)) (Polynomial.derivative Q)) t₁ := by
    have h := HasDerivAt.scomp (g₁ := fun w : ℂ => Polynomial.eval w Q) t₁
      (Polynomial.hasDerivAt Q (Complex.exp ((t₁ : ℂ) * Complex.I))) hcurve
    exact h
  have hTd : HasDerivAt T (deriv T t₁) t₁ :=
    (((TrigPolySmooth hT).differentiable (by simp)) t₁).hasDerivAt
  have hGderiv : HasDerivAt
      (fun t : ℝ => Complex.exp ((m : ℂ) * (t : ℂ) * Complex.I) * ((T t : ℝ) : ℂ))
      (0 : ℂ) t₁ := by
    have hlin : HasDerivAt (fun t : ℝ => (m : ℂ) * (t : ℂ) * Complex.I)
        ((m : ℂ) * ((1 : ℝ) : ℂ) * Complex.I) t₁ :=
      (hre.const_mul ((m : ℂ))).mul_const Complex.I
    have hTc : HasDerivAt (fun t : ℝ => ((T t : ℝ) : ℂ)) (((deriv T t₁ : ℝ) : ℂ)) t₁ :=
      hTd.ofReal_comp
    have hprod := hlin.cexp.mul hTc
    rw [ht₁zero, ht₁deriv] at hprod
    convert hprod using 1
    all_goals first
      | rfl
      | simp
  have hFG : (fun t : ℝ => Polynomial.eval (Complex.exp ((t : ℂ) * Complex.I)) Q)
      = fun t : ℝ => Complex.exp ((m : ℂ) * (t : ℂ) * Complex.I) * ((T t : ℝ) : ℂ) :=
    funext heval
  have hderivzero :
      Polynomial.eval (Complex.exp ((t₁ : ℂ) * Complex.I)) (Polynomial.derivative Q) = 0 := by
    have h1 := (hFG ▸ hFderiv).unique hGderiv
    rw [smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left
      (mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero)
  have hmult : 2 ≤ Q.rootMultiplicity (Complex.exp ((t₁ : ℂ) * Complex.I)) := by
    rw [Polynomial.le_rootMultiplicity_iff hQne]
    obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr (hroot t₁ ht₁zero)
    have hdQ : Polynomial.derivative Q
        = R + (Polynomial.X - Polynomial.C (Complex.exp ((t₁ : ℂ) * Complex.I)))
            * Polynomial.derivative R := by
      rw [hR, Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
        Polynomial.derivative_C]
      ring
    have hRroot : R.IsRoot (Complex.exp ((t₁ : ℂ) * Complex.I)) := by
      have h := hderivzero
      rw [hdQ] at h
      simpa [Polynomial.IsRoot] using h
    obtain ⟨S, hS⟩ := Polynomial.dvd_iff_isRoot.mpr hRroot
    exact ⟨S, by rw [hR, hS]; ring⟩
  have hcount : ∀ W : Finset ℂ, (∀ w ∈ W, Q.IsRoot w) →
      ∑ w ∈ W, Q.rootMultiplicity w ≤ Q.natDegree := by
    intro W hW
    have hsub : W ⊆ Q.roots.toFinset := by
      intro w hw
      simpa [Multiset.mem_toFinset, Polynomial.mem_roots, hQne] using hW w hw
    calc ∑ w ∈ W, Q.rootMultiplicity w
        = ∑ w ∈ W, Multiset.count w Q.roots :=
          Finset.sum_congr rfl (fun w _ => (Polynomial.count_roots Q).symm)
      _ ≤ ∑ w ∈ Q.roots.toFinset, Multiset.count w Q.roots :=
          Finset.sum_le_sum_of_subset hsub
      _ = Multiset.card Q.roots := Multiset.toFinset_sum_count_eq _
      _ ≤ Q.natDegree := Polynomial.card_roots' Q
  have hcard : (Z.image (fun z : ℝ => Complex.exp ((z : ℂ) * Complex.I))).card = Z.card := by
    refine Finset.card_image_of_injOn (fun x hx y hy hxy => ?_)
    exact hinj x y (hZmem x (Finset.mem_coe.mp hx)) (hZmem y (Finset.mem_coe.mp hy)) hxy
  have hWroot : ∀ w ∈ Z.image (fun z : ℝ => Complex.exp ((z : ℂ) * Complex.I)), Q.IsRoot w := by
    intro w hw
    obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp hw
    exact hzeq ▸ hroot z (hZzero z hz)
  have hw1notW : Complex.exp ((t₁ : ℂ) * Complex.I)
      ∉ Z.image (fun z : ℝ => Complex.exp ((z : ℂ) * Complex.I)) := by
    intro hmem
    obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp hmem
    exact ht₁notZ ((hinj z t₁ (hZmem z hz) ht₁mem hzeq) ▸ hz)
  have hins : ∀ w ∈ insert (Complex.exp ((t₁ : ℂ) * Complex.I))
      (Z.image (fun z : ℝ => Complex.exp ((z : ℂ) * Complex.I))), Q.IsRoot w := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw'
    · exact hroot t₁ ht₁zero
    · exact hWroot w hw'
  have hle := hcount _ hins
  rw [Finset.sum_insert hw1notW] at hle
  have hone : ∀ w ∈ Z.image (fun z : ℝ => Complex.exp ((z : ℂ) * Complex.I)),
      1 ≤ Q.rootMultiplicity w :=
    fun w hw => (Polynomial.rootMultiplicity_pos hQne).2 (hWroot w hw)
  have hcard2 : (Z.image (fun z : ℝ => Complex.exp ((z : ℂ) * Complex.I))).card
      ≤ ∑ w ∈ Z.image (fun z : ℝ => Complex.exp ((z : ℂ) * Complex.I)),
          Q.rootMultiplicity w := by
    simpa using Finset.card_nsmul_le_sum _ _ 1 hone
  rw [hcard] at hcard2
  omega
