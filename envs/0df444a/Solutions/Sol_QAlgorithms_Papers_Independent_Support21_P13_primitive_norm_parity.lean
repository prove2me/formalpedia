-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P13.primitive_norm_parity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T10:19:42.576084+00:00
-- url     : https://prove2.me/submissions/b2c62fd4-01f8-4271-9501-d77a77187b66

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P13
noncomputable section

open scoped Classical

open QAlgorithms.Papers.Independent.Support21.P13

namespace G68Z

abbrev ω : ℂ := QAlgorithms.gateT true true
abbrev s : ℝ := Real.sqrt 2

lemma s_sq : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
lemma s_mul : s * s = 2 := Real.mul_self_sqrt (by norm_num)

lemma omega_eq : ω = ⟨s / 2, s / 2⟩ := by
  have h : ω = Complex.exp (Complex.I * Real.pi / 4) := by
    simp [ω, QAlgorithms.gateT, Matrix.diagonal_apply_eq]
  rw [h, show Complex.I * Real.pi / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  apply Complex.ext <;> simp [s]

lemma omega_re : ω.re = s / 2 := by rw [omega_eq]
lemma omega_im : ω.im = s / 2 := by rw [omega_eq]

lemma omega_sq : ω ^ 2 = Complex.I := by
  apply Complex.ext <;> simp [sq, Complex.mul_re, Complex.mul_im, omega_re, omega_im] <;>
    nlinarith [s_mul]

lemma omega_four : ω ^ 4 = -1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, omega_sq, Complex.I_sq]

lemma sqrt2_eq : ((s : ℝ) : ℂ) = ω - ω ^ 3 := by
  have h3 : ω ^ 3 = ω ^ 2 * ω := by ring
  rw [h3, omega_sq]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, omega_re, omega_im] <;> ring

/-- coordinates of a product -/
def cmul (a b : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![a 0 * b 0 - (a 1 * b 3 + a 2 * b 2 + a 3 * b 1),
    a 0 * b 1 + a 1 * b 0 - (a 2 * b 3 + a 3 * b 2),
    a 0 * b 2 + a 1 * b 1 + a 2 * b 0 - a 3 * b 3,
    a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0]

lemma cv_mul (a b : Fin 4 → ℤ) : coordinateValue a * coordinateValue b = coordinateValue (cmul a b) := by
  simp only [coordinateValue, cmul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  linear_combination ((a 1 * b 3 + a 2 * b 2 + a 3 * b 1 : ℂ) + (a 2 * b 3 + a 3 * b 2 : ℂ) * ω +
    (a 3 * b 3 : ℂ) * ω ^ 2) * omega_four

lemma cv_add (a b : Fin 4 → ℤ) : coordinateValue a + coordinateValue b = coordinateValue (a + b) := by
  simp only [coordinateValue, Pi.add_apply]; push_cast; ring

lemma cv_neg (a : Fin 4 → ℤ) : -coordinateValue a = coordinateValue (-a) := by
  simp only [coordinateValue, Pi.neg_apply]; push_cast; ring

lemma cv_re (a : Fin 4 → ℤ) : (coordinateValue a).re = a 0 + (a 1 - a 3) * (s / 2) := by
  have h3 : ω ^ 3 = ω ^ 2 * ω := by ring
  simp only [coordinateValue, h3, omega_sq]
  simp [Complex.mul_re, Complex.mul_im, omega_re, omega_im]; ring

lemma cv_im (a : Fin 4 → ℤ) : (coordinateValue a).im = a 2 + (a 1 + a 3) * (s / 2) := by
  have h3 : ω ^ 3 = ω ^ 2 * ω := by ring
  simp only [coordinateValue, h3, omega_sq]
  simp [Complex.mul_re, Complex.mul_im, omega_re, omega_im]; ring

lemma int_sqrt2 (m n : ℤ) (h : (m : ℝ) + n * s = 0) : m = 0 ∧ n = 0 := by
  by_cases hn : n = 0
  · subst hn; simp at h; exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    apply irrational_sqrt_two
    refine ⟨(-m / n : ℚ), ?_⟩
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    push_cast
    field_simp
    linarith

lemma cv_inj {a b : Fin 4 → ℤ} (h : coordinateValue a = coordinateValue b) : a = b := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  rw [cv_re, cv_re] at hr
  rw [cv_im, cv_im] at hi
  obtain ⟨h0, h13⟩ := int_sqrt2 (2 * (a 0 - b 0)) ((a 1 - a 3) - (b 1 - b 3)) (by push_cast; linarith)
  obtain ⟨h2, h13'⟩ := int_sqrt2 (2 * (a 2 - b 2)) ((a 1 + a 3) - (b 1 + b 3)) (by push_cast; linarith)
  funext i
  fin_cases i <;> simp <;> omega

lemma mem_iff (z : ℂ) : z ∈ integralRing ↔ ∃ a, z = coordinateValue a := by
  constructor
  · intro hz
    induction hz using Subring.closure_induction with
    | mem x hx =>
      simp only [Set.mem_singleton_iff] at hx
      exact ⟨![0, 1, 0, 0], by simp [hx, coordinateValue]⟩
    | zero => exact ⟨0, by simp [coordinateValue]⟩
    | one => exact ⟨![1, 0, 0, 0], by simp [coordinateValue]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, cv_add a b⟩
    | neg x _ hx => obtain ⟨a, rfl⟩ := hx; exact ⟨-a, cv_neg a⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨cmul a b, cv_mul a b⟩
  · rintro ⟨a, rfl⟩
    have hω : ω ∈ integralRing := Subring.subset_closure (by simp)
    unfold coordinateValue
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
    · exact intCast_mem integralRing _
    · exact mul_mem (intCast_mem integralRing _) hω
    · exact mul_mem (intCast_mem integralRing _) (pow_mem hω _)
    · exact mul_mem (intCast_mem integralRing _) (pow_mem hω _)

lemma cv_mem (a : Fin 4 → ℤ) : coordinateValue a ∈ integralRing := (mem_iff _).mpr ⟨a, rfl⟩

/-- √2 · cv c -/
def smul2 (c : Fin 4 → ℤ) : Fin 4 → ℤ := ![c 1 - c 3, c 0 + c 2, c 1 + c 3, c 2 - c 0]

lemma sqrt2_mul (c : Fin 4 → ℤ) : ((s : ℝ) : ℂ) * coordinateValue c = coordinateValue (smul2 c) := by
  rw [sqrt2_eq]
  simp only [coordinateValue, smul2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  linear_combination (-(c 1 : ℂ) - (c 2 : ℂ) * ω - (c 3 : ℂ) * ω ^ 2 + (c 3 : ℂ)) * omega_four

lemma dvd_sqrt2_iff (b : Fin 4 → ℤ) :
    DividesIntegral ((s : ℝ) : ℂ) (coordinateValue b) ↔ Even (b 0 + b 2) ∧ Even (b 1 + b 3) := by
  constructor
  · rintro ⟨⟨q, hq⟩, h⟩
    obtain ⟨c, rfl⟩ := (mem_iff q).mp hq
    simp only at h
    rw [sqrt2_mul] at h
    have := cv_inj h
    have h0 := congrFun this 0; have h1 := congrFun this 1; have h2 := congrFun this 2
    have h3 := congrFun this 3
    simp [smul2] at h0 h1 h2 h3
    exact ⟨⟨c 1, by omega⟩, ⟨c 2, by omega⟩⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    -- c1 = u, c3 = u - b0, c2 = v, c0 = v - b3
    refine ⟨⟨coordinateValue ![v - b 3, u, v, u - b 0], cv_mem _⟩, ?_⟩
    simp only
    rw [sqrt2_mul]
    congr 1
    funext i
    fin_cases i <;> simp [smul2] <;> omega

lemma dvd_two_iff (b : Fin 4 → ℤ) :
    DividesIntegral 2 (coordinateValue b) ↔ ∀ i, Even (b i) := by
  constructor
  · rintro ⟨⟨q, hq⟩, h⟩
    obtain ⟨c, rfl⟩ := (mem_iff q).mp hq
    simp only at h
    have : coordinateValue b = coordinateValue (fun i => 2 * c i) := by
      rw [h]; simp only [coordinateValue, Int.cast_mul, Int.cast_ofNat]; ring
    have := cv_inj this
    intro i; rw [this]; exact ⟨c i, by ring⟩
  · intro h
    choose c hc using h
    refine ⟨⟨coordinateValue c, cv_mem _⟩, ?_⟩
    simp only [coordinateValue, hc]; push_cast; ring

lemma normSquared_cv (a : Fin 4 → ℤ) :
    normSquared (coordinateValue a) = coordinateValue ![formP a, formQ a, 0, -formQ a] := by
  have e : normSquared (coordinateValue a) = ((formP a : ℝ) + formQ a * s : ℝ) := by
    unfold normSquared
    congr 1
    rw [Complex.normSq_apply, cv_re, cv_im]
    simp only [formP, formQ]; push_cast
    nlinarith [s_mul]
  rw [e]
  have h2 := sqrt2_mul ![1, 0, 0, 0]
  apply Complex.ext
  · rw [cv_re]; simp; ring
  · rw [cv_im]; simp

lemma sqrtTwoInteger_val : ((sqrtTwoInteger : integralRing) : ℂ) = ((s : ℝ) : ℂ) := by
  rw [sqrt2_eq]; rfl

lemma dvd_sub_iff (z : ℂ) (hz : z ∈ integralRing) :
    sqrtTwoInteger ∣ (⟨z, hz⟩ : integralRing) ↔ DividesIntegral ((s : ℝ) : ℂ) z := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by have := congrArg Subtype.val hc; simpa [sqrtTwoInteger_val] using this⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext (by simp [hc, sqrtTwoInteger_val])⟩

lemma two_val : ((2 : integralRing) : ℂ) = 2 :=
  map_ofNat integralRing.subtype 2

lemma two_dvd_iff (z : ℂ) (hz : z ∈ integralRing) :
    (2 : integralRing) ∣ (⟨z, hz⟩ : integralRing) ↔ DividesIntegral 2 z := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by have := congrArg Subtype.val hc; simpa [two_val] using this⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext (by simp [hc, two_val])⟩

lemma gde_zero_iff (z : ℂ) (hz : z ∈ integralRing) :
    gde z = 0 ↔ ¬ DividesIntegral ((s : ℝ) : ℂ) z := by
  rw [gde, dif_pos hz, emultiplicity_eq_zero, dvd_sub_iff]

lemma gdeTwo_zero_iff (z : ℂ) (hz : z ∈ integralRing) :
    gdeTwo z = 0 ↔ ¬ DividesIntegral 2 z := by
  rw [gdeTwo, dif_pos hz, emultiplicity_eq_zero, two_dvd_iff]

end G68Z

namespace G68Z

lemma par1 (a : Fin 4 → ℤ) :
    Even (formP a) ∧ Even (formQ a) ↔ Even (a 0 + a 2) ∧ Even (a 1 + a 3) := by
  simp only [formP, formQ, parity_simps]
  tauto

lemma par2 (a : Fin 4 → ℤ) (h : ¬ (Even (a 0 + a 2) ∧ Even (a 1 + a 3))) :
    (Even (formP a) → Odd (formQ a)) ∧ (¬ Even (formP a) → Even (formQ a)) := by
  rw [← Int.not_even_iff_odd]
  simp only [formP, formQ, parity_simps, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true] at h ⊢
  tauto

lemma normSq_mem (z : ℂ) (hz : z ∈ integralRing) : normSquared z ∈ integralRing := by
  obtain ⟨a, rfl⟩ := (mem_iff z).mp hz
  rw [normSquared_cv]; exact cv_mem _

lemma dvd_sqrt2_norm (a : Fin 4 → ℤ) :
    DividesIntegral ((s : ℝ) : ℂ) (normSquared (coordinateValue a)) ↔ Even (formP a) := by
  rw [normSquared_cv, dvd_sqrt2_iff]
  simp

lemma dvd_two_norm (a : Fin 4 → ℤ) :
    DividesIntegral 2 (normSquared (coordinateValue a)) ↔ Even (formP a) ∧ Even (formQ a) := by
  rw [normSquared_cv, dvd_two_iff]
  constructor
  · intro h; exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨h1, h2⟩ i
    fin_cases i <;> simp [h1, h2]

end G68Z

namespace G68Z

lemma real_cv (m n : ℤ) : ((((m : ℝ) + n * s : ℝ)) : ℂ) = coordinateValue ![m, n, 0, -n] := by
  apply Complex.ext
  · rw [cv_re]; simp; ring
  · rw [cv_im]; simp

lemma bil (a b : Fin 4 → ℤ) :
    (((s : ℝ) : ℂ) * coordinateValue a * star (coordinateValue b)).re =
      ((a 0 * (b 1 - b 3) + b 0 * (a 1 - a 3) + a 2 * (b 1 + b 3) + b 2 * (a 1 + a 3) : ℤ) : ℝ) +
        ((a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3 : ℤ) : ℝ) * s := by
  have hs : (((s : ℝ) : ℂ) * coordinateValue a * star (coordinateValue b)).re =
      s * ((coordinateValue a).re * (coordinateValue b).re + (coordinateValue a).im * (coordinateValue b).im) := by
    simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
  rw [hs, cv_re, cv_re, cv_im, cv_im]
  push_cast
  have := s_mul
  linear_combination (((a 1 : ℝ) - a 3) * (b 1 - b 3) / 4 + ((a 1 : ℝ) + a 3) * (b 1 + b 3) / 4) * s * this +
    ((a 0 : ℝ) * (b 1 - b 3) + b 0 * (a 1 - a 3) + a 2 * (b 1 + b 3) + b 2 * (a 1 + a 3)) / 2 * this

end G68Z

open G68Z in
/-- Proposition 4, PDF p.21: both antecedents use sqrt(2)-divisibility of the
squared norm. The primitive hypothesis is shared by the two implications. -/
theorem solution (a : Fin 4 → ℤ)
    (hprimitive : gde (coordinateValue a) = 0) :
    (DividesIntegral ((Real.sqrt 2 : ℝ) : ℂ) (normSquared (coordinateValue a)) →
      Even (formP a) ∧ Odd (formQ a)) ∧
    (¬ DividesIntegral ((Real.sqrt 2 : ℝ) : ℂ) (normSquared (coordinateValue a)) →
      Odd (formP a) ∧ Even (formQ a)) := by
  rw [gde_zero_iff _ (cv_mem a), dvd_sqrt2_iff] at hprimitive
  obtain ⟨h1, h2⟩ := par2 a hprimitive
  rw [dvd_sqrt2_norm]
  refine ⟨fun h => ⟨h, h1 h⟩, fun h => ⟨Int.not_even_iff_odd.mp h, h2 h⟩⟩
