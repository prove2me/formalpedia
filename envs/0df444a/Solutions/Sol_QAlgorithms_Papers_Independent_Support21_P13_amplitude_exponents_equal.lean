-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P13.amplitude_exponents_equal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T10:46:03.49746+00:00
-- url     : https://prove2.me/submissions/33bd6c00-6eb2-4cb0-b73e-af50d7dba52b

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

namespace G68Z

lemma dec2 : ∀ n : ℕ, ∀ a : ℤ, a.natAbs = n → a ≠ 0 → ∃ i : ℕ, ∃ a1 : ℤ, a = 2 ^ i * a1 ∧ Odd a1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a hn ha
    rcases Int.even_or_odd a with ⟨c, hc⟩ | ho
    · have hc0 : c ≠ 0 := by rintro rfl; simp at hc; exact ha hc
      obtain ⟨i, c1, h1, h2⟩ := ih c.natAbs (by omega) c rfl hc0
      exact ⟨i + 1, c1, by rw [hc, h1]; ring, h2⟩
    · exact ⟨0, a, by simp, ho⟩

lemma v2_eq (i : ℕ) (a1 : ℤ) (h : Odd a1) : emultiplicity (2 : ℤ) (2 ^ i * a1) = i := by
  rw [emultiplicity_eq_coe]
  refine ⟨dvd_mul_right _ _, fun ⟨c, hc⟩ => ?_⟩
  have : a1 = 2 * c := by
    have h2 : (2 : ℤ) ^ i ≠ 0 := pow_ne_zero _ (by norm_num)
    apply mul_left_cancel₀ h2
    rw [hc]; ring
  exact (Int.not_even_iff_odd.mpr h) ⟨c, by omega⟩

lemma sq2c : ((s : ℝ) : ℂ) ^ 2 = 2 := by
  have := s_sq; exact_mod_cast this

lemma zc_mem (u w : ℤ) : (u : ℂ) + ((s : ℝ) : ℂ) * w ∈ integralRing := by
  have := real_cv u w
  push_cast at this
  rw [mul_comm, this]; exact cv_mem _

lemma gde_form (d : ℕ) (u w : ℤ) (hu : Odd u) :
    gde (((s : ℝ) : ℂ) ^ d * ((u : ℂ) + ((s : ℝ) : ℂ) * w)) = d := by
  have hY := zc_mem u w
  have hr : ((s : ℝ) : ℂ) ∈ integralRing := by rw [← sqrtTwoInteger_val]; exact sqrtTwoInteger.2
  have hz : ((s : ℝ) : ℂ) ^ d * ((u : ℂ) + ((s : ℝ) : ℂ) * w) ∈ integralRing :=
    mul_mem (pow_mem hr _) hY
  rw [gde, dif_pos hz]
  have he : (⟨_, hz⟩ : integralRing) = sqrtTwoInteger ^ d * ⟨_, hY⟩ := by
    apply Subtype.ext
    simp [sqrtTwoInteger_val]
  rw [he, emultiplicity_eq_coe]
  refine ⟨dvd_mul_right _ _, fun ⟨c, hc⟩ => ?_⟩
  have hr0 : sqrtTwoInteger ≠ 0 := by
    intro h0
    have := congrArg Subtype.val h0
    rw [sqrtTwoInteger_val] at this
    simp [s] at this
  have hdiv : sqrtTwoInteger ∣ (⟨_, hY⟩ : integralRing) := by
    refine ⟨c, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero d hr0)
    rw [hc]; ring
  rw [dvd_sub_iff] at hdiv
  have := real_cv u w
  push_cast at this
  rw [mul_comm (((s : ℝ) : ℂ)), this, dvd_sqrt2_iff] at hdiv
  simp at hdiv
  exact (Int.not_even_iff_odd.mpr hu) hdiv

end G68Z


namespace G68Z

lemma om5 : ω ^ 5 = -ω := by rw [pow_succ, omega_four]; ring
lemma om6 : ω ^ 6 = -ω ^ 2 := by rw [show (6:ℕ) = 4 + 2 from rfl, pow_add, omega_four]; ring
lemma om7 : ω ^ 7 = -ω ^ 3 := by rw [show (7:ℕ) = 4 + 3 from rfl, pow_add, omega_four]; ring

lemma normSq_omega : Complex.normSq ω = 1 := by
  rw [Complex.normSq_apply, omega_re, omega_im]; nlinarith [s_mul]

lemma base_case (a : Fin 4 → ℤ) (h : Complex.normSq (coordinateValue a) = 1) :
    ∃ j : Fin 8, coordinateValue a = ω ^ j.val := by
  have hn := congrArg Complex.re (normSquared_cv a)
  simp only [normSquared, Complex.ofReal_re, h] at hn
  rw [cv_re] at hn
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons] at hn
  obtain ⟨hP, hQ⟩ := int_sqrt2 (formP a - 1) (formQ a) (by push_cast at hn ⊢; linear_combination -hn)
  simp only [formP] at hP
  simp only [coordinateValue]
  generalize a 0 = a0 at *; generalize a 1 = a1 at *; generalize a 2 = a2 at *; generalize a 3 = a3 at *
  have b0 : -1 ≤ a0 ∧ a0 ≤ 1 := by constructor <;> nlinarith [sq_nonneg a1, sq_nonneg a2, sq_nonneg a3]
  have b1 : -1 ≤ a1 ∧ a1 ≤ 1 := by constructor <;> nlinarith [sq_nonneg a0, sq_nonneg a2, sq_nonneg a3]
  have b2 : -1 ≤ a2 ∧ a2 ≤ 1 := by constructor <;> nlinarith [sq_nonneg a1, sq_nonneg a0, sq_nonneg a3]
  have b3 : -1 ≤ a3 ∧ a3 ≤ 1 := by constructor <;> nlinarith [sq_nonneg a1, sq_nonneg a2, sq_nonneg a0]
  obtain ⟨l0, u0⟩ := b0; obtain ⟨l1, u1⟩ := b1; obtain ⟨l2, u2⟩ := b2; obtain ⟨l3, u3⟩ := b3
  interval_cases a0 <;> interval_cases a1 <;> interval_cases a2 <;> interval_cases a3 <;>
    norm_num at hP <;>
    first
    | (refine ⟨0, ?_⟩; simp; done) | (refine ⟨1, ?_⟩; simp; done) | (refine ⟨2, ?_⟩; simp; done)
    | (refine ⟨3, ?_⟩; simp; done) | (refine ⟨4, ?_⟩; simp [omega_four]; done)
    | (refine ⟨5, ?_⟩; simp [om5]; done) | (refine ⟨6, ?_⟩; simp [om6]; done)
    | (refine ⟨7, ?_⟩; simp [om7]; done)

lemma s_ne : ((s : ℝ) : ℂ) ≠ 0 := by
  have : (0 : ℝ) < s := Real.sqrt_pos.mpr (by norm_num)
  exact_mod_cast this.ne'

lemma s_mem : ((s : ℝ) : ℂ) ∈ integralRing := by rw [← sqrtTwoInteger_val]; exact sqrtTwoInteger.2

lemma peel : ∀ k : ℕ, ∀ x ∈ integralRing, Complex.normSq x = 2 ^ k →
    ∃ j : Fin 8, x = ((s : ℝ) : ℂ) ^ k * ω ^ j.val := by
  intro k
  induction k with
  | zero =>
    intro x hx h
    obtain ⟨a, rfl⟩ := (mem_iff x).mp hx
    obtain ⟨j, hj⟩ := base_case a (by simpa using h)
    exact ⟨j, by simp [hj]⟩
  | succ k ih =>
    intro x hx h
    obtain ⟨a, rfl⟩ := (mem_iff x).mp hx
    have hn := congrArg Complex.re (normSquared_cv a)
    simp only [normSquared, Complex.ofReal_re, h] at hn
    rw [cv_re] at hn
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] at hn
    obtain ⟨hP, hQ⟩ := int_sqrt2 (formP a - 2 ^ (k + 1)) (formQ a)
      (by push_cast at hn ⊢; linear_combination -hn)
    have hev : Even (formP a) ∧ Even (formQ a) :=
      ⟨⟨2 ^ k, by rw [show formP a = 2 ^ (k + 1) by omega, pow_succ]; ring⟩, by rw [hQ]; exact ⟨0, rfl⟩⟩
    rw [par1, ← dvd_sqrt2_iff] at hev
    obtain ⟨⟨q, hq⟩, hxq⟩ := hev
    simp only at hxq
    have hnq : Complex.normSq q = 2 ^ k := by
      have h2 := h
      rw [hxq, Complex.normSq_mul, Complex.normSq_ofReal, s_mul, pow_succ] at h2
      linarith
    obtain ⟨j, hj⟩ := ih q hq hnq
    exact ⟨j, by rw [hxq, hj]; ring⟩

lemma synth (z : ℂ) (hz : z ∈ synthesisRing) : ∃ k : ℕ, z * ((s : ℝ) : ℂ) ^ k ∈ integralRing := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨1, by rw [pow_one, inv_mul_cancel₀ s_ne]; exact one_mem _⟩
    · simp only [Set.mem_singleton_iff] at hx; subst hx
      exact ⟨0, by rw [pow_zero, mul_one, ← omega_sq]; exact pow_mem (Subring.subset_closure (by simp)) _⟩
  | zero => exact ⟨0, by simp [zero_mem]⟩
  | one => exact ⟨0, by simp [one_mem]⟩
  | add x y _ _ hx hy =>
    obtain ⟨k1, h1⟩ := hx; obtain ⟨k2, h2⟩ := hy
    refine ⟨k1 + k2, ?_⟩
    have : (x + y) * ((s : ℝ) : ℂ) ^ (k1 + k2) =
        x * ((s : ℝ) : ℂ) ^ k1 * ((s : ℝ) : ℂ) ^ k2 + y * ((s : ℝ) : ℂ) ^ k2 * ((s : ℝ) : ℂ) ^ k1 := by ring
    rw [this]
    exact add_mem (mul_mem h1 (pow_mem s_mem _)) (mul_mem h2 (pow_mem s_mem _))
  | neg x _ hx =>
    obtain ⟨k, h⟩ := hx
    exact ⟨k, by rw [neg_mul]; exact neg_mem h⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k1, h1⟩ := hx; obtain ⟨k2, h2⟩ := hy
    refine ⟨k1 + k2, ?_⟩
    have : x * y * ((s : ℝ) : ℂ) ^ (k1 + k2) = (x * ((s : ℝ) : ℂ) ^ k1) * (y * ((s : ℝ) : ℂ) ^ k2) := by ring
    rw [this]; exact mul_mem h1 h2

end G68Z


namespace G68Z

lemma nd1 (x : ℂ) (hx : x ∈ integralRing) :
    DividesIntegral ((s : ℝ) : ℂ) x ↔ DividesIntegral 2 (normSquared x) := by
  obtain ⟨a, rfl⟩ := (mem_iff x).mp hx
  rw [dvd_sqrt2_iff, dvd_two_norm, par1]

lemma nd2 (x : ℂ) (hx : x ∈ integralRing) (h : ¬ DividesIntegral ((s : ℝ) : ℂ) x) :
    gde (normSquared x) ≤ 1 := by
  have hmem := normSq_mem _ hx
  rw [nd1 x hx] at h
  rw [gde, dif_pos hmem]
  have hlt : emultiplicity sqrtTwoInteger (⟨normSquared x, hmem⟩ : integralRing) < (2 : ℕ) := by
    rw [emultiplicity_lt_iff_not_dvd]
    have hsq : sqrtTwoInteger ^ 2 = (2 : integralRing) := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, sqrtTwoInteger_val, two_val]
      push_cast; exact_mod_cast s_sq
    rw [hsq, two_dvd_iff]
    exact h
  exact Order.le_of_lt_add_one hlt

lemma normSq_s_pow (z : ℂ) (n : ℕ) : Complex.normSq (z * ((s : ℝ) : ℂ) ^ n) = Complex.normSq z * 2 ^ n := by
  rw [Complex.normSq_mul, map_pow, Complex.normSq_ofReal, s_mul]

lemma div_cancel (z : ℂ) (n : ℕ) (h : DividesIntegral ((s : ℝ) : ℂ) (z * ((s : ℝ) : ℂ) ^ (n + 1))) :
    z * ((s : ℝ) : ℂ) ^ n ∈ integralRing := by
  obtain ⟨⟨q, hq⟩, h⟩ := h
  have : z * ((s : ℝ) : ℂ) ^ n = q := by
    apply mul_left_cancel₀ s_ne
    rw [← h]; ring
  rw [this]; exact hq

/-- 2 | 2c - |y|² stuff: if normSquared x = 2 * (c - normSquared y) with c ∈ ring then 2 ∣ normSquared x. -/
lemma two_dvd_of (u v : ℂ) (hv : v ∈ integralRing) (h : u = 2 * v) : DividesIntegral 2 u :=
  ⟨⟨v, hv⟩, h⟩

lemma descend (z w : ℂ) (n : ℕ) (hstate : Complex.normSq z + Complex.normSq w = 1)
    (hx : z * ((s : ℝ) : ℂ) ^ (n + 1) ∈ integralRing) :
    ∀ m : ℕ, w * ((s : ℝ) : ℂ) ^ (n + 1 + m) ∈ integralRing → w * ((s : ℝ) : ℂ) ^ (n + 1) ∈ integralRing := by
  intro m
  induction m with
  | zero => simpa using id
  | succ m ih =>
    intro hy
    apply ih
    have hmem := normSq_mem _ hx
    have hdiv : DividesIntegral 2 (normSquared (w * ((s : ℝ) : ℂ) ^ (n + 1 + (m + 1)))) := by
      refine two_dvd_of _ ((2 : ℂ) ^ (n + 1 + m) - normSquared (z * ((s : ℝ) : ℂ) ^ (n + 1)) * 2 ^ m)
        (sub_mem (pow_mem (by exact_mod_cast intCast_mem integralRing 2) _)
          (mul_mem hmem (pow_mem (by exact_mod_cast intCast_mem integralRing 2) _))) ?_
      simp only [normSquared, normSq_s_pow]
      have hw : Complex.normSq w = 1 - Complex.normSq z := by linarith
      rw [hw]; push_cast; ring
    rw [← nd1 _ hy] at hdiv
    have := div_cancel w (n + 1 + m) (by simpa [add_assoc] using hdiv)
    exact this

end G68Z

namespace G68Z

lemma core (z w : ℂ) (hw : w ∈ synthesisRing)
    (hstate : Complex.normSq z + Complex.normSq w = 1) (d : ℤ) (hd : IsSDE z d) (h1 : 1 ≤ d) :
    IsSDE w d ∧ z * ((s : ℝ) : ℂ) ^ d ∈ integralRing ∧ w * ((s : ℝ) : ℂ) ^ d ∈ integralRing ∧
      gde (normSquared (z * ((s : ℝ) : ℂ) ^ d)) = gde (normSquared (w * ((s : ℝ) : ℂ) ^ d)) ∧
      gde (normSquared (z * ((s : ℝ) : ℂ) ^ d)) ≤ 1 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = n + 1 := ⟨(d - 1).toNat, by omega⟩
  have e1 : ((s : ℝ) : ℂ) ^ ((n : ℤ) + 1) = ((s : ℝ) : ℂ) ^ (n + 1) := by
    rw [← zpow_natCast]; push_cast; rfl
  obtain ⟨hx, hmin⟩ := hd
  rw [e1] at hx ⊢
  -- x primitive
  have hxp : ¬ DividesIntegral ((s : ℝ) : ℂ) (z * ((s : ℝ) : ℂ) ^ (n + 1)) := by
    intro h
    have := hmin n (by rw [zpow_natCast]; exact div_cancel z n h)
    omega
  -- w s^(n+1) ∈ ring
  obtain ⟨k, hk⟩ := synth w hw
  have hy : w * ((s : ℝ) : ℂ) ^ (n + 1) ∈ integralRing := by
    rcases le_or_gt k (n + 1) with hkn | hkn
    · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hkn
      rw [hm, pow_add, ← mul_assoc]; exact mul_mem hk (pow_mem s_mem _)
    · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hkn
      exact descend z w n hstate hx (m + 1) (by rw [show n + 1 + (m + 1) = k by omega]; exact hk)
  -- y primitive
  have hyp : ¬ DividesIntegral ((s : ℝ) : ℂ) (w * ((s : ℝ) : ℂ) ^ (n + 1)) := by
    intro h
    have hy' := div_cancel w n h
    apply hxp
    rw [nd1 _ hx]
    refine two_dvd_of _ ((2 : ℂ) ^ n - normSquared (w * ((s : ℝ) : ℂ) ^ n))
      (sub_mem (pow_mem (by exact_mod_cast intCast_mem integralRing 2) _) (normSq_mem _ hy')) ?_
    simp only [normSquared, normSq_s_pow]
    have hzz : Complex.normSq z = 1 - Complex.normSq w := by linarith
    rw [hzz]; push_cast; ring
  refine ⟨⟨by rw [e1]; exact hy, fun e he => ?_⟩, hx, hy, ?_, nd2 _ hx hxp⟩
  · -- minimality for w
    by_contra hlt
    push Not at hlt
    apply hyp
    have : w * ((s : ℝ) : ℂ) ^ n ∈ integralRing := by
      have hle : e ≤ n := by omega
      have : w * ((s : ℝ) : ℂ) ^ n = (w * ((s : ℝ) : ℂ) ^ e) * ((s : ℝ) : ℂ) ^ ((n : ℤ) - e) := by
        rw [mul_assoc, ← zpow_add₀ s_ne, ← zpow_natCast]; congr 2; ring
      rw [this]
      refine mul_mem he ?_
      obtain ⟨t, ht⟩ : ∃ t : ℕ, (n : ℤ) - e = t := ⟨((n : ℤ) - e).toNat, by omega⟩
      rw [ht, zpow_natCast]; exact pow_mem s_mem _
    exact ⟨⟨_, this⟩, by simp only; ring⟩
  · -- equal gde values
    have bx := nd2 _ hx hxp
    have byy := nd2 _ hy hyp
    have hsum : normSquared (z * ((s : ℝ) : ℂ) ^ (n + 1)) + normSquared (w * ((s : ℝ) : ℂ) ^ (n + 1)) =
        ((s : ℝ) : ℂ) * (((s : ℝ) : ℂ) * (2 : ℂ) ^ n) := by
      simp only [normSquared, normSq_s_pow]; push_cast
      rw [← mul_assoc, ← sq, sq2c]
      linear_combination (2 : ℂ) ^ (n + 1) * (by exact_mod_cast hstate : (Complex.normSq z : ℂ) + Complex.normSq w = 1)
    have hmx := normSq_mem _ hx
    have hmy := normSq_mem _ hy
    have h2n : ((s : ℝ) : ℂ) * (2 : ℂ) ^ n ∈ integralRing :=
      mul_mem s_mem (pow_mem (by exact_mod_cast intCast_mem integralRing 2) _)
    have key : DividesIntegral ((s : ℝ) : ℂ) (normSquared (z * ((s : ℝ) : ℂ) ^ (n + 1))) ↔
        DividesIntegral ((s : ℝ) : ℂ) (normSquared (w * ((s : ℝ) : ℂ) ^ (n + 1))) := by
      constructor
      · rintro ⟨⟨q, hq⟩, hq'⟩
        refine ⟨⟨((s : ℝ) : ℂ) * (2 : ℂ) ^ n - q, sub_mem h2n hq⟩, ?_⟩
        simp only at hq' ⊢
        linear_combination hsum - hq'
      · rintro ⟨⟨q, hq⟩, hq'⟩
        refine ⟨⟨((s : ℝ) : ℂ) * (2 : ℂ) ^ n - q, sub_mem h2n hq⟩, ?_⟩
        simp only at hq' ⊢
        linear_combination hsum - hq'
    have zx := gde_zero_iff _ hmx
    have zy := gde_zero_iff _ hmy
    have c1 : ∀ v : ℕ∞, v ≤ 1 → v = 0 ∨ v = 1 := by
      intro v hv
      rcases eq_or_ne v 0 with h | h
      · exact Or.inl h
      · right; exact le_antisymm hv (Order.one_le_iff_ne_zero.mpr h)
    rcases c1 _ bx with h | h <;> rcases c1 _ byy with h' | h'
    · rw [h, h']
    · exfalso; rw [h'] at zy; rw [h] at zx
      have := zx.mp rfl; rw [key] at this
      exact absurd (zy.mpr this) (by simp)
    · exfalso; rw [h'] at zy; rw [h] at zx
      have := zy.mp rfl; rw [← key] at this
      exact absurd (zx.mpr this) (by simp)
    · rw [h, h']

end G68Z

open G68Z in
/-- Lemma 4, PDF p.9: the exponents here belong to amplitudes, not squared
moduli. The primitive numerators are constructed from the common exponent. -/
theorem solution (z w : ℂ)
    (hz : z ∈ synthesisRing) (hw : w ∈ synthesisRing)
    (hstate : Complex.normSq z + Complex.normSq w = 1)
    (hpositive : (∃ d : ℤ, IsSDE z d ∧ 1 ≤ d) ∨
      (∃ d : ℤ, IsSDE w d ∧ 1 ≤ d)) :
    ∃ d : ℤ, IsSDE z d ∧ IsSDE w d ∧
      let x := z * ((Real.sqrt 2 : ℝ) : ℂ) ^ d
      let y := w * ((Real.sqrt 2 : ℝ) : ℂ) ^ d
      x ∈ integralRing ∧ y ∈ integralRing ∧
      gde (normSquared x) = gde (normSquared y) ∧ gde (normSquared x) ≤ 1 := by
  rcases hpositive with ⟨d, hd, h1⟩ | ⟨d, hd, h1⟩
  · obtain ⟨hw', hx, hy, heq, hle⟩ := core z w hw hstate d hd h1
    exact ⟨d, hd, hw', hx, hy, heq, hle⟩
  · obtain ⟨hz', hy, hx, heq, hle⟩ := core w z hz (by linarith) d hd h1
    exact ⟨d, hz', hd, hx, hy, heq.symm, heq ▸ hle⟩
