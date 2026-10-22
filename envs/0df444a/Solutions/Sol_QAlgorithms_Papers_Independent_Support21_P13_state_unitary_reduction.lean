-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P13.state_unitary_reduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T11:10:48.254928+00:00
-- url     : https://prove2.me/submissions/a89867cc-9d40-485c-87dc-5998fb012b07

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
theorem umc (z : ℂ) (hz : z ∈ synthesisRing) :
    ‖z‖ = 1 ↔ ∃ k : Fin 8, z = (QAlgorithms.gateT true true) ^ k.val := by
  constructor
  · intro hz1
    obtain ⟨k, hk⟩ := synth z hz
    have hn : Complex.normSq (z * ((s : ℝ) : ℂ) ^ k) = 2 ^ k := by
      rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq, hz1, map_pow, Complex.normSq_ofReal, s_mul]
      ring
    obtain ⟨j, hj⟩ := peel k _ hk hn
    refine ⟨j, ?_⟩
    have hsk : ((s : ℝ) : ℂ) ^ k ≠ 0 := pow_ne_zero _ s_ne
    apply mul_right_cancel₀ hsk
    rw [hj]; ring
  · rintro ⟨j, rfl⟩
    rw [norm_pow]
    have h1 : ‖ω‖ ^ 2 = 1 := by rw [Complex.sq_norm, normSq_omega]
    have h2 : ‖ω‖ = 1 := by
      have := norm_nonneg ω
      nlinarith
    show ‖ω‖ ^ j.val = 1
    rw [h2, one_pow]

end G68Z

namespace G68Z

lemma det2 (A : Matrix Bool Bool ℂ) :
    A.det = A false false * A true true - A false true * A true false := by
  rw [← Matrix.det_reindex_self finTwoEquiv.symm A, Matrix.det_fin_two]
  simp [finTwoEquiv]

lemma pc (V : Matrix Bool Bool ℂ) (hV : V ∈ Matrix.unitaryGroup Bool ℂ) :
    V false true = -star (V true false) * V.det ∧ V true true = star (V false false) * V.det := by
  have h1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have h2 := Matrix.mem_unitaryGroup_iff.mp hV
  have f1 := congrFun (congrFun h1 false) false
  have f2 := congrFun (congrFun h1 false) true
  have e1 := congrFun (congrFun h2 false) true
  have e2 := congrFun (congrFun h2 true) true
  simp only [Matrix.mul_apply, Matrix.star_apply, Fintype.sum_bool, Matrix.one_apply] at f1 f2 e1 e2
  simp only [if_true, if_false, Bool.true_eq_false, Bool.false_eq_true] at f1 f2 e1 e2
  rw [det2]
  constructor
  · linear_combination V true true * e1 - V false true * e2
  · linear_combination -(V true true) * f1 + V true false * f2

lemma word_cons (x : HTLetter) (c : List HTLetter) :
    htWordMatrix (x :: c) = htWordMatrix c * htMatrix x := by
  simp [htWordMatrix, List.prod_append]

lemma word_append (l1 l2 : List HTLetter) :
    htWordMatrix (l1 ++ l2) = htWordMatrix l2 * htWordMatrix l1 := by
  simp [htWordMatrix, List.reverse_append, List.prod_append]

lemma det_H : (QAlgorithms.hadamard).det = ω ^ 4 := by
  rw [det2, omega_four]
  simp [QAlgorithms.hadamard]
  rw [← mul_inv, ← sq, ← Complex.ofReal_pow, show Real.sqrt 2 ^ 2 = 2 from s_sq]
  push_cast; ring

lemma det_T : (QAlgorithms.gateT).det = ω := by
  simp [QAlgorithms.gateT, Matrix.det_diagonal, ω]

lemma det_word (c : List HTLetter) : ∃ m : ℕ, (htWordMatrix c).det = ω ^ m := by
  induction c with
  | nil => exact ⟨0, by simp [htWordMatrix]⟩
  | cons x c ih =>
    obtain ⟨m, hm⟩ := ih
    rw [word_cons, Matrix.det_mul, hm]
    cases x
    · exact ⟨m + 4, by rw [htMatrix, det_H, pow_add]⟩
    · exact ⟨m + 1, by rw [htMatrix, det_T, pow_succ]⟩

lemma omega_eight : ω ^ 8 = 1 := by
  rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, omega_four]; norm_num

lemma omega_mod (m : ℕ) : ω ^ m = ω ^ (m % 8) := by
  conv_lhs => rw [← Nat.div_add_mod m 8, pow_add, pow_mul, omega_eight, one_pow, one_mul]

lemma H_unitary : QAlgorithms.hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hs : star QAlgorithms.hadamard = QAlgorithms.hadamard := by
    ext i j
    cases i <;> cases j <;> simp [QAlgorithms.hadamard, Matrix.star_apply, Complex.conj_ofReal]
  rw [hs]; exact QAlgorithms.hadamard_mul_self

lemma T_unitary : QAlgorithms.gateT ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  have hω : ω * star ω = 1 := by
    rw [Complex.star_def, Complex.mul_conj, normSq_omega]; simp
  cases i <;> cases j <;> simp [QAlgorithms.gateT, Matrix.mul_apply, Matrix.star_apply, Fintype.sum_bool,
    Matrix.diagonal_apply] <;> simpa [ω, QAlgorithms.gateT, Matrix.diagonal_apply] using hω

lemma word_unitary (c : List HTLetter) : htWordMatrix c ∈ Matrix.unitaryGroup Bool ℂ := by
  induction c with
  | nil => simp [htWordMatrix]
  | cons x c ih =>
    rw [word_cons]
    refine mul_mem ih ?_
    cases x
    · exact H_unitary
    · exact T_unitary

lemma word_T (r : ℕ) : htWordMatrix (List.replicate r HTLetter.t) = QAlgorithms.gateT ^ r := by
  induction r with
  | zero => simp [htWordMatrix]
  | succ r ih =>
    rw [List.replicate_succ, word_cons, ih, htMatrix, pow_succ]

lemma T_pow_col (r : ℕ) (b : Bool) : (QAlgorithms.gateT ^ r) b false = if b then 0 else 1 := by
  simp only [QAlgorithms.gateT, Matrix.diagonal_pow, Matrix.diagonal_apply]
  cases b <;> simp

lemma det_ring (U : Matrix Bool Bool ℂ) (h : EntriesInRing U) : U.det ∈ synthesisRing := by
  rw [det2]
  exact sub_mem (mul_mem (h _ _) (h _ _)) (mul_mem (h _ _) (h _ _))

lemma det_norm (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ) : ‖U.det‖ = 1 :=
  CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hU)

end G68Z

open G68Z in
/-- Section 3, PDF pp.4-5: lift any exact first-column preparation to U by right
multiplication with T^r, 0<=r<8. The chronological correction is prepended.
Conversely, a circuit for U prepares its first column without extra gates. -/
theorem solution (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) (hring : EntriesInRing U)
    (c : List HTLetter) (hcol : ∀ b, htWordMatrix c b false = U b false) :
    ∃ k kp : Fin 8,
      U = phaseCompletion (U false false) (U true false) (k.val : ℤ) ∧
      (htWordMatrix c).det = (QAlgorithms.gateT true true) ^ kp.val ∧
      let r := (k.val + 8 - kp.val) % 8
      htWordMatrix (List.replicate r HTLetter.t ++ c) = U ∧
      (List.replicate r HTLetter.t ++ c).length ≤ c.length + 7 := by
  obtain ⟨k, hk⟩ := (umc U.det (det_ring U hring)).mp (det_norm U hU)
  obtain ⟨m, hm⟩ := det_word c
  have hpcU := pc U hU
  refine ⟨k, ⟨m % 8, Nat.mod_lt _ (by norm_num)⟩, ?_, ?_, ?_⟩
  · ext a b
    cases a <;> cases b <;> simp only [phaseCompletion, zpow_natCast, if_true, if_false,
      Bool.false_eq_true]
    · rw [hpcU.1, hk]
    · rw [hpcU.2, hk]
  · show (htWordMatrix c).det = ω ^ (m % 8)
    rw [hm, omega_mod]
  · intro r
    refine ⟨?_, by simp; omega⟩
    rw [word_append, word_T]
    set V := htWordMatrix c * QAlgorithms.gateT ^ r
    have hV : V ∈ Matrix.unitaryGroup Bool ℂ := mul_mem (word_unitary c) (pow_mem T_unitary r)
    have hpcV := pc V hV
    have hcolV : ∀ b, V b false = U b false := by
      intro b
      simp only [V, Matrix.mul_apply, Fintype.sum_bool, T_pow_col]
      simp [hcol b]
    have hdet : V.det = U.det := by
      simp only [V]
      rw [Matrix.det_mul, Matrix.det_pow, det_T, hm, hk, ← pow_add, omega_mod, omega_mod k.val]
      congr 1
      simp only [r]
      omega
    ext a b
    cases a <;> cases b
    · exact hcolV false
    · rw [hpcV.1, hpcU.1, hcolV true, hdet]
    · exact hcolV true
    · rw [hpcV.2, hpcU.2, hcolV false, hdet]
