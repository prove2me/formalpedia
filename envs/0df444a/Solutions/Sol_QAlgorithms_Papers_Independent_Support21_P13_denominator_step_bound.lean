-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P13.denominator_step_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T11:04:54.925359+00:00
-- url     : https://prove2.me/submissions/0c14dfce-11d2-4992-b226-a8f29775f102

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


namespace G68Z

lemma cv_smul (t : ℤ) (c : Fin 4 → ℤ) : (t : ℂ) * coordinateValue c = coordinateValue (fun i => t * c i) := by
  simp only [coordinateValue]; push_cast; ring

lemma s_pow_two_mul (N : ℕ) : ((s : ℝ) : ℂ) ^ (2 * N) = (2 : ℂ) ^ N := by rw [pow_mul, sq2c]

/-- finite √2-adic decomposition of a nonzero element. -/
lemma fin_dec (x : ℂ) (hx : x ∈ integralRing) (h0 : x ≠ 0) :
    ∃ p : ℕ, ∃ x' : ℂ, x' ∈ integralRing ∧ x = ((s : ℝ) : ℂ) ^ p * x' ∧ ¬ DividesIntegral ((s : ℝ) : ℂ) x' := by
  let P : ℕ → Prop := fun p => ∃ x' : ℂ, x' ∈ integralRing ∧ x = ((s : ℝ) : ℂ) ^ p * x'
  have hex : ∃ p, ¬ P p := by
    by_contra hall
    push Not at hall
    obtain ⟨a, rfl⟩ := (mem_iff x).mp hx
    set N := ∑ i, (a i).natAbs + 1
    obtain ⟨x'', hx'', he⟩ := hall (2 * N)
    obtain ⟨c, rfl⟩ := (mem_iff x'').mp hx''
    rw [s_pow_two_mul, show (2 : ℂ) ^ N = ((2 ^ N : ℤ) : ℂ) by push_cast; rfl, cv_smul] at he
    have hac := cv_inj he
    apply h0
    have : a = 0 := by
      funext i
      have hi : a i = 2 ^ N * c i := congrFun hac i
      by_contra hne
      have hci : c i ≠ 0 := by rintro h; rw [h, mul_zero] at hi; exact hne hi
      have h1 : (2 : ℤ) ^ N ≤ |a i| := by
        rw [hi, abs_mul, abs_of_pos (by positivity)]
        exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hci)
      have h2 : ((a i).natAbs : ℤ) < N := by
        have : (a i).natAbs ≤ ∑ j, (a j).natAbs :=
          Finset.single_le_sum (f := fun j => (a j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      have h3 : (N : ℤ) < 2 ^ N := by exact_mod_cast Nat.lt_two_pow_self
      rw [Int.abs_eq_natAbs] at h1
      omega
    rw [this]; simp [coordinateValue]
  classical
  let p0 := Nat.find hex
  have hp0 : ¬ P p0 := Nat.find_spec hex
  have hpos : p0 ≠ 0 := by
    intro h; apply hp0; rw [h]; exact ⟨x, hx, by simp⟩
  obtain ⟨p, hp⟩ : ∃ p, p0 = p + 1 := Nat.exists_eq_succ_of_ne_zero hpos
  have hPp : P p := by
    by_contra hn
    have := Nat.find_min' hex hn
    omega
  obtain ⟨x', hx', he⟩ := hPp
  refine ⟨p, x', hx', he, fun ⟨⟨q, hq⟩, hq'⟩ => hp0 ?_⟩
  rw [hp]
  exact ⟨q, hq, by rw [he, hq', pow_succ]; ring⟩

lemma emult_pow_mul (n e : ℕ) (B : integralRing) (h : emultiplicity sqrtTwoInteger B = e) :
    emultiplicity sqrtTwoInteger (sqrtTwoInteger ^ n * B) = ((n + e : ℕ) : ℕ∞) := by
  rw [emultiplicity_eq_coe] at h ⊢
  obtain ⟨⟨c, hc⟩, hnd⟩ := h
  have hr0 : sqrtTwoInteger ≠ 0 := by
    intro h0
    have := congrArg Subtype.val h0
    rw [sqrtTwoInteger_val] at this
    exact s_ne this
  refine ⟨⟨c, by rw [hc, pow_add]; ring⟩, fun ⟨d, hd⟩ => hnd ⟨d, ?_⟩⟩
  apply mul_left_cancel₀ (pow_ne_zero n hr0)
  rw [hd]; ring

lemma gde_ge (z : ℂ) (hz : z ∈ integralRing) (k : ℕ) (q : ℂ) (hq : q ∈ integralRing)
    (h : z = ((s : ℝ) : ℂ) ^ k * q) : (k : ℕ∞) ≤ gde z := by
  rw [gde, dif_pos hz]
  apply le_emultiplicity_of_pow_dvd
  exact ⟨⟨q, hq⟩, Subtype.ext (by simp [sqrtTwoInteger_val, h])⟩

lemma gde_spow (n : ℕ) (u : ℂ) (hu : u ∈ integralRing) (e : ℕ) (he : gde u = e) :
    gde (((s : ℝ) : ℂ) ^ n * u) = ((n + e : ℕ) : ℕ∞) := by
  have hz : ((s : ℝ) : ℂ) ^ n * u ∈ integralRing := mul_mem (pow_mem s_mem _) hu
  rw [gde, dif_pos hu] at he
  rw [gde, dif_pos hz]
  have : (⟨_, hz⟩ : integralRing) = sqrtTwoInteger ^ n * ⟨u, hu⟩ :=
    Subtype.ext (by simp [sqrtTwoInteger_val])
  rw [this]
  exact emult_pow_mul n e _ he

lemma eps_cases (v : ℕ∞) (h : v ≤ 1) : v = 0 ∨ v = 1 := by
  rcases eq_or_ne v 0 with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (le_antisymm h (Order.one_le_iff_ne_zero.mpr h0))

/-- R(x,y) = Re(√2 x ȳ) -/
def Rr (x y : ℂ) : ℂ := ((((s : ℝ) : ℂ) * x * star y).re : ℂ)

lemma Rr_mem (x y : ℂ) (hx : x ∈ integralRing) (hy : y ∈ integralRing) : Rr x y ∈ integralRing := by
  obtain ⟨a, rfl⟩ := (mem_iff x).mp hx
  obtain ⟨b, rfl⟩ := (mem_iff y).mp hy
  unfold Rr
  rw [bil, real_cv]; exact cv_mem _

lemma normSq_add_R (x y : ℂ) : normSquared (x + y) = normSquared x + normSquared y + ((s : ℝ) : ℂ) * Rr x y := by
  unfold normSquared Rr
  rw [Complex.normSq_add]
  have : (((s : ℝ) : ℂ) * x * star y).re = s * (x * (starRingEnd ℂ) y).re := by
    rw [mul_assoc, Complex.re_ofReal_mul]; rfl
  rw [this]; push_cast
  rw [← mul_assoc, ← sq, sq2c]

lemma Rr_scale (p q : ℕ) (x y : ℂ) :
    Rr (((s : ℝ) : ℂ) ^ p * x) (((s : ℝ) : ℂ) ^ q * y) = ((s : ℝ) : ℂ) ^ (p + q) * Rr x y := by
  unfold Rr
  have : ((s : ℝ) : ℂ) * (((s : ℝ) : ℂ) ^ p * x) * star (((s : ℝ) : ℂ) ^ q * y) =
      (((s ^ (p + q) : ℝ)) : ℂ) * (((s : ℝ) : ℂ) * x * star y) := by
    simp only [star_mul', Complex.star_def, map_pow, Complex.conj_ofReal]; push_cast; ring
  rw [this, Complex.re_ofReal_mul]; push_cast; ring

lemma halfV (n : ℕ) : halfValuation (n : ℕ∞) = ((n / 2 : ℕ) : ℕ∞) := by
  unfold halfValuation
  rw [if_neg (ENat.coe_ne_top n), ENat.toNat_coe]

end G68Z


namespace G68Z
theorem nsvb (x y : integralRing) (m : ℕ)
    (hsum : Complex.normSq (x : ℂ) + Complex.normSq (y : ℂ) = Real.sqrt 2 ^ m) :
    min (m : ℕ∞) (1 + halfValuation (gde (normSquared (x : ℂ)) +
      gde (normSquared (y : ℂ)))) ≤ gde (normSquared ((x : ℂ) + (y : ℂ))) := by
  have hxr := x.2
  have hyr := y.2
  have hsm : ((Real.sqrt 2 ^ m : ℝ) : ℂ) = ((s : ℝ) : ℂ) ^ m := by push_cast; rfl
  have hsum' : normSquared (x : ℂ) + normSquared (y : ℂ) = ((s : ℝ) : ℂ) ^ m := by
    unfold normSquared; rw [← hsm, ← hsum]; push_cast; ring
  have hsmem : ((s : ℝ) : ℂ) ^ m ∈ integralRing := pow_mem s_mem _
  have hxy : (x : ℂ) + (y : ℂ) ∈ integralRing := add_mem hxr hyr
  have hN := normSq_mem _ hxy
  -- zero cases
  by_cases hx0 : (x : ℂ) = 0
  · have : gde (normSquared (x : ℂ)) = ⊤ := by
      have h0 : normSquared (0 : ℂ) = 0 := by simp [normSquared]
      rw [hx0, h0, gde, dif_pos (zero_mem _)]; exact emultiplicity_zero _
    rw [this, top_add, halfValuation, if_pos rfl, add_top, min_eq_left le_top]
    refine gde_ge _ hN m 1 (one_mem _) ?_
    rw [hx0, zero_add, mul_one, ← hsum', hx0]; simp [normSquared]
  by_cases hy0 : (y : ℂ) = 0
  · have : gde (normSquared (y : ℂ)) = ⊤ := by
      have h0 : normSquared (0 : ℂ) = 0 := by simp [normSquared]
      rw [hy0, h0, gde, dif_pos (zero_mem _)]; exact emultiplicity_zero _
    rw [this, add_top, halfValuation, if_pos rfl, add_top, min_eq_left le_top]
    refine gde_ge _ hN m 1 (one_mem _) ?_
    rw [hy0, add_zero, mul_one, ← hsum', hy0]; simp [normSquared]
  obtain ⟨p, x', hx', hxe, hxp⟩ := fin_dec _ hxr hx0
  obtain ⟨q, y', hy', hye, hyp⟩ := fin_dec _ hyr hy0
  obtain ⟨ex, hex⟩ : ∃ ex : ℕ, gde (normSquared x') = ex ∧ ex ≤ 1 := by
    rcases eps_cases _ (nd2 _ hx' hxp) with h | h
    · exact ⟨0, h, by omega⟩
    · exact ⟨1, h, le_rfl⟩
  obtain ⟨ey, hey⟩ : ∃ ey : ℕ, gde (normSquared y') = ey ∧ ey ≤ 1 := by
    rcases eps_cases _ (nd2 _ hy' hyp) with h | h
    · exact ⟨0, h, by omega⟩
    · exact ⟨1, h, le_rfl⟩
  have hnx : normSquared (x : ℂ) = ((s : ℝ) : ℂ) ^ (2 * p) * normSquared x' := by
    rw [hxe]; unfold normSquared; rw [mul_comm, normSq_s_pow, s_pow_two_mul]; push_cast; ring
  have hny : normSquared (y : ℂ) = ((s : ℝ) : ℂ) ^ (2 * q) * normSquared y' := by
    rw [hye]; unfold normSquared; rw [mul_comm, normSq_s_pow, s_pow_two_mul]; push_cast; ring
  rw [hnx, hny, gde_spow _ _ (normSq_mem _ hx') ex hex.1, gde_spow _ _ (normSq_mem _ hy') ey hey.1,
    ← Nat.cast_add, halfV]
  -- divisibility of R
  set T := (2 * p + ex + (2 * q + ey)) / 2
  obtain ⟨R0, hR0, hRe⟩ : ∃ R0 : ℂ, R0 ∈ integralRing ∧ Rr (x : ℂ) (y : ℂ) = ((s : ℝ) : ℂ) ^ T * R0 := by
    rw [hxe, hye, Rr_scale]
    by_cases hb : ex = 1 ∧ ey = 1
    · obtain ⟨rfl, rfl⟩ := hb
      have hx'0 : gde x' = 0 := (gde_zero_iff _ hx').mpr hxp
      have hy'0 : gde y' = 0 := (gde_zero_iff _ hy').mpr hyp
      have dx : DividesIntegral ((s : ℝ) : ℂ) (normSquared x') := by
        by_contra hc; rw [← gde_zero_iff _ (normSq_mem _ hx'), hex.1] at hc; exact absurd hc (by simp)
      have dy : DividesIntegral ((s : ℝ) : ℂ) (normSquared y') := by
        by_contra hc; rw [← gde_zero_iff _ (normSq_mem _ hy'), hey.1] at hc; exact absurd hc (by simp)
      -- bilinear divisibility on primitive parts
      obtain ⟨a, ha⟩ := (mem_iff x').mp hx'
      obtain ⟨b, hb⟩ := (mem_iff y').mp hy'
      have hdiv : DividesIntegral ((s : ℝ) : ℂ) (Rr x' y') := by
        have hxp' := hxp; have hyp' := hyp
        rw [ha, dvd_sqrt2_iff] at hxp'
        rw [hb, dvd_sqrt2_iff] at hyp'
        rw [ha, dvd_sqrt2_norm] at dx
        rw [hb, dvd_sqrt2_norm] at dy
        unfold Rr
        rw [ha, hb, bil, real_cv, dvd_sqrt2_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
          Matrix.head_cons, Matrix.tail_cons, add_zero, add_neg_cancel]
        refine ⟨?_, by simp⟩
        have key : ∀ x0 x1 x2 x3 y0 y1 y2 y3 : ZMod 2, ¬(x0 + x2 = 0 ∧ x1 + x3 = 0) →
            ¬(y0 + y2 = 0 ∧ y1 + y3 = 0) → x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = 0 →
            y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2 = 0 →
            x0 * (y1 - y3) + y0 * (x1 - x3) + x2 * (y1 + y3) + y2 * (x1 + x3) = 0 := by decide
        have ev : ∀ n : ℤ, Even n ↔ (n : ZMod 2) = 0 := fun n => by
          rw [even_iff_two_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]; norm_num
        simp only [formP, ev] at hxp' hyp' dx dy ⊢
        push_cast at hxp' hyp' dx dy ⊢
        exact key _ _ _ _ _ _ _ _ hxp' hyp' dx dy
      obtain ⟨⟨r0, hr0⟩, hr0'⟩ := hdiv
      refine ⟨r0, hr0, ?_⟩
      rw [hr0', show T = p + q + 1 by omega, pow_succ]; ring
    · refine ⟨Rr x' y', Rr_mem _ _ hx' hy', ?_⟩
      rw [show T = p + q by omega]
  -- final
  have hfin := normSq_add_R (x : ℂ) (y : ℂ)
  rw [hsum', hRe] at hfin
  have hmin : ((min m (1 + T) : ℕ) : ℕ∞) ≤ gde (normSquared ((x : ℂ) + (y : ℂ))) := by
    refine gde_ge _ hN _ (((s : ℝ) : ℂ) ^ (m - min m (1 + T)) + ((s : ℝ) : ℂ) ^ (1 + T - min m (1 + T)) * R0)
      (add_mem (pow_mem s_mem _) (mul_mem (pow_mem s_mem _) hR0)) ?_
    have e1 : ((s : ℝ) : ℂ) ^ m = ((s : ℝ) : ℂ) ^ (min m (1 + T)) * ((s : ℝ) : ℂ) ^ (m - min m (1 + T)) := by
      rw [← pow_add, Nat.add_sub_cancel' (min_le_left _ _)]
    have e2 : ((s : ℝ) : ℂ) * ((s : ℝ) : ℂ) ^ T =
        ((s : ℝ) : ℂ) ^ (min m (1 + T)) * ((s : ℝ) : ℂ) ^ (1 + T - min m (1 + T)) := by
      rw [← pow_add, Nat.add_sub_cancel' (min_le_right _ _), pow_add, pow_one]
    rw [hfin, e1, ← mul_assoc, e2]; ring
  calc min (m : ℕ∞) (1 + ((T : ℕ) : ℕ∞)) = ((min m (1 + T) : ℕ) : ℕ∞) := by push_cast; rfl
    _ ≤ _ := hmin

end G68Z

namespace G68Z

lemma spow_add (a b : ℤ) : ((s : ℝ) : ℂ) ^ a * ((s : ℝ) : ℂ) ^ b = ((s : ℝ) : ℂ) ^ (a + b) :=
  (zpow_add₀ s_ne a b).symm

lemma val_iff (v : ℂ) (hv : v ∈ integralRing) (g : ℕ) (hg : gde v = g) (j : ℤ) :
    v * ((s : ℝ) : ℂ) ^ j ∈ integralRing ↔ -(g : ℤ) ≤ j := by
  have hg' := hg
  rw [gde, dif_pos hv] at hg'
  obtain ⟨⟨c, hc⟩, hce⟩ := pow_dvd_of_le_emultiplicity (le_of_eq hg'.symm)
  have hvc : v = ((s : ℝ) : ℂ) ^ g * c := by
    have := congrArg Subtype.val hce; simpa [sqrtTwoInteger_val] using this
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨t, ht⟩ : ∃ t : ℕ, j = -(t : ℤ) := ⟨(-j).toNat, by omega⟩
    have hle := gde_ge v hv t _ h (by
      rw [ht, zpow_neg, zpow_natCast]; have := pow_ne_zero t s_ne; field_simp)
    rw [hg] at hle
    have : t ≤ g := by exact_mod_cast hle
    omega
  · intro h
    obtain ⟨t, ht⟩ : ∃ t : ℕ, (g : ℤ) + j = t := ⟨((g : ℤ) + j).toNat, by omega⟩
    have : v * ((s : ℝ) : ℂ) ^ j = c * ((s : ℝ) : ℂ) ^ t := by
      rw [hvc, ← zpow_natCast, mul_comm _ c, mul_assoc, spow_add, ht, zpow_natCast]
    rw [this]; exact mul_mem hc (pow_mem s_mem _)

lemma sde_of (v : ℂ) (hv : v ∈ integralRing) (g : ℕ) (hg : gde v = g) (M : ℤ) :
    IsSDE (v * ((s : ℝ) : ℂ) ^ M) (-(g : ℤ) - M) := by
  refine ⟨?_, fun e he => ?_⟩
  · rw [mul_assoc, spow_add]; exact (val_iff v hv g hg _).mpr (by omega)
  · rw [mul_assoc, spow_add] at he
    have := (val_iff v hv g hg _).mp he
    omega

lemma sde_unique {c : ℂ} {d e : ℤ} (h1 : IsSDE c d) (h2 : IsSDE c e) : d = e :=
  le_antisymm (h1.2 e h2.1) (h2.2 d h1.1)

lemma amp (z : ℂ) (hz : z ∈ synthesisRing) (hz0 : z ≠ 0) :
    ∃ D : ℤ, IsSDE z D ∧ ¬ DividesIntegral ((s : ℝ) : ℂ) (z * ((s : ℝ) : ℂ) ^ D) := by
  obtain ⟨K, hK⟩ := synth z hz
  have hx0 : z * ((s : ℝ) : ℂ) ^ K ≠ 0 := mul_ne_zero hz0 (pow_ne_zero _ s_ne)
  obtain ⟨p, x', hx', he, hxp⟩ := fin_dec _ hK hx0
  have hzx : z * ((s : ℝ) : ℂ) ^ ((K : ℤ) - p) = x' := by
    have : z * ((s : ℝ) : ℂ) ^ ((K : ℤ) - p) = z * ((s : ℝ) : ℂ) ^ K * ((s : ℝ) : ℂ) ^ (-(p : ℤ)) := by
      rw [mul_assoc, ← zpow_natCast, spow_add]; ring_nf
    rw [this, he, mul_comm (((s : ℝ) : ℂ) ^ p), mul_assoc, ← zpow_natCast, spow_add, add_neg_cancel,
      zpow_zero, mul_one]
  refine ⟨(K : ℤ) - p, ⟨by rw [hzx]; exact hx', fun e he' => ?_⟩, by rw [hzx]; exact hxp⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (K : ℤ) - p - e = t + 1 := ⟨((K : ℤ) - p - e - 1).toNat, by omega⟩
  apply hxp
  refine ⟨⟨z * ((s : ℝ) : ℂ) ^ e * ((s : ℝ) : ℂ) ^ t, mul_mem he' (pow_mem s_mem _)⟩, ?_⟩
  simp only
  rw [← hzx]
  rw [show (K : ℤ) - p = e + ((t : ℤ) + 1) by omega, ← spow_add, zpow_add₀ s_ne, zpow_natCast, zpow_one]
  ring

lemma omega_zpow_mem (k : ℤ) : ω ^ k ∈ integralRing := by
  have hω : ω ∈ integralRing := Subring.subset_closure (by simp)
  have hinv : ω⁻¹ = ω ^ 7 := by
    have h8 : ω * ω ^ 7 = 1 := by
      rw [← pow_succ', show 7 + 1 = 4 * 2 from rfl, pow_mul, omega_four]; norm_num
    exact (eq_inv_of_mul_eq_one_right h8).symm
  rcases k with n | n
  · simp only [Int.ofNat_eq_natCast, zpow_natCast]; exact pow_mem hω _
  · rw [zpow_negSucc, ← inv_pow, hinv]; exact pow_mem (pow_mem hω _) _

lemma normSq_omega_zpow (k : ℤ) : Complex.normSq (ω ^ k) = 1 := by
  rw [map_zpow₀, normSq_omega, one_zpow]

lemma gde_one : gde 1 = 0 := by
  rw [gde_zero_iff _ (one_mem _)]
  have : (1 : ℂ) = coordinateValue ![1, 0, 0, 0] := by simp [coordinateValue]
  rw [this, dvd_sqrt2_iff]; simp

lemma gde_strict (a b : ℂ) (ha : a ∈ integralRing) (hb : b ∈ integralRing) (g : ℕ)
    (hga : gde a = g) (hgb : (g : ℕ∞) < gde b) : gde (a + b) = g := by
  rw [gde, dif_pos ha] at hga
  rw [gde, dif_pos hb] at hgb
  rw [gde, dif_pos (add_mem ha hb)]
  have e : (⟨a + b, add_mem ha hb⟩ : integralRing) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
  rw [e]
  rw [emultiplicity_eq_coe] at hga ⊢
  have hB : sqrtTwoInteger ^ (g + 1) ∣ (⟨b, hb⟩ : integralRing) :=
    pow_dvd_of_le_emultiplicity (by exact_mod_cast Order.add_one_le_of_lt hgb)
  refine ⟨dvd_add hga.1 (dvd_trans (pow_dvd_pow _ (Nat.le_succ g)) hB), fun h => hga.2 ?_⟩
  have := dvd_sub h hB
  convert this using 1
  exact Subtype.ext (by simp)

end G68Z

open G68Z in
/-- Lemma 2, PDF p.6: both sde arguments are squared moduli. Finite exponents
are expressed by their least-exponent graph, with integer k unrestricted. -/
theorem solution (z w : ℂ)
    (hz : z ∈ synthesisRing) (hw : w ∈ synthesisRing)
    (hstate : Complex.normSq z + Complex.normSq w = 1)
    (d : ℤ) (hd : IsSDE (normSquared z) d) (hlarge : 4 ≤ d) (k : ℤ) :
    ∃ e : ℤ,
      IsSDE (normSquared ((z + w * (QAlgorithms.gateT true true) ^ k) / ((Real.sqrt 2 : ℝ) : ℂ))) e ∧
      -1 ≤ e - d ∧ e - d ≤ 1 := by
  -- z ≠ 0
  have hz0 : z ≠ 0 := by
    rintro rfl
    have h0 : normSquared (0 : ℂ) = 0 := by simp [normSquared]
    rw [h0] at hd
    have := hd.2 (d - 1) (by simp [zero_mem])
    omega
  obtain ⟨D, hD, hxp⟩ := amp z hz hz0
  have hx := hD.1
  obtain ⟨ε, hε, hε1⟩ : ∃ ε : ℕ, gde (normSquared (z * ((s : ℝ) : ℂ) ^ D)) = ε ∧ ε ≤ 1 := by
    rcases eps_cases _ (nd2 _ hx hxp) with h | h
    · exact ⟨0, h, by omega⟩
    · exact ⟨1, h, le_rfl⟩
  have hnz : normSquared z = normSquared (z * ((s : ℝ) : ℂ) ^ D) * ((s : ℝ) : ℂ) ^ (-(2 * D)) := by
    unfold normSquared
    rw [Complex.normSq_mul, map_zpow₀, Complex.normSq_ofReal, s_mul]; push_cast
    rw [mul_assoc, show (2 : ℂ) = ((s : ℝ) : ℂ) ^ (2 : ℤ) by rw [zpow_ofNat, sq2c], ← zpow_mul, spow_add]
    ring_nf; rw [zpow_zero, mul_one]
  have hd' := sde_of _ (normSq_mem _ hx) ε hε (-(2 * D))
  rw [← hnz] at hd'
  have hdD := sde_unique hd hd'
  have hD2 : 2 ≤ D := by omega
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, D = n := ⟨D.toNat, by omega⟩
  obtain ⟨hwD, -, hy, hgxy, -⟩ := core z w hw hstate n hD (by omega)
  simp only [zpow_natCast] at hx hy hgxy hε hxp
  set x := z * ((s : ℝ) : ℂ) ^ n
  set y := w * ((s : ℝ) : ℂ) ^ n
  set ωk := (QAlgorithms.gateT true true) ^ k
  have hωk : ωk ∈ integralRing := omega_zpow_mem k
  have hyω : y * ωk ∈ integralRing := mul_mem hy hωk
  have hnyω : normSquared (y * ωk) = normSquared y := by
    unfold normSquared; rw [Complex.normSq_mul, normSq_omega_zpow, mul_one]
  have hsumR : Complex.normSq x + Complex.normSq (y * ωk) = Real.sqrt 2 ^ (2 * n) := by
    have e1 : Complex.normSq x = Complex.normSq z * 2 ^ n := normSq_s_pow z n
    have e2 : Complex.normSq (y * ωk) = Complex.normSq w * 2 ^ n := by
      rw [Complex.normSq_mul, normSq_omega_zpow, mul_one]; exact normSq_s_pow w n
    rw [e1, e2, pow_mul, show Real.sqrt 2 ^ 2 = 2 from s_sq]
    linear_combination (2 : ℝ) ^ n * hstate
  -- lower bound on gde |u|²
  set u := x + y * ωk
  set v := x - y * ωk
  have hu : u ∈ integralRing := add_mem hx hyω
  have hv : v ∈ integralRing := sub_mem hx hyω
  have hεy : gde (normSquared (y * ωk)) = ε := by rw [hnyω, ← hgxy, hε]
  have low := nsvb ⟨x, hx⟩ ⟨y * ωk, hyω⟩ (2 * n) hsumR
  simp only at low
  rw [hε, hεy, ← Nat.cast_add, halfV, show (ε + ε) / 2 = ε by omega] at low
  have low' : ((1 + ε : ℕ) : ℕ∞) ≤ gde (normSquared u) := by
    refine le_trans (le_of_eq ?_) low
    rw [min_eq_right (by exact_mod_cast (by omega : 1 + ε ≤ 2 * n))]; push_cast; rfl
  -- upper bound via u + v = 2x
  have hsumUV : Complex.normSq u + Complex.normSq v = Real.sqrt 2 ^ (2 * n + 2) := by
    have h1 : Complex.normSq u + Complex.normSq v = 2 * (Complex.normSq x + Complex.normSq (y * ωk)) := by
      simp only [u, v, Complex.normSq_add, Complex.normSq_sub]; ring
    rw [h1, hsumR, pow_add, show Real.sqrt 2 ^ 2 = 2 from s_sq]; ring
  have up := nsvb ⟨u, hu⟩ ⟨v, hv⟩ (2 * n + 2) hsumUV
  simp only at up
  have huv : u + v = ((s : ℝ) : ℂ) ^ 2 * x := by simp only [u, v]; rw [sq2c]; ring
  have hg2x : gde (normSquared (u + v)) = ((4 + ε : ℕ) : ℕ∞) := by
    rw [huv]
    have : normSquared (((s : ℝ) : ℂ) ^ 2 * x) = ((s : ℝ) : ℂ) ^ 4 * normSquared x := by
      unfold normSquared; rw [mul_comm, normSq_s_pow]; push_cast
      rw [show (4 : ℕ) = 2 * 2 from rfl, s_pow_two_mul]; ring
    rw [this, gde_spow 4 _ (normSq_mem _ hx) ε hε]
  rw [hg2x] at up
  -- gde|u|² = gde|v|²
  have hsumC : normSquared u + normSquared v = ((s : ℝ) : ℂ) ^ (2 * n + 2) * 1 := by
    unfold normSquared; rw [mul_one]; push_cast
    rw [show (Complex.normSq u : ℂ) + Complex.normSq v = ((Complex.normSq u + Complex.normSq v : ℝ) : ℂ) by
      push_cast; ring, hsumUV]; push_cast; rfl
  have hg1 : gde (normSquared u + normSquared v) = ((2 * n + 2 : ℕ) : ℕ∞) := by
    rw [hsumC, gde_spow _ 1 (one_mem _) 0 gde_one]
  have hhalf : ∀ a b : ℕ∞, (6 : ℕ∞) ≤ a → (6 : ℕ∞) ≤ b → ((4 + ε : ℕ) : ℕ∞) < 1 + halfValuation (a + b) := by
    intro a b ha hb
    by_cases hab : a + b = ⊤
    · rw [hab, halfValuation, if_pos rfl, add_top]; exact ENat.coe_lt_top _
    · obtain ⟨N, hN⟩ : ∃ N : ℕ, a + b = N := ⟨(a + b).toNat, (ENat.coe_toNat hab).symm⟩
      rw [hN, halfV]
      have h12 : (12 : ℕ∞) ≤ N := by rw [← hN]; exact le_trans (by norm_num) (add_le_add ha hb)
      have : 12 ≤ N := by exact_mod_cast h12
      have : 4 + ε < 1 + N / 2 := by omega
      exact_mod_cast this
  have h6 : (6 : ℕ∞) ≤ ((2 * n + 2 : ℕ) : ℕ∞) := by exact_mod_cast (by omega : 6 ≤ 2 * n + 2)
  have hmin_lt : ((4 + ε : ℕ) : ℕ∞) < ((2 * n + 2 : ℕ) : ℕ∞) := by exact_mod_cast (by omega : 4 + ε < 2 * n + 2)
  have hupper : 1 + halfValuation (gde (normSquared u) + gde (normSquared v)) ≤ ((4 + ε : ℕ) : ℕ∞) := by
    by_contra hc
    push Not at hc
    exact absurd up (not_le.mpr (lt_min hmin_lt hc))
  -- gde|u|² = gde|v|²
  have hnu := normSq_mem _ hu
  have hnv := normSq_mem _ hv
  have heq : gde (normSquared u) = gde (normSquared v) := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt)
      have := gde_strict _ _ hnu hnv g hg.symm (hg ▸ hlt)
      rw [hg1] at this
      have hg' : g = 2 * n + 2 := by exact_mod_cast this.symm
      have := hhalf _ _ (hg ▸ hg' ▸ h6) (le_trans (hg ▸ hg' ▸ h6) hlt.le)
      exact absurd hupper (not_le.mpr this)
    · obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt)
      have := gde_strict _ _ hnv hnu g hg.symm (hg ▸ hlt)
      rw [add_comm, hg1] at this
      have hg' : g = 2 * n + 2 := by exact_mod_cast this.symm
      have := hhalf _ _ (le_trans (hg ▸ hg' ▸ h6) hlt.le) (hg ▸ hg' ▸ h6)
      exact absurd hupper (not_le.mpr this)
  rw [← heq] at hupper
  have hfin : gde (normSquared u) ≠ ⊤ := by
    intro htop
    rw [htop, top_add, halfValuation, if_pos rfl, add_top] at hupper
    exact absurd hupper (by simp)
  obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hg, ← Nat.cast_add, halfV, show (g + g) / 2 = g by omega] at hupper
  rw [← hg] at low'
  have hg3 : 1 + g ≤ 4 + ε := by exact_mod_cast hupper
  have hg1' : 1 + ε ≤ g := by exact_mod_cast low'
  -- the new squared modulus
  have hz' : normSquared ((z + w * QAlgorithms.gateT true true ^ k) / ((Real.sqrt 2 : ℝ) : ℂ)) =
      normSquared u * ((s : ℝ) : ℂ) ^ (-(2 * (n : ℤ) + 2)) := by
    have hu' : (z + w * QAlgorithms.gateT true true ^ k) / ((Real.sqrt 2 : ℝ) : ℂ) =
        u * ((s : ℝ) : ℂ) ^ (-((n : ℤ) + 1)) := by
      simp only [u, x, y, ωk]
      rw [zpow_neg, zpow_add₀ s_ne, zpow_natCast, zpow_one]
      have h1 := s_ne
      have h2 := pow_ne_zero n s_ne
      field_simp
    rw [hu']
    unfold normSquared
    rw [Complex.normSq_mul, map_zpow₀, Complex.normSq_ofReal, s_mul]; push_cast
    rw [show (2 : ℂ) = ((s : ℝ) : ℂ) ^ (2 : ℤ) by rw [zpow_ofNat, sq2c], ← zpow_mul]
    ring_nf
  have hsde := sde_of _ hnu g hg.symm (-(2 * (n : ℤ) + 2))
  rw [← hz'] at hsde
  refine ⟨_, hsde, by omega, by omega⟩
