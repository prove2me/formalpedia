-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P15.remark3_nearTightness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:59:01.970324+00:00
-- url     : https://prove2.me/submissions/2d7852d4-460c-4150-a3f0-fb957a25012a

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P15

namespace X6P15r

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in

lemma two_selfAdjoint (P : Matrix ι ι ℂ) (hPh : Pᴴ = P) (a b : ℝ) :
    IsSelfAdjoint ((a : ℂ) • P + (b : ℂ) • (1 - P)) := by
  show ((a : ℂ) • P + (b : ℂ) • (1 - P))ᴴ = _
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_sub,
    conjTranspose_one, hPh]
  simp

lemma spectrum_two (P : Matrix ι ι ℂ) (hP : P * P = P) (a b : ℝ) (r : ℝ)
    (hr : r ∈ spectrum ℝ ((a : ℂ) • P + (b : ℂ) • (1 - P))) : r = a ∨ r = b := by
  by_contra h
  push Not at h
  obtain ⟨ha, hb⟩ := h
  apply (spectrum.mem_iff.1 hr)
  have ha' : ((r : ℂ) - a) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast ha
  have hb' : ((r : ℂ) - b) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hb
  set Y : Matrix ι ι ℂ := ((r : ℂ) - a)⁻¹ • P + ((r : ℂ) - b)⁻¹ • (1 - P)
  have hX : algebraMap ℝ (Matrix ι ι ℂ) r - ((a : ℂ) • P + (b : ℂ) • (1 - P)) =
      ((r : ℂ) - a) • P + ((r : ℂ) - b) • (1 - P) := by
    rw [Algebra.algebraMap_eq_smul_one]
    rw [show (r • (1 : Matrix ι ι ℂ)) = (r : ℂ) • (1 : Matrix ι ι ℂ) by
      rw [← Complex.coe_smul]]
    simp only [sub_smul, smul_sub]
    abel
  rw [hX]
  have hP1 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hP2 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have hP3 : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, one_mul, hP1, sub_zero]
  refine isUnit_iff_exists.2 ⟨Y, ?_, ?_⟩
  · simp only [Y, add_mul, mul_add, smul_mul_smul, hP, hP1, hP2, hP3, smul_zero, add_zero,
      zero_add, mul_inv_cancel₀ ha', mul_inv_cancel₀ hb', one_smul]
    abel
  · simp only [Y, add_mul, mul_add, smul_mul_smul, hP, hP1, hP2, hP3, smul_zero, add_zero,
      zero_add, inv_mul_cancel₀ ha', inv_mul_cancel₀ hb', one_smul]
    abel

lemma cfc_two (P : Matrix ι ι ℂ) (hP : P * P = P) (hPh : Pᴴ = P) (a b : ℝ) (f : ℝ → ℝ) :
    cfc f ((a : ℂ) • P + (b : ℂ) • (1 - P)) = (f a : ℂ) • P + (f b : ℂ) • (1 - P) := by
  have hsa := two_selfAdjoint P hPh a b
  rcases eq_or_ne a b with hab | hab
  · subst hab
    have : (a : ℂ) • P + (a : ℂ) • (1 - P) = algebraMap ℝ (Matrix ι ι ℂ) a := by
      rw [← smul_add, add_sub_cancel, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
    rw [this, cfc_algebraMap, Algebra.algebraMap_eq_smul_one, ← smul_add, add_sub_cancel,
      ← Complex.coe_smul]
  · set α : ℝ := (f a - f b) / (a - b)
    set β : ℝ := (a * f b - b * f a) / (a - b)
    have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
    have hcongr : cfc f ((a : ℂ) • P + (b : ℂ) • (1 - P)) =
        cfc (fun x => α * x + β) ((a : ℂ) • P + (b : ℂ) • (1 - P)) := by
      apply cfc_congr
      intro r hr
      rcases spectrum_two P hP a b r hr with h | h
      · subst h; simp only [α, β]; field_simp; ring
      · subst h; simp only [α, β]; field_simp; ring
    rw [hcongr, cfc_add (a := (a : ℂ) • P + (b : ℂ) • (1 - P)) (fun x => α * x) (fun _ => β),
      cfc_const_mul α (fun x => x) ((a : ℂ) • P + (b : ℂ) • (1 - P)),
      cfc_id' (R := ℝ) (a := (a : ℂ) • P + (b : ℂ) • (1 - P)),
      cfc_const β ((a : ℂ) • P + (b : ℂ) • (1 - P))]
    rw [Algebra.algebraMap_eq_smul_one]
    rw [show (β • (1 : Matrix ι ι ℂ)) = (β : ℂ) • (1 : Matrix ι ι ℂ) by
      rw [← Complex.coe_smul]]
    rw [show (α • ((a : ℂ) • P + (b : ℂ) • (1 - P))) =
        (α : ℂ) • ((a : ℂ) • P + (b : ℂ) • (1 - P)) by rw [← Complex.coe_smul]]
    have hab'' : (a : ℂ) - b ≠ 0 := by rw [sub_ne_zero]; exact_mod_cast hab
    have e1 : (f a : ℂ) = α * a + β := by
      simp only [α, β]; push_cast; field_simp; ring
    have e2 : (f b : ℂ) = α * b + β := by
      simp only [α, β]; push_cast; field_simp; ring
    rw [e1, e2]
    simp only [smul_add, smul_sub, smul_smul, add_smul, sub_smul]
    abel

lemma sq_two (P : Matrix ι ι ℂ) (hP : P * P = P) (hPh : Pᴴ = P) (x y : ℝ) :
    ((x : ℂ) • P + (y : ℂ) • (1 - P))ᴴ * ((x : ℂ) • P + (y : ℂ) • (1 - P)) =
      ((x * x : ℝ) : ℂ) • P + ((y * y : ℝ) : ℂ) • (1 - P) := by
  have hP1 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hP2 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have hP3 : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, one_mul, hP1, sub_zero]
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_sub,
    conjTranspose_one, hPh]
  simp only [Complex.star_def, Complex.conj_ofReal, add_mul, mul_add, smul_mul_smul, hP, hP1,
    hP2, hP3, smul_zero, add_zero, zero_add]
  push_cast; ring_nf

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P15
open QAlgorithms.Papers.Independent.Information100.P08 (bellVector)

lemma P_apply (d : ℕ) (p q : Fin d × Fin d) :
    pureDensity (bellVector d) p q = if p.1 = p.2 ∧ q.1 = q.2 then ((d : ℂ))⁻¹ else 0 := by
  simp only [pureDensity, bellVector, Matrix.of_apply]
  by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;> simp [hp, hq]
  rw [← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (Nat.cast_nonneg d)]
  simp

lemma diag_sum (d : ℕ) (c : ℂ) :
    ∑ x : Fin d × Fin d, (if x.1 = x.2 then c else 0) = d * c := by
  rw [Fintype.sum_prod_type]
  simp

lemma P_mul (d : ℕ) (hd : 0 < d) :
    pureDensity (bellVector d) * pureDensity (bellVector d) = pureDensity (bellVector d) := by
  ext p q
  rw [Matrix.mul_apply]
  simp only [P_apply]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  by_cases h : p.1 = p.2 ∧ q.1 = q.2
  · have : ∀ x : Fin d × Fin d, ((if p.1 = p.2 ∧ x.1 = x.2 then (d : ℂ)⁻¹ else 0) *
        (if x.1 = x.2 ∧ q.1 = q.2 then (d : ℂ)⁻¹ else 0)) =
        if x.1 = x.2 then (d : ℂ)⁻¹ * (d : ℂ)⁻¹ else 0 := by
      intro x; by_cases hx : x.1 = x.2 <;> simp [hx, h]
    rw [Finset.sum_congr rfl (fun x _ => this x), diag_sum, if_pos h]
    field_simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hp : p.1 = p.2
    · have hq : ¬ q.1 = q.2 := fun hq => h ⟨hp, hq⟩
      simp [hq]
    · simp [hp]

lemma P_herm (d : ℕ) : (pureDensity (bellVector d))ᴴ = pureDensity (bellVector d) := by
  ext p q
  simp only [conjTranspose_apply, P_apply]
  by_cases h1 : p.1 = p.2 <;> by_cases h2 : q.1 = q.2 <;> simp [h1, h2]

lemma P_trace (d : ℕ) (hd : 0 < d) : (pureDensity (bellVector d)).trace = 1 := by
  rw [Matrix.trace]
  simp only [diag_apply, P_apply, and_self]
  rw [diag_sum]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

lemma one_trace (d : ℕ) : (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ).trace = (d : ℂ) ^ 2 := by
  rw [Matrix.trace_one]; simp [Fintype.card_prod, sq]

lemma trace_two (d : ℕ) (hd : 0 < d) (a b : ℂ) :
    (a • pureDensity (bellVector d) + b • (1 - pureDensity (bellVector d))).trace =
      a + b * ((d : ℂ) ^ 2 - 1) := by
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_sub, P_trace d hd,
    one_trace]
  simp

lemma traceLeft_P (d : ℕ) :
    traceLeft (pureDensity (bellVector d)) = (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext b b'
  simp only [traceLeft, Matrix.of_apply, P_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : b = b'
  · subst h; simp
  · simp only [if_neg h, mul_zero]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : a = b
    · subst ha; simp [h]
    · simp [ha]

lemma traceLeft_lin (d : ℕ) (a b : ℂ) (A B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    traceLeft (a • A + b • B) = a • traceLeft A + b • traceLeft B := by
  ext x y
  simp [traceLeft, Finset.sum_add_distrib, Finset.mul_sum]

lemma traceLeft_sub (d : ℕ) (A B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    traceLeft (A - B) = traceLeft A - traceLeft B := by
  ext x y
  simp [traceLeft, Finset.sum_sub_distrib]

lemma traceLeft_one (d : ℕ) :
    traceLeft (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) = (d : ℂ) • 1 := by
  ext x y
  simp only [traceLeft, Matrix.of_apply, Matrix.one_apply, Prod.mk.injEq, true_and,
    Matrix.smul_apply, smul_eq_mul]
  by_cases h : x = y <;> simp [h]

lemma vn_two (d : ℕ) (hd : 0 < d) (a b : ℝ) :
    vnEntropy ((a : ℂ) • pureDensity (bellVector d) + (b : ℂ) • (1 - pureDensity (bellVector d))) =
      -(a * Real.logb 2 a + b * Real.logb 2 b * ((d : ℝ) ^ 2 - 1)) := by
  unfold vnEntropy
  rw [cfc_two _ (P_mul d hd) (P_herm d), trace_two d hd]
  have hre : ((d : ℂ) ^ 2).re = (d : ℝ) ^ 2 := by
    rw [show ((d : ℂ) ^ 2) = (((d : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
  have him : ((d : ℂ) ^ 2).im = 0 := by
    rw [show ((d : ℂ) ^ 2) = (((d : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_im]
  simp [Complex.add_re, Complex.mul_re, hre, him]

end X6P15r

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P15 Matrix
open QAlgorithms.Papers.Independent.Information100.P08 (bellVector)
open scoped ComplexOrder

lemma X6_first (d : ℕ) (hd : 2 ≤ d) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsDensityMatrix (pureDensity (bellVector d)) ∧ IsDensityMatrix (isotropicDensity d ε) ∧
      traceDistance (isotropicDensity d ε) (pureDensity (bellVector d)) = ε ∧
      finiteConditionalEntropy (isotropicDensity d ε) -
        finiteConditionalEntropy (pureDensity (bellVector d)) =
        ε * Real.logb 2 ((d : ℝ) ^ 2 - 1) + binEntropy2 ε := by
  have hd0 : 0 < d := by omega
  set P := pureDensity (bellVector d) with hPdef
  have hP := X6P15r.P_mul d hd0
  have hPh := X6P15r.P_herm d
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hD : (0 : ℝ) < (d : ℝ) ^ 2 - 1 := by nlinarith
  set c : ℝ := ε / ((d : ℝ) ^ 2 - 1) with hc
  have hc0 : 0 ≤ c := div_nonneg h0 hD.le
  have hcD : c * ((d : ℝ) ^ 2 - 1) = ε := by rw [hc]; field_simp
  have hρ : isotropicDensity d ε = ((1 - ε : ℝ) : ℂ) • P + ((c : ℝ) : ℂ) • (1 - P) := rfl
  have hQ : (1 - P).PosSemidef := by
    have := X6P15r.sq_two P hP hPh 0 1
    simp only [Complex.ofReal_zero, zero_smul, Complex.ofReal_one, one_smul, zero_add,
      mul_zero, mul_one] at this
    rw [← this]; exact posSemidef_conjTranspose_mul_self _
  have hPpsd : P.PosSemidef := pureDensity_posSemidef _
  refine ⟨⟨hPpsd, X6P15r.P_trace d hd0⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hρ]
    exact (hPpsd.smul (by exact_mod_cast (by linarith : (0 : ℝ) ≤ 1 - ε))).add
      (hQ.smul (by exact_mod_cast hc0))
  · rw [hρ, X6P15r.trace_two d hd0]
    have : ((c : ℝ) : ℂ) * ((d : ℂ) ^ 2 - 1) = (ε : ℂ) := by
      rw [← hcD]; push_cast; ring
    rw [this]; push_cast; ring
  · unfold traceDistance traceNorm
    have hdiff : isotropicDensity d ε - P = ((-ε : ℝ) : ℂ) • P + ((c : ℝ) : ℂ) • (1 - P) := by
      rw [hρ]; push_cast; module
    rw [hdiff, X6P15r.sq_two P hP hPh, X6P15r.cfc_two P hP hPh, X6P15r.trace_two d hd0,
      neg_mul_neg, Real.sqrt_mul_self h0, Real.sqrt_mul_self hc0]
    have hre : ((d : ℂ) ^ 2).re = (d : ℝ) ^ 2 := by
      rw [show ((d : ℂ) ^ 2) = (((d : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
    have him : ((d : ℂ) ^ 2).im = 0 := by
      rw [show ((d : ℂ) ^ 2) = (((d : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_im]
    simp [Complex.add_re, Complex.mul_re, hre, him, abs_of_nonneg h0]
    nlinarith [hcD]
  · unfold finiteConditionalEntropy
    have htl : traceLeft (isotropicDensity d ε) = traceLeft P := by
      rw [hρ, X6P15r.traceLeft_lin, X6P15r.traceLeft_sub, X6P15r.traceLeft_one,
        X6P15r.traceLeft_P]
      have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
        smul_eq_mul]
      split_ifs
      · have : ((c : ℝ) : ℂ) * ((d : ℂ) ^ 2 - 1) = (ε : ℂ) := by
          rw [← hcD]; push_cast; ring
        field_simp
        push_cast at this ⊢
        linear_combination this
      · simp
    have hvP : vnEntropy P = 0 := by
      have := X6P15r.vn_two d hd0 1 0
      simpa using this
    rw [htl, hvP, hρ, X6P15r.vn_two d hd0]
    unfold binEntropy2 Real.binEntropy
    rcases h0.eq_or_lt with he | he
    · subst he; simp [hc]
    · have hc' : 0 < c := div_pos he hD
      have hlogc : Real.log c = Real.log ε - Real.log ((d : ℝ) ^ 2 - 1) := by
        rw [hc, Real.log_div he.ne' hD.ne']
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      clear_value c
      generalize hDD : (d : ℝ) ^ 2 - 1 = D at *
      simp only [Real.logb, Real.log_inv]
      rw [hlogc]
      field_simp
      linear_combination (-(Real.log ε - Real.log D)) * hcD

theorem solution :
    (∀ (d : ℕ), 2 ≤ d → ∀ (epsilon : ℝ), 0 ≤ epsilon → epsilon ≤ 1 →
      let sigma := (pureDensity (bellVector d))
      let rho := isotropicDensity d epsilon
      IsDensityMatrix sigma ∧ IsDensityMatrix rho ∧ traceDistance rho sigma = epsilon ∧
      finiteConditionalEntropy rho - finiteConditionalEntropy sigma =
        epsilon * Real.logb 2 ((d : ℝ)^2 - 1) + binEntropy2 epsilon) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ d : ℕ, N ≤ d →
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ 1 →
      |(finiteConditionalEntropy (isotropicDensity d epsilon) -
          finiteConditionalEntropy (pureDensity (bellVector d))) -
        (2 * epsilon * Real.logb 2 (d : ℝ) + binEntropy2 epsilon)| ≤
          C * epsilon / (d : ℝ)^2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨fun d hd ε h0 h1 => X6_first d hd ε h0 h1, 2 / Real.log 2, by positivity, 2, le_rfl, ?_⟩
  intro d hd ε h0 h1
  rw [(X6_first d hd ε h0 h1).2.2.2]
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  have hD : (0 : ℝ) < (d : ℝ) ^ 2 - 1 := by nlinarith
  set L := Real.log ((d : ℝ) ^ 2 - 1) - 2 * Real.log d with hL
  have hexpr : ε * Real.logb 2 ((d : ℝ) ^ 2 - 1) + binEntropy2 ε -
      (2 * ε * Real.logb 2 (d : ℝ) + binEntropy2 ε) = ε * L / Real.log 2 := by
    simp only [Real.logb, hL]; ring
  have hLdiv : L = Real.log (((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 2) := by
    rw [Real.log_div hD.ne' hd2.ne', Real.log_pow]; push_cast; ring
  have hx : 0 < ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 2 := div_pos hD hd2
  have hLle : L ≤ 0 := by
    rw [hLdiv]; apply Real.log_nonpos hx.le
    rw [div_le_one hd2]; linarith
  have hLge : -(2 / (d : ℝ) ^ 2) ≤ L := by
    have := Real.one_sub_inv_le_log_of_pos hx
    rw [← hLdiv, inv_div] at this
    have h2 : 1 - (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) = -(1 / ((d : ℝ) ^ 2 - 1)) := by
      field_simp; ring
    have h3 : 1 / ((d : ℝ) ^ 2 - 1) ≤ 2 / (d : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ hD hd2]; nlinarith
    linarith
  rw [hexpr, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h0 hLle)
    hl2.le)]
  rw [show -(ε * L / Real.log 2) = ε * (-L) / Real.log 2 by ring,
    show 2 / Real.log 2 * ε / (d : ℝ) ^ 2 = ε * (2 / (d : ℝ) ^ 2) / Real.log 2 by
      field_simp]
  gcongr
  linarith
