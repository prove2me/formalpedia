-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P03.corollary13_lowDegree
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:48:48.935974+00:00
-- url     : https://prove2.me/submissions/bf1080a7-160b-41d5-92b4-a23302b4c50d

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate Matrix

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

def g59a_pH : Fin 4 → Fin 4 := ![0, 3, 2, 1]
def g59a_sH : Fin 4 → ℝ := ![1, 1, -1, 1]
def g59a_pS : Fin 4 → Fin 4 := ![0, 2, 1, 3]
def g59a_sS : Fin 4 → ℝ := ![1, -1, 1, 1]

lemma g59a_had (p : Fin 4) :
    hadamardᴴ * singlePauli p * hadamard = ((g59a_sH p : ℝ) : ℂ) • singlePauli (g59a_pH p) := by
  have h2 : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  fin_cases p <;> ext a b <;> cases a <;> cases b <;>
    simp [hadamard, singlePauli, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fintype.sum_bool,
      g59a_sH, g59a_pH] <;> ring_nf <;> simp [h2] <;> ring_nf <;> simp [hs] <;> ring

lemma g59a_phs (p : Fin 4) :
    phaseSᴴ * singlePauli p * phaseS = ((g59a_sS p : ℝ) : ℂ) • singlePauli (g59a_pS p) := by
  fin_cases p <;> ext a b <;> cases a <;> cases b <;>
    simp [phaseS, singlePauli, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fintype.sum_bool,
      g59a_sS, g59a_pS]

lemma g59a_nwt_mul {I : Type*} [Fintype I] [DecidableEq I] (A B : I → Matrix Bool Bool ℂ) :
    namedWireTensor A * namedWireTensor B = namedWireTensor (fun i => A i * B i) := by
  ext x y
  simp only [Matrix.mul_apply, namedWireTensor]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib]

lemma g59a_nwt_ct {I : Type*} [Fintype I] [DecidableEq I] (A : I → Matrix Bool Bool ℂ) :
    (namedWireTensor A)ᴴ = namedWireTensor (fun i => (A i)ᴴ) := by
  ext x y
  simp only [Matrix.conjTranspose_apply, namedWireTensor]
  rw [show star (∏ i, A i (y i) (x i)) = starRingEnd ℂ (∏ i, A i (y i) (x i)) from rfl, map_prod]
  rfl

lemma g59a_nwt_smul_at {I : Type*} [Fintype I] [DecidableEq I] (B : I → Matrix Bool Bool ℂ) (i : I)
    (c : ℂ) : namedWireTensor (fun j => if j = i then c • B j else B j) = c • namedWireTensor B := by
  ext x y
  simp only [namedWireTensor, Matrix.smul_apply, smul_eq_mul]
  rw [show (∏ j, (if j = i then c • B j else B j) (x j) (y j)) =
      ∏ j, ((if j = i then c else 1) * B j (x j) (y j)) from
    Finset.prod_congr rfl fun j _ => by split_ifs <;> simp]
  rw [Finset.prod_mul_distrib]; simp

lemma g59a_conj {I : Type*} [Fintype I] [DecidableEq I] (P : I → Fin 4) (i : I)
    (U : Matrix Bool Bool ℂ) (q : Fin 4) (s : ℝ)
    (h : Uᴴ * singlePauli (P i) * U = (s : ℂ) • singlePauli q) (rho : Matrix (I → Bool) (I → Bool) ℂ) :
    effectProb (wordMatrix P) (conjugateWire i U rho) =
      s * effectProb (wordMatrix (Function.update P i q)) rho := by
  set V := namedWireTensor fun j => if j = i then U else (1 : Matrix Bool Bool ℂ) with hV
  have hc : conjugateWire i U rho = V * rho * Vᴴ := rfl
  have key : Vᴴ * wordMatrix P * V = (s : ℂ) • wordMatrix (Function.update P i q) := by
    rw [hV, g59a_nwt_ct, wordMatrix, g59a_nwt_mul, g59a_nwt_mul, wordMatrix, ← g59a_nwt_smul_at _ i]
    congr 1; funext j
    by_cases hj : j = i
    · subst hj; simp [h]
    · simp [hj, Function.update_of_ne hj]
  unfold effectProb
  rw [hc, show wordMatrix P * (V * rho * Vᴴ) = (wordMatrix P * V * rho) * Vᴴ by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm,
    show Vᴴ * (wordMatrix P * V * rho) = (Vᴴ * wordMatrix P * V) * rho by simp only [Matrix.mul_assoc],
    key, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

lemma g59a_xcont {I : Type*} [Fintype I] [DecidableEq I] (W : Matrix (I → Bool) (I → Bool) ℂ) :
    Continuous fun rho : Matrix (I → Bool) (I → Bool) ℂ => effectProb W rho := by
  unfold effectProb
  exact Complex.continuous_re.comp ((continuous_const.matrix_mul continuous_id).matrix_trace)

lemma g59a_ccont {I : Type*} [Fintype I] [DecidableEq I] (i : I) (U : Matrix Bool Bool ℂ) :
    Continuous (conjugateWire (I := I) i U) := by
  unfold conjugateWire
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

lemma g59a_inv {I : Type*} [Fintype I] [DecidableEq I] (D : Measure (Matrix (I → Bool) (I → Bool) ℂ))
    (f : Matrix (I → Bool) (I → Bool) ℂ → Matrix (I → Bool) (I → Bool) ℂ) (hf : Continuous f)
    (hD : Measure.map f D = D) (g : Matrix (I → Bool) (I → Bool) ℂ → ℝ) (hg : Continuous g) :
    ∫ x, g x ∂D = ∫ x, g (f x) ∂D := by
  conv_lhs => rw [← hD]
  exact integral_map hf.measurable.aemeasurable hg.measurable.aestronglyMeasurable

lemma g59a_alg (φ : Fin 4 → Fin 4 → ℝ)
    (hH : ∀ p q, φ p q = g59a_sH p * g59a_sH q * φ (g59a_pH p) (g59a_pH q))
    (hS : ∀ p q, φ p q = g59a_sS p * g59a_sS q * φ (g59a_pS p) (g59a_pS q)) :
    (∀ p q, p ≠ q → φ p q = 0) ∧ φ 2 2 = φ 1 1 ∧ φ 3 3 = φ 1 1 := by
  have hH00 : φ 0 0 = (1) * (1) * φ 0 0 := hH 0 0
  have hH01 : φ 0 1 = (1) * (1) * φ 0 3 := hH 0 1
  have hH02 : φ 0 2 = (1) * (-1) * φ 0 2 := hH 0 2
  have hH03 : φ 0 3 = (1) * (1) * φ 0 1 := hH 0 3
  have hH10 : φ 1 0 = (1) * (1) * φ 3 0 := hH 1 0
  have hH11 : φ 1 1 = (1) * (1) * φ 3 3 := hH 1 1
  have hH12 : φ 1 2 = (1) * (-1) * φ 3 2 := hH 1 2
  have hH13 : φ 1 3 = (1) * (1) * φ 3 1 := hH 1 3
  have hH20 : φ 2 0 = (-1) * (1) * φ 2 0 := hH 2 0
  have hH21 : φ 2 1 = (-1) * (1) * φ 2 3 := hH 2 1
  have hH22 : φ 2 2 = (-1) * (-1) * φ 2 2 := hH 2 2
  have hH23 : φ 2 3 = (-1) * (1) * φ 2 1 := hH 2 3
  have hH30 : φ 3 0 = (1) * (1) * φ 1 0 := hH 3 0
  have hH31 : φ 3 1 = (1) * (1) * φ 1 3 := hH 3 1
  have hH32 : φ 3 2 = (1) * (-1) * φ 1 2 := hH 3 2
  have hH33 : φ 3 3 = (1) * (1) * φ 1 1 := hH 3 3
  have hS00 : φ 0 0 = (1) * (1) * φ 0 0 := hS 0 0
  have hS01 : φ 0 1 = (1) * (-1) * φ 0 2 := hS 0 1
  have hS02 : φ 0 2 = (1) * (1) * φ 0 1 := hS 0 2
  have hS03 : φ 0 3 = (1) * (1) * φ 0 3 := hS 0 3
  have hS10 : φ 1 0 = (-1) * (1) * φ 2 0 := hS 1 0
  have hS11 : φ 1 1 = (-1) * (-1) * φ 2 2 := hS 1 1
  have hS12 : φ 1 2 = (-1) * (1) * φ 2 1 := hS 1 2
  have hS13 : φ 1 3 = (-1) * (1) * φ 2 3 := hS 1 3
  have hS20 : φ 2 0 = (1) * (1) * φ 1 0 := hS 2 0
  have hS21 : φ 2 1 = (1) * (-1) * φ 1 2 := hS 2 1
  have hS22 : φ 2 2 = (1) * (1) * φ 1 1 := hS 2 2
  have hS23 : φ 2 3 = (1) * (1) * φ 1 3 := hS 2 3
  have hS30 : φ 3 0 = (1) * (1) * φ 3 0 := hS 3 0
  have hS31 : φ 3 1 = (1) * (-1) * φ 3 2 := hS 3 1
  have hS32 : φ 3 2 = (1) * (1) * φ 3 1 := hS 3 2
  have hS33 : φ 3 3 = (1) * (1) * φ 3 3 := hS 3 3
  refine ⟨?_, by linarith, by linarith⟩
  intro p q hpq
  fin_cases p <;> fin_cases q <;> simp at hpq ⊢ <;> linarith

lemma g59a_phi {I : Type*} [Fintype I] [DecidableEq I] (D : Measure (Matrix (I → Bool) (I → Bool) ℂ))
    (hflat : IsLocallyFlat D) (P Q : I → Fin 4) (i : I) :
    let φ := fun p q => ∫ ρ, effectProb (wordMatrix (Function.update P i p)) ρ *
      effectProb (wordMatrix (Function.update Q i q)) ρ ∂D
    (∀ p q, p ≠ q → φ p q = 0) ∧ φ 2 2 = φ 1 1 ∧ φ 3 3 = φ 1 1 := by
  intro φ
  apply g59a_alg
  · intro p q
    simp only [φ]
    rw [g59a_inv D _ (g59a_ccont i hadamard) (hflat i).1 (fun ρ =>
      effectProb (wordMatrix (Function.update P i p)) ρ *
        effectProb (wordMatrix (Function.update Q i q)) ρ) ((g59a_xcont _).mul (g59a_xcont _))]
    simp only [g59a_conj (Function.update P i p) i hadamard (g59a_pH p) (g59a_sH p)
        (by rw [Function.update_self]; exact g59a_had p),
      g59a_conj (Function.update Q i q) i hadamard (g59a_pH q) (g59a_sH q)
        (by rw [Function.update_self]; exact g59a_had q), Function.update_idem]
    rw [← integral_const_mul]; congr 1; funext ρ; ring
  · intro p q
    simp only [φ]
    rw [g59a_inv D _ (g59a_ccont i phaseS) (hflat i).2 (fun ρ =>
      effectProb (wordMatrix (Function.update P i p)) ρ *
        effectProb (wordMatrix (Function.update Q i q)) ρ) ((g59a_xcont _).mul (g59a_xcont _))]
    simp only [g59a_conj (Function.update P i p) i phaseS (g59a_pS p) (g59a_sS p)
        (by rw [Function.update_self]; exact g59a_phs p),
      g59a_conj (Function.update Q i q) i phaseS (g59a_pS q) (g59a_sS q)
        (by rw [Function.update_self]; exact g59a_phs q), Function.update_idem]
    rw [← integral_const_mul]; congr 1; funext ρ; ring

lemma g59a_off {I : Type*} [Fintype I] [DecidableEq I] (D : Measure (Matrix (I → Bool) (I → Bool) ℂ))
    (hflat : IsLocallyFlat D) (P Q : I → Fin 4) (h : P ≠ Q) :
    ∫ ρ, effectProb (wordMatrix P) ρ * effectProb (wordMatrix Q) ρ ∂D = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  have := (g59a_phi D hflat P Q i).1 (P i) (Q i) hi
  simpa only [Function.update_eq_self] using this

def g59a_psi {I : Type*} [Fintype I] [DecidableEq I] (D : Measure (Matrix (I → Bool) (I → Bool) ℂ))
    (P : I → Fin 4) : ℝ :=
  ∫ ρ, effectProb (wordMatrix P) ρ * effectProb (wordMatrix P) ρ ∂D

lemma g59a_dg {I : Type*} [Fintype I] [DecidableEq I] (D : Measure (Matrix (I → Bool) (I → Bool) ℂ))
    (hflat : IsLocallyFlat D) (P : I → Fin 4) (i : I) (p q : Fin 4) (hp : p ≠ 0) (hq : q ≠ 0) :
    g59a_psi D (Function.update P i p) = g59a_psi D (Function.update P i q) := by
  obtain ⟨_, h2, h3⟩ := g59a_phi D hflat P P i
  have key : ∀ r : Fin 4, r ≠ 0 → g59a_psi D (Function.update P i r) = g59a_psi D (Function.update P i 1) := by
    intro r hr
    fin_cases r
    · exact absurd rfl hr
    · rfl
    · exact h2
    · exact h3
  rw [key p hp, key q hq]

def g59a_Zc {I : Type*} (P : I → Fin 4) : I → Fin 4 := fun i => if P i = 0 then 0 else 3

lemma g59a_canon {I : Type*} [Fintype I] [DecidableEq I] (D : Measure (Matrix (I → Bool) (I → Bool) ℂ))
    (hflat : IsLocallyFlat D) (P : I → Fin 4) : g59a_psi D P = g59a_psi D (g59a_Zc P) := by
  have key : ∀ T : Finset I, g59a_psi D P =
      g59a_psi D (fun i => if i ∈ T ∧ P i ≠ 0 then 3 else P i) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert a T ha ih =>
      rw [ih]
      set R : I → Fin 4 := fun i => if i ∈ T ∧ P i ≠ 0 then 3 else P i with hR
      by_cases hPa : P a = 0
      · congr 1; funext i
        by_cases hi : i = a
        · subst hi; simp [hR, hPa]
        · simp [hR, hi]
      · have hRa : R a = P a := by simp [hR, ha]
        have e1 : R = Function.update R a (P a) := by rw [← hRa, Function.update_eq_self]
        have e2 : (fun i => if i ∈ insert a T ∧ P i ≠ 0 then (3 : Fin 4) else P i) =
            Function.update R a 3 := by
          funext i
          by_cases hi : i = a
          · subst hi; simp [hPa]
          · simp [Function.update_of_ne hi, hR, hi]
        rw [e2]; conv_lhs => rw [e1]
        exact g59a_dg D hflat R a (P a) 3 hPa (by decide)
  rw [key Finset.univ]
  congr 1; funext i
  simp only [Finset.mem_univ, true_and, g59a_Zc]
  split_ifs <;> simp_all

open scoped MatrixOrder in
lemma g59a_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) :
    ∑ a, ∑ b, ‖ρ b a‖ ≤ Fintype.card ι := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.1.nonneg
  set r : ι → ℝ := fun a => ∑ k, ‖B k a‖ ^ 2 with hr
  have hent : ∀ b a, ‖ρ b a‖ ≤ (r b + r a) / 2 := by
    intro b a
    rw [hB, Matrix.star_eq_conjTranspose, Matrix.mul_apply]
    calc ‖∑ k, Bᴴ b k * B k a‖ ≤ ∑ k, ‖Bᴴ b k * B k a‖ := norm_sum_le _ _
      _ ≤ ∑ k, (‖B k b‖ ^ 2 + ‖B k a‖ ^ 2) / 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, Matrix.conjTranspose_apply, norm_star]
          nlinarith [sq_nonneg (‖B k b‖ - ‖B k a‖)]
      _ = (r b + r a) / 2 := by rw [hr, ← Finset.sum_div, Finset.sum_add_distrib]
  have htr : ∑ a, r a = 1 := by
    have h1 := congrArg Complex.re hρ.2
    rw [hB, Matrix.trace, Matrix.star_eq_conjTranspose] at h1
    simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
      RCLike.star_def, Complex.conj_mul'] at h1
    simpa [hr, ← Complex.ofReal_pow] using h1
  calc ∑ a, ∑ b, ‖ρ b a‖ ≤ ∑ a, ∑ b, (r b + r a) / 2 :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hent b a
    _ = Fintype.card ι := by
        simp only [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, htr, ← Finset.mul_sum]
        ring

lemma g59a_sp_le (p : Fin 4) (a b : Bool) : ‖singlePauli p a b‖ ≤ 1 := by
  fin_cases p <;> cases a <;> cases b <;> simp [singlePauli, pauliX, pauliY, pauliZ]

lemma g59a_xb {I : Type*} [Fintype I] [DecidableEq I] (P : I → Fin 4)
    (ρ : Matrix (I → Bool) (I → Bool) ℂ) (hρ : IsDensityMatrix ρ) :
    |effectProb (wordMatrix P) ρ| ≤ Fintype.card (I → Bool) := by
  unfold effectProb
  calc |(wordMatrix P * ρ).trace.re| ≤ ‖(wordMatrix P * ρ).trace‖ := Complex.abs_re_le_norm _
    _ = ‖∑ a, ∑ b, wordMatrix P a b * ρ b a‖ := by simp [Matrix.trace, Matrix.mul_apply]
    _ ≤ ∑ a, ∑ b, ‖ρ b a‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_mul]
        have : ‖wordMatrix P a b‖ ≤ 1 := by
          rw [show wordMatrix P a b = ∏ i, singlePauli (P i) (a i) (b i) from rfl, norm_prod]
          exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => g59a_sp_le _ _ _
        nlinarith [norm_nonneg (ρ b a), norm_nonneg (wordMatrix P a b)]
    _ ≤ _ := g59a_entry ρ hρ

lemma g59a_int {I : Type*} [Fintype I] [DecidableEq I] (D : Measure (Matrix (I → Bool) (I → Bool) ℂ))
    (hD : IsStateLaw D) (P Q : I → Fin 4) :
    Integrable (fun ρ => effectProb (wordMatrix P) ρ * effectProb (wordMatrix Q) ρ) D := by
  have := hD.1
  refine Integrable.of_bound ((g59a_xcont _).mul (g59a_xcont _)).measurable.aestronglyMeasurable
    ((Fintype.card (I → Bool) : ℝ) * Fintype.card (I → Bool)) ?_
  filter_upwards [hD.2] with ρ hρ0
  have hρ : IsDensityMatrix ρ := by convert hρ0
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul (g59a_xb P ρ hρ) (g59a_xb Q ρ hρ) (abs_nonneg _) (by positivity)

lemma g59a_card {I : Type*} [Fintype I] [DecidableEq I] (S : Finset I) :
    (Finset.univ.filter fun Q : I → Fin 4 => wordSupport Q = S).card = 3 ^ S.card := by
  have : (Finset.univ.filter fun Q : I → Fin 4 => wordSupport Q = S) =
      Fintype.piFinset (fun i => if i ∈ S then Finset.univ.erase (0 : Fin 4) else {0}) := by
    ext Q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro rfl i
      by_cases h : Q i = 0 <;> simp [wordSupport, h]
    · intro h
      ext i
      have hi := h i
      by_cases hS : i ∈ S
      · simp only [hS, if_true, Finset.mem_erase] at hi; simp [wordSupport, hS, hi.1]
      · simp only [hS, if_false, Finset.mem_singleton] at hi; simp [wordSupport, hS, hi]
  rw [this, Fintype.card_piFinset]
  have hc : ∀ i, (if i ∈ S then Finset.univ.erase (0 : Fin 4) else {0}).card =
      if i ∈ S then 3 else 1 := by intro i; split_ifs <;> simp
  simp only [hc]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

lemma g59a_mw {I : Type*} [Fintype I] [DecidableEq I] (D : Measure (Matrix (I → Bool) (I → Bool) ℂ))
    (hD : IsStateLaw D) (hflat : IsLocallyFlat D) (P : I → Fin 4) :
    momentWeight D P = g59a_psi D P := by
  unfold momentWeight subsystemPurity pauliWeight
  rw [integral_div, integral_finsetSum _ (fun Q _ => by simpa only [sq] using g59a_int D hD Q Q)]
  have : ∀ Q ∈ Finset.univ.filter (fun Q : I → Fin 4 => wordSupport Q = wordSupport P),
      ∫ ρ, effectProb (wordMatrix Q) ρ ^ 2 ∂D = g59a_psi D P := by
    intro Q hQ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hQ
    simp only [sq]
    change g59a_psi D Q = g59a_psi D P
    rw [g59a_canon D hflat Q, g59a_canon D hflat P]
    congr 1; funext i
    have := congrArg (i ∈ ·) hQ
    simp only [wordSupport, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
    simp only [g59a_Zc]
    by_cases h : P i = 0
    · simp [h, not_not.mp (mt this.mp (by simp [h]))]
    · simp [h, this.mpr h]
  rw [Finset.sum_congr rfl this, Finset.sum_const, g59a_card, nsmul_eq_mul]
  push_cast
  rw [div_pow]
  field_simp
lemma g59a_pauli_compl (a b a' b' : Bool) :
    ∑ p : Fin 4, singlePauli p a b * conj (singlePauli p a' b') =
      if a = a' ∧ b = b' then 2 else 0 := by
  rw [Fin.sum_univ_four]
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp [singlePauli, pauliX, pauliY, pauliZ] <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

lemma g59a_pauli_herm (p : Fin 4) (a b : Bool) : star (singlePauli p a b) = singlePauli p b a := by
  fin_cases p <;> cases a <;> cases b <;> simp [singlePauli, pauliX, pauliY, pauliZ]

lemma g59a_word_apply {I : Type*} [Fintype I] [DecidableEq I] (P : I → Fin 4) (y x : I → Bool) :
    wordMatrix P y x = ∏ i, singlePauli (P i) (y i) (x i) := rfl

lemma g59a_word_compl {I : Type*} [Fintype I] [DecidableEq I] (y x y' x' : I → Bool) :
    ∑ P : I → Fin 4, wordMatrix P y x * conj (wordMatrix P y' x') =
      if y = y' ∧ x = x' then (2 : ℂ) ^ Fintype.card I else 0 := by
  simp only [g59a_word_apply, map_prod]
  simp only [← Finset.prod_mul_distrib]
  have : ∏ i, ∑ p : Fin 4, singlePauli p (y i) (x i) * conj (singlePauli p (y' i) (x' i)) =
      ∑ P : I → Fin 4, ∏ i, singlePauli (P i) (y i) (x i) * conj (singlePauli (P i) (y' i) (x' i)) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [← this]
  simp only [g59a_pauli_compl]
  by_cases h : y = y' ∧ x = x'
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [if_neg h]
    have : ∃ i, ¬ (y i = y' i ∧ x i = x' i) := by
      by_contra hc; push Not at hc
      exact h ⟨funext fun i => (hc i).1, funext fun i => (hc i).2⟩
    obtain ⟨i, hi⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma g59a_word_herm {I : Type*} [Fintype I] [DecidableEq I] (P : I → Fin 4) : (wordMatrix P)ᴴ = wordMatrix P := by
  ext x y
  rw [Matrix.conjTranspose_apply, g59a_word_apply, g59a_word_apply]
  rw [show star (∏ i, singlePauli (P i) (y i) (x i)) = starRingEnd ℂ (∏ i, singlePauli (P i) (y i) (x i))
    from rfl, map_prod]
  exact Finset.prod_congr rfl fun i _ => g59a_pauli_herm _ _ _
lemma g59a_coef_eq {I : Type*} [Fintype I] [DecidableEq I] (H : Matrix ((I → Bool)) ((I → Bool)) ℂ) (hH : H.IsHermitian)
    (P : I → Fin 4) :
    ((coefficient H P : ℝ) : ℂ) = (wordMatrix P * H).trace / 2 ^ Fintype.card I := by
  have hreal : ((wordMatrix P * H).trace.re : ℂ) = (wordMatrix P * H).trace := by
    have : star (wordMatrix P * H).trace = (wordMatrix P * H).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hH.eq, g59a_word_herm,
        Matrix.trace_mul_comm]
    exact Complex.conj_eq_iff_re.mp this
  rw [← hreal]
  unfold coefficient
  push_cast
  congr
  all_goals exact Subsingleton.elim _ _

lemma g59a_expand {I : Type*} [Fintype I] [DecidableEq I] (H : Matrix ((I → Bool)) ((I → Bool)) ℂ) (hH : H.IsHermitian) :
    H = ∑ P : I → Fin 4, ((coefficient H P : ℝ) : ℂ) • wordMatrix P := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, g59a_coef_eq H hH]
  have hW : ∀ P : I → Fin 4, wordMatrix P a b = conj (wordMatrix P b a) := by
    intro P
    have := congrFun (congrFun (g59a_word_herm P) a) b
    rw [Matrix.conjTranspose_apply] at this
    rw [← this]; rfl
  simp only [hW, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ y : (I → Bool), ∑ P : I → Fin 4, ∑ x, wordMatrix P y x * H x y / 2 ^ Fintype.card I *
      conj (wordMatrix P b a) = ∑ x, H x y / 2 ^ Fintype.card I * (∑ P : I → Fin 4,
        wordMatrix P y x * conj (wordMatrix P b a)) := by
    intro y
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun P _ => by ring
  simp only [this, g59a_word_compl]
  rw [Finset.sum_eq_single b, Finset.sum_eq_single a]
  · simp
  · intro x _ hx; simp [hx]
  · simp
  · intro y _ hy; simp [hy]
  · simp

lemma g59a_eP {I : Type*} [Fintype I] [DecidableEq I] (O : Matrix (I → Bool) (I → Bool) ℂ)
    (hO : O.IsHermitian) (ρ : Matrix (I → Bool) (I → Bool) ℂ) :
    effectProb O ρ = ∑ P : I → Fin 4, coefficient O P * effectProb (wordMatrix P) ρ := by
  conv_lhs => rw [g59a_expand O hO]
  unfold effectProb
  rw [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

lemma g59a_qint {I : Type*} [Fintype I] [DecidableEq I] (D : Measure (Matrix (I → Bool) (I → Bool) ℂ))
    (hD : IsStateLaw D) (c d : (I → Fin 4) → ℝ) :
    Integrable (fun ρ => (∑ P, c P * effectProb (wordMatrix P) ρ) *
      (∑ Q, d Q * effectProb (wordMatrix Q) ρ)) D := by
  simp only [Finset.sum_mul_sum]
  refine integrable_finsetSum _ fun P _ => integrable_finsetSum _ fun Q _ => ?_
  exact ((g59a_int D hD P Q).const_mul (c P * d Q)).congr
    (Filter.Eventually.of_forall fun ρ => by ring)

lemma g59a_quad {I : Type*} [Fintype I] [DecidableEq I] (D : Measure (Matrix (I → Bool) (I → Bool) ℂ))
    (hD : IsStateLaw D) (hflat : IsLocallyFlat D) (c d : (I → Fin 4) → ℝ) :
    ∫ ρ, (∑ P, c P * effectProb (wordMatrix P) ρ) * (∑ Q, d Q * effectProb (wordMatrix Q) ρ) ∂D =
      ∑ P, c P * d P * momentWeight D P := by
  simp only [Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun P _ => integrable_finsetSum _ fun Q _ =>
    ((g59a_int D hD P Q).const_mul (c P * d Q)).congr
      (Filter.Eventually.of_forall fun ρ => by ring)]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [integral_finsetSum _ fun Q _ => ((g59a_int D hD P Q).const_mul (c P * d Q)).congr
      (Filter.Eventually.of_forall fun ρ => by ring)]
  have : ∀ Q, ∫ ρ, c P * effectProb (wordMatrix P) ρ * (d Q * effectProb (wordMatrix Q) ρ) ∂D =
      c P * d Q * ∫ ρ, effectProb (wordMatrix P) ρ * effectProb (wordMatrix Q) ρ ∂D := by
    intro Q; rw [← integral_const_mul]; congr 1; funext ρ; ring
  simp only [this]
  rw [Finset.sum_eq_single P (fun Q _ hQ => by rw [g59a_off D hflat P Q (Ne.symm hQ), mul_zero])
    (by simp), g59a_mw D hD hflat]
  rfl

open scoped ComplexOrder

lemma g59a_psd_cs {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (hM : M.PosSemidef)
    (a b : ι) : ‖M a b‖ ^ 2 ≤ (M a a).re * (M b b).re := by
  have h := (hM.submatrix ![a, b]).det_nonneg
  rw [Matrix.det_fin_two] at h
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have hba : M b a = star (M a b) := (hM.1.apply b a).symm
  have haa : (M a a).im = 0 := by
    have := hM.1.apply a a; exact Complex.conj_eq_iff_im.mp this
  have hbb : (M b b).im = 0 := by
    have := hM.1.apply b b; exact Complex.conj_eq_iff_im.mp this
  have h2 := (Complex.nonneg_iff.mp h).1
  rw [hba] at h2
  simp only [Complex.sub_re, Complex.mul_re, haa, hbb, mul_zero, sub_zero, Complex.zero_re] at h2
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at h2
  linarith

def g59a_join {I : Type*} (S : Finset I) (u v : I → Bool) : I → Bool := fun i => if i ∈ S then u i else v i

lemma g59a_wire_swap (p q : Fin 4) (a b c d : Bool) :
    True := trivial

lemma g59a_swap1 (a b c d : Bool) :
    ∑ p : Fin 4, singlePauli p a b * singlePauli p c d = if a = d ∧ b = c then 2 else 0 := by
  rw [Fin.sum_univ_four]
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [singlePauli, pauliX, pauliY, pauliZ] <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

lemma g59a_swap {I : Type*} [Fintype I] [DecidableEq I] (S : Finset I) (x y x' y' : I → Bool) :
    ∑ Q ∈ Fintype.piFinset (fun i => if i ∈ S then (Finset.univ : Finset (Fin 4)) else {0}),
      wordMatrix Q x y * wordMatrix Q x' y' =
      if y' = g59a_join S x x' ∧ y = g59a_join S x' x then (2 : ℂ) ^ S.card else 0 := by
  simp only [g59a_word_apply, ← Finset.prod_mul_distrib]
  rw [← Finset.prod_univ_sum (t := fun i => if i ∈ S then (Finset.univ : Finset (Fin 4)) else {0})
    (f := fun i p => singlePauli p (x i) (y i) * singlePauli p (x' i) (y' i))]
  have hw : ∀ i, ∑ p ∈ (if i ∈ S then (Finset.univ : Finset (Fin 4)) else {0}),
      singlePauli p (x i) (y i) * singlePauli p (x' i) (y' i) =
      (if i ∈ S then (2 : ℂ) else 1) *
        (if y' i = g59a_join S x x' i ∧ y i = g59a_join S x' x i then 1 else 0) := by
    intro i
    by_cases hi : i ∈ S
    · simp only [hi, if_true, g59a_swap1, g59a_join]
      by_cases h1 : x i = y' i <;> by_cases h2 : y i = x' i <;> simp [h1, h2, eq_comm]
    · simp only [hi, if_false, Finset.sum_singleton, g59a_join]
      simp only [singlePauli, if_true, Matrix.one_apply]
      by_cases h1 : x i = y i <;> by_cases h2 : x' i = y' i <;> simp [h1, h2, eq_comm]
  simp only [hw, Finset.prod_mul_distrib]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  by_cases h : y' = g59a_join S x x' ∧ y = g59a_join S x' x
  · rw [if_pos h, Finset.prod_eq_one (fun i _ => if_pos ⟨by rw [h.1], by rw [h.2]⟩), mul_one]
  · rw [if_neg h]
    have : ∃ i, ¬ (y' i = g59a_join S x x' i ∧ y i = g59a_join S x' x i) := by
      by_contra hc; push Not at hc
      exact h ⟨funext fun i => (hc i).1, funext fun i => (hc i).2⟩
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), mul_zero]

open scoped MatrixOrder in
lemma g59a_partial {I : Type*} [Fintype I] [DecidableEq I] (S : Finset I)
    (ρ : Matrix (I → Bool) (I → Bool) ℂ) (hρ : IsDensityMatrix ρ) :
    ∃ r : ℝ, r ≤ 1 ∧ ∑ x, ∑ x', ρ (g59a_join S x' x) x * ρ (g59a_join S x x') x' = (r : ℂ) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => Bool)
  let ρ' := ρ.submatrix e.symm e.symm
  have hρ' : ρ'.PosSemidef := hρ.1.submatrix _
  let M : Matrix ({i // i ∈ S} → Bool) ({i // i ∈ S} → Bool) ℂ :=
    fun u v => ∑ c : {i // i ∉ S} → Bool, ρ' (u, c) (v, c)
  have hM : M.PosSemidef := by
    have : M = ∑ c : {i // i ∉ S} → Bool, ρ'.submatrix (fun u => (u, c)) (fun u => (u, c)) := by
      ext u v; simp [M, Matrix.sum_apply]
    rw [this]; exact Matrix.posSemidef_sum _ fun c _ => hρ'.submatrix _
  have hj : ∀ a c b d, g59a_join S (e.symm (b, d)) (e.symm (a, c)) = e.symm (b, c) := by
    intro a c b d; funext i; by_cases hi : i ∈ S <;> simp [g59a_join, e, hi]
  have hsum : ∑ x, ∑ x', ρ (g59a_join S x' x) x * ρ (g59a_join S x x') x' =
      ∑ a, ∑ b, M b a * M a b := by
    rw [← (Equiv.sum_comp e.symm _)]
    simp only [← (Equiv.sum_comp e.symm _)]
    simp only [Fintype.sum_prod_type, hj]
    simp only [M, ρ', Matrix.submatrix_apply, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  have hreal : ∀ a b, M b a * M a b = ((‖M a b‖ ^ 2 : ℝ) : ℂ) := by
    intro a b
    rw [← (hM.1.apply b a), Complex.star_def, mul_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  refine ⟨(∑ a, ∑ b, ‖M a b‖ ^ 2 : ℝ), ?_, by rw [hsum]; push_cast; simp only [hreal]; push_cast; rfl⟩
  have htr : ∑ a, (M a a).re = 1 := by
    have h1 := congrArg Complex.re hρ.2
    have ht : ∑ p, ρ (e.symm p) (e.symm p) = ρ.trace := Equiv.sum_comp e.symm (fun x => ρ x x)
    rw [← ht, Fintype.sum_prod_type] at h1
    simpa [M, ρ', Complex.re_sum] using h1
  calc ∑ a, ∑ b, ‖M a b‖ ^ 2 ≤ ∑ a, ∑ b, (M a a).re * (M b b).re :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => g59a_psd_cs M hM a b
    _ = (∑ a, (M a a).re) * (∑ b, (M b b).re) := by rw [Finset.sum_mul_sum]
    _ = 1 := by rw [htr, one_mul]

lemma g59a_tr_real {I : Type*} [Fintype I] [DecidableEq I] (P : I → Fin 4)
    (ρ : Matrix (I → Bool) (I → Bool) ℂ) (hρ : ρ.IsHermitian) :
    (wordMatrix P * ρ).trace = ((effectProb (wordMatrix P) ρ : ℝ) : ℂ) := by
  unfold effectProb
  have : star (wordMatrix P * ρ).trace = (wordMatrix P * ρ).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hρ.eq, g59a_word_herm,
      Matrix.trace_mul_comm]
  exact (Complex.conj_eq_iff_re.mp this).symm

lemma g59a_purity {I : Type*} [Fintype I] [DecidableEq I] (ρ : Matrix (I → Bool) (I → Bool) ℂ)
    (hρ : IsDensityMatrix ρ) (S : Finset I) :
    ∑ Q ∈ Finset.univ.filter (fun Q : I → Fin 4 => wordSupport Q = S),
      effectProb (wordMatrix Q) ρ ^ 2 ≤ 2 ^ S.card := by
  set T := Fintype.piFinset (fun i => if i ∈ S then (Finset.univ : Finset (Fin 4)) else {0}) with hT
  have hsub : Finset.univ.filter (fun Q : I → Fin 4 => wordSupport Q = S) ⊆ T := by
    intro Q hQ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hQ
    rw [hT, Fintype.mem_piFinset]
    intro i
    by_cases hi : i ∈ S
    · simp [hi]
    · rw [if_neg hi, Finset.mem_singleton]
      have : i ∉ wordSupport Q := hQ ▸ hi
      simpa [wordSupport] using this
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _) ?_
  obtain ⟨r, hr1, hr⟩ := g59a_partial S ρ hρ
  have key : ((∑ Q ∈ T, effectProb (wordMatrix Q) ρ ^ 2 : ℝ) : ℂ) = (2 : ℂ) ^ S.card * (r : ℂ) := by
    push_cast
    simp only [sq, ← g59a_tr_real _ ρ hρ.1.1]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul_sum]
    have e1 : ∑ Q ∈ T, ∑ x, ∑ x', ∑ y, ∑ y', wordMatrix Q x y * ρ y x * (wordMatrix Q x' y' * ρ y' x') =
        ∑ x, ∑ x', ∑ y, ∑ y', (∑ Q ∈ T, wordMatrix Q x y * wordMatrix Q x' y') * (ρ y x * ρ y' x') := by
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun x' _ => ?_
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun y' _ => ?_
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun Q _ => by ring
    rw [e1, hT]
    simp only [g59a_swap]
    have e2 : ∀ x x' : I → Bool, ∑ y, ∑ y', (if y' = g59a_join S x x' ∧ y = g59a_join S x' x then
        (2 : ℂ) ^ S.card else 0) * (ρ y x * ρ y' x') =
        2 ^ S.card * (ρ (g59a_join S x' x) x * ρ (g59a_join S x x') x') := by
      intro x x'
      rw [Finset.sum_eq_single (g59a_join S x' x), Finset.sum_eq_single (g59a_join S x x')]
      · simp
      · intro y' _ hy'; simp [hy']
      · simp
      · intro y _ hy; refine Finset.sum_eq_zero fun y' _ => ?_; simp [hy]
      · simp
    simp only [e2, ← Finset.mul_sum, hr]
  have key' : (∑ Q ∈ T, effectProb (wordMatrix Q) ρ ^ 2 : ℝ) = 2 ^ S.card * r := by
    exact_mod_cast key
  rw [key']
  have : (0 : ℝ) < 2 ^ S.card := by positivity
  nlinarith

section g59aprop1
open scoped ComplexOrder Matrix.Norms.L2Operator

lemma g58a_pauli_compl (a b a' b' : Bool) :
    ∑ p : Fin 4, singlePauli p a b * conj (singlePauli p a' b') =
      if a = a' ∧ b = b' then 2 else 0 := by
  rw [Fin.sum_univ_four]
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp [singlePauli, pauliX, pauliY, pauliZ] <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

lemma g58a_pauli_herm (p : Fin 4) (a b : Bool) : star (singlePauli p a b) = singlePauli p b a := by
  fin_cases p <;> cases a <;> cases b <;> simp [singlePauli, pauliX, pauliY, pauliZ]

lemma g58a_word_apply {n : ℕ} (P : Fin n → Fin 4) (y x : Fin n → Bool) :
    wordMatrix P y x = ∏ i, singlePauli (P i) (y i) (x i) := rfl

lemma g58a_word_compl {n : ℕ} (y x y' x' : Fin n → Bool) :
    ∑ P : Fin n → Fin 4, wordMatrix P y x * conj (wordMatrix P y' x') =
      if y = y' ∧ x = x' then (2 : ℂ) ^ n else 0 := by
  simp only [g58a_word_apply, map_prod]
  simp only [← Finset.prod_mul_distrib]
  have : ∏ i, ∑ p : Fin 4, singlePauli p (y i) (x i) * conj (singlePauli p (y' i) (x' i)) =
      ∑ P : Fin n → Fin 4, ∏ i, singlePauli (P i) (y i) (x i) * conj (singlePauli (P i) (y' i) (x' i)) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [← this]
  simp only [g58a_pauli_compl]
  by_cases h : y = y' ∧ x = x'
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [if_neg h]
    have : ∃ i, ¬ (y i = y' i ∧ x i = x' i) := by
      by_contra hc; push Not at hc
      exact h ⟨funext fun i => (hc i).1, funext fun i => (hc i).2⟩
    obtain ⟨i, hi⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma g58a_word_herm {n : ℕ} (P : Fin n → Fin 4) : (wordMatrix P)ᴴ = wordMatrix P := by
  ext x y
  rw [Matrix.conjTranspose_apply, g58a_word_apply, g58a_word_apply]
  rw [show star (∏ i, singlePauli (P i) (y i) (x i)) = starRingEnd ℂ (∏ i, singlePauli (P i) (y i) (x i))
    from rfl, map_prod]
  exact Finset.prod_congr rfl fun i _ => g58a_pauli_herm _ _ _

lemma g58a_tr {n : ℕ} (P : Fin n → Fin 4) (H : Matrix (Qubits n) (Qubits n) ℂ) :
    (wordMatrix P * H).trace = ∑ z : Qubits n × Qubits n, wordMatrix P z.1 z.2 * H z.2 z.1 := by
  rw [Fintype.sum_prod_type]; rfl

lemma g58a_parseval {n : ℕ} (H : Matrix (Qubits n) (Qubits n) ℂ) (hH : H.IsHermitian) :
    ∑ P : Fin n → Fin 4, coefficient H P ^ 2 =
      (∑ z : Qubits n × Qubits n, ‖H z.2 z.1‖ ^ 2) / (2 : ℝ) ^ n := by
  have hreal : ∀ P, ((wordMatrix P * H).trace.re : ℂ) = (wordMatrix P * H).trace := by
    intro P
    have : star (wordMatrix P * H).trace = (wordMatrix P * H).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hH.eq, g58a_word_herm,
        Matrix.trace_mul_comm]
    exact Complex.conj_eq_iff_re.mp this
  have hsq : ∀ P, coefficient H P ^ 2 =
      ((wordMatrix P * H).trace * conj (wordMatrix P * H).trace).re / ((2 : ℝ) ^ n) ^ 2 := by
    intro P
    unfold coefficient
    rw [Fintype.card_fin, div_pow, ← hreal P, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    ring_nf
    rw [mul_comm]
    congr
    all_goals exact Subsingleton.elim _ _
  simp only [hsq, ← Finset.sum_div, ← Complex.re_sum]
  have key : ∑ P : Fin n → Fin 4, (wordMatrix P * H).trace * conj (wordMatrix P * H).trace =
      (2 : ℂ) ^ n * ∑ z : Qubits n × Qubits n, H z.2 z.1 * conj (H z.2 z.1) := by
    simp only [g58a_tr, map_sum, map_mul, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    have : ∀ z z' : Qubits n × Qubits n, ∑ P : Fin n → Fin 4,
        wordMatrix P z.1 z.2 * H z.2 z.1 * (conj (wordMatrix P z'.1 z'.2) * conj (H z'.2 z'.1)) =
        (if z = z' then (2 : ℂ) ^ n else 0) * (H z.2 z.1 * conj (H z'.2 z'.1)) := by
      intro z z'
      have := g58a_word_compl z.1 z.2 z'.1 z'.2
      have h' : (if z.1 = z'.1 ∧ z.2 = z'.2 then (2:ℂ)^n else 0) = if z = z' then 2^n else 0 := by
        simp [Prod.ext_iff]
      rw [h'] at this
      rw [← this, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [Finset.sum_comm (γ := Fin n → Fin 4), this, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
  rw [key]
  have hn : ∀ z : Qubits n × Qubits n, H z.2 z.1 * conj (H z.2 z.1) = ((‖H z.2 z.1‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [hn, ← Complex.ofReal_sum, ← Complex.ofReal_pow, ← Complex.ofReal_ofNat,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  field_simp

lemma g58a_col {n : ℕ} (H : Matrix (Qubits n) (Qubits n) ℂ) (y : Qubits n) :
    ∑ x, ‖H x y‖ ^ 2 ≤ specNorm H ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec H (EuclideanSpace.single y 1)
  rw [EuclideanSpace.norm_single, norm_one, mul_one] at h
  have h0 : 0 ≤ ‖(EuclideanSpace.equiv (Qubits n) ℂ).symm (H *ᵥ (EuclideanSpace.single y (1 : ℂ)))‖ :=
    norm_nonneg _
  have h2 := pow_le_pow_left₀ h0 h 2
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h2
  have e : ∀ x, ((EuclideanSpace.equiv (Qubits n) ℂ).symm
      (H *ᵥ (EuclideanSpace.single y (1 : ℂ)))).ofLp x = H x y := by
    intro x; simp [Matrix.mulVec, dotProduct]
  simp only [e] at h2
  exact h2

theorem g59a_prop1 (n : ℕ) (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) :
    frobNorm H / Real.sqrt ((2 : ℝ) ^ n) = pauliNorm 2 H ∧
      pauliNorm 2 H ≤ specNorm H := by
  set F := ∑ z : Qubits n × Qubits n, ‖H z.2 z.1‖ ^ 2 with hF
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfrob : frobNorm H = Real.sqrt F := by
    unfold frobNorm
    rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
    congr 1
    rw [hF, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Real.rpow_two]
  have hpauli : pauliNorm 2 H = Real.sqrt (F / 2 ^ n) := by
    unfold pauliNorm
    rw [Real.sqrt_eq_rpow, ← g58a_parseval H hH]
    congr 1
    refine Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun P _ => ?_
    rw [Real.rpow_eq_pow, Real.rpow_two, sq_abs]
  refine ⟨?_, ?_⟩
  · rw [hfrob, hpauli, Real.sqrt_div' _ (by positivity)]
  · rw [hpauli]
    have hs : 0 ≤ specNorm H := norm_nonneg _
    rw [← Real.sqrt_sq hs]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    have : F ≤ ∑ y : Qubits n, specNorm H ^ 2 := by
      rw [hF, Fintype.sum_prod_type]
      exact Finset.sum_le_sum fun y _ => g58a_col H y
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    simp only [Qubits, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
    push_cast at this
    linarith

end g59aprop1
lemma g59a_nwt_trace {I : Type*} [Fintype I] [DecidableEq I] (A : I → Matrix Bool Bool ℂ) :
    (namedWireTensor A).trace = ∏ i, (A i).trace := by
  simp only [Matrix.trace, Matrix.diag, namedWireTensor]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma g59a_pp (a b : Fin 4) : (singlePauli a * singlePauli b).trace = if a = b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [singlePauli, pauliX, pauliY, pauliZ, Matrix.trace, Fintype.sum_bool, Matrix.mul_apply] <;>
    norm_num [Complex.I_sq]

lemma g59a_orth {I : Type*} [Fintype I] [DecidableEq I] (A B : I → Fin 4) (h : A ≠ B) :
    (wordMatrix A * wordMatrix B).trace = 0 := by
  unfold wordMatrix
  rw [g59a_nwt_mul, g59a_nwt_trace]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [g59a_pp, if_neg hj])

lemma g59a_trWW {I : Type*} [Fintype I] [DecidableEq I] (P Q : I → Fin 4) :
    (wordMatrix P * wordMatrix Q).trace = if P = Q then (2 : ℂ) ^ Fintype.card I else 0 := by
  by_cases h : P = Q
  · subst h; rw [if_pos rfl]; unfold wordMatrix
    rw [g59a_nwt_mul, g59a_nwt_trace]; simp [g59a_pp]
  · rw [if_neg h, g59a_orth P Q h]

lemma g59a_coef_trunc {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ)
    (O : Matrix (I → Bool) (I → Bool) ℂ) (P : I → Fin 4) :
    coefficient (truncateStrict k O) P = if pauliWeight P < k then coefficient O P else 0 := by
  unfold truncateStrict
  conv_lhs => unfold coefficient
  simp only [Matrix.mul_sum, Matrix.trace_sum]
  simp only [Matrix.mul_smul, Matrix.trace_smul, g59a_trWW, smul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs
  · rw [show (2 : ℂ) ^ Fintype.card I = ((2 ^ Fintype.card I : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    unfold coefficient
    field_simp
  · simp

lemma g59a_trunc_herm {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ)
    (O : Matrix (I → Bool) (I → Bool) ℂ) : (truncateStrict k O).IsHermitian := by
  unfold truncateStrict Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Matrix.conjTranspose_smul, g59a_word_herm]
  simp

lemma g59a_mw_le {I : Type*} [Fintype I] [DecidableEq I] (D : Measure (Matrix (I → Bool) (I → Bool) ℂ))
    (hD : IsStateLaw D) (P : I → Fin 4) :
    0 ≤ momentWeight D P ∧ momentWeight D P ≤ (2 / 3 : ℝ) ^ pauliWeight P := by
  have := hD.1
  unfold momentWeight
  have hint : Integrable (fun rho => subsystemPurity rho (wordSupport P)) D := by
    unfold subsystemPurity
    refine Integrable.div_const (integrable_finsetSum _ fun Q _ => ?_) _
    simpa only [sq] using g59a_int D hD Q Q
  have h1 : ∫ rho, subsystemPurity rho (wordSupport P) ∂D ≤ 1 := by
    have : ∫ rho, subsystemPurity rho (wordSupport P) ∂D ≤ ∫ _rho, (1 : ℝ) ∂D := by
      refine integral_mono_ae hint (integrable_const _) ?_
      filter_upwards [hD.2] with ρ hρ0
      have hρ : IsDensityMatrix ρ := by convert hρ0
      unfold subsystemPurity
      rw [div_le_one (by positivity)]
      exact g59a_purity ρ hρ _
    simpa using this
  have h0 : 0 ≤ ∫ rho, subsystemPurity rho (wordSupport P) ∂D :=
    integral_nonneg fun ρ => div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
  exact ⟨mul_nonneg (by positivity) h0, by
    calc _ ≤ (2 / 3 : ℝ) ^ pauliWeight P * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := mul_one _⟩

theorem g59a_cor13 (n k : ℕ) (hk : 0 < k) (O : (Matrix (Qubits n) (Qubits n) ℂ))
    (hO : O.IsHermitian) (D : Measure ((Matrix (Qubits n) (Qubits n) ℂ)))
    (hD : IsStateLaw D) (hflat : IsLocallyFlat D) :
    (∫ rho, |effectProb O rho - effectProb (truncateStrict k O) rho| ^ 2 ∂D) ≤
      (2 / 3 : ℝ) ^ k * specNorm O ^ 2 := by
  set O2 := truncateStrict k O
  have h2 : O2.IsHermitian := g59a_trunc_herm k O
  set c : (Fin n → Fin 4) → ℝ := fun P => coefficient O P - coefficient O2 P with hc
  have hf : ∀ ρ, effectProb O ρ - effectProb O2 ρ = ∑ P, c P * effectProb (wordMatrix P) ρ := by
    intro ρ
    rw [g59a_eP O hO, g59a_eP O2 h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun P _ => ?_
    simp only [hc]; ring
  simp only [hf]; simp only [sq_abs]; simp only [sq]
  rw [g59a_quad D hD hflat c c]
  have hterm : ∀ P, c P * c P * momentWeight D P ≤ (2 / 3 : ℝ) ^ k * coefficient O P ^ 2 := by
    intro P
    have hcP : c P = if pauliWeight P < k then 0 else coefficient O P := by
      simp only [hc, O2, g59a_coef_trunc]; split_ifs <;> ring
    obtain ⟨hm0, hm1⟩ := g59a_mw_le D hD P
    rw [hcP]
    split_ifs with hw
    · simp only [mul_zero, zero_mul]; positivity
    · push Not at hw
      have : momentWeight D P ≤ (2 / 3 : ℝ) ^ k :=
        hm1.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hw)
      nlinarith [sq_nonneg (coefficient O P)]
  have hpar : ∑ P : Fin n → Fin 4, coefficient O P ^ 2 ≤ specNorm O ^ 2 := by
    have h := (g59a_prop1 n O hO).2
    unfold pauliNorm at h
    have h' : (∑ P : Fin n → Fin 4, coefficient O P ^ 2).rpow (1 / 2) ≤ specNorm O := by
      convert h using 3
      · congr; exact Subsingleton.elim _ _
      · show _ = |coefficient O _| ^ (2 : ℝ)
        rw [Real.rpow_two, sq_abs]
    clear h
    have h := h'
    have hs : 0 ≤ ∑ P : Fin n → Fin 4, coefficient O P ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h0 : 0 ≤ Real.rpow (∑ P : Fin n → Fin 4, coefficient O P ^ 2) (1 / 2) :=
      Real.rpow_nonneg hs _
    have hsq : (Real.rpow (∑ P : Fin n → Fin 4, coefficient O P ^ 2) (1 / 2)) ^ 2 =
        ∑ P : Fin n → Fin 4, coefficient O P ^ 2 := by
      rw [show (Real.rpow (∑ P : Fin n → Fin 4, coefficient O P ^ 2) (1 / 2)) =
        Real.sqrt (∑ P : Fin n → Fin 4, coefficient O P ^ 2) by
          rw [Real.sqrt_eq_rpow]; rfl, Real.sq_sqrt hs]
    rw [← hsq]
    exact pow_le_pow_left₀ h0 h 2
  calc ∑ P, c P * c P * momentWeight D P ≤ ∑ P, (2 / 3 : ℝ) ^ k * coefficient O P ^ 2 :=
        Finset.sum_le_sum fun P _ => hterm P
    _ = (2 / 3 : ℝ) ^ k * ∑ P, coefficient O P ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (2 / 3 : ℝ) ^ k * specNorm O ^ 2 := mul_le_mul_of_nonneg_left hpar (by positivity)
    _ = _ := by ring

theorem solution (n k : ℕ) (hk : 0 < k) (O : (Matrix (Qubits n) (Qubits n) ℂ))
    (hO : O.IsHermitian) (D : Measure ((Matrix (Qubits n) (Qubits n) ℂ)))
    (hD : IsStateLaw D) (hflat : IsLocallyFlat D) :
    (∫ rho, |effectProb O rho - effectProb (truncateStrict k O) rho| ^ 2 ∂D) ≤
      (2 / 3 : ℝ) ^ k * specNorm O ^ 2 := g59a_cor13 n k hk O hO D hD hflat
