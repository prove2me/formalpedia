-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P03.observableLabel_preprocessing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:56:29.880612+00:00
-- url     : https://prove2.me/submissions/26e02ed9-83e9-4a4a-b5ca-6a1d9780bf6a

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

universe g59au

lemma g59a_pure_val {A : Type g59au} (x : A) : (pure x : Execution A).value = x := rfl
lemma g59a_pure_steps {A : Type g59au} (x : A) : (pure x : Execution A).steps = 0 := rfl

lemma g59a_bind_val {A B : Type g59au} (a : Execution A) (f : A → Execution B) :
    (a >>= f).value = (f a.value).value := rfl

lemma g59a_bind_steps {A B : Type g59au} (a : Execution A) (f : A → Execution B) :
    (a >>= f).steps = a.steps + (f a.value).steps := rfl

instance g59a_lawful : LawfulMonad Execution := LawfulMonad.mk'
  (id_map := fun x => by cases x; rfl)
  (pure_bind := fun x f => by
    simp only [Pure.pure, Bind.bind, executionBind, executionPure, Nat.zero_add])
  (bind_assoc := fun x f g => by
    simp only [Bind.bind, executionBind, Nat.add_assoc])

lemma g59a_foldlM {A B : Type g59au} (f : B → A → Execution B) (g : B → A → B) (c : A → ℕ)
    (hv : ∀ b a, (f b a).value = g b a) (hs : ∀ b a, (f b a).steps = c a) :
    ∀ (l : List A) (init : B), (l.foldlM f init).value = l.foldl g init ∧
      (l.foldlM f init).steps = (l.map c).sum := by
  intro l
  induction l with
  | nil => intro init; exact ⟨rfl, rfl⟩
  | cons a l ih =>
    intro init
    rw [List.foldlM_cons, g59a_bind_val, g59a_bind_steps, hv, hs, List.foldl_cons, List.map_cons,
      List.sum_cons]
    exact ⟨(ih _).1, by rw [(ih _).2]⟩

lemma g59a_mapM {A B : Type g59au} (f : A → Execution B) :
    ∀ l : List A, (l.mapM f).value = l.map (fun a => (f a).value) ∧
      (l.mapM f).steps = (l.map (fun a => (f a).steps)).sum := by
  intro l
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons a l ih =>
    rw [List.mapM_cons]
    simp only [g59a_bind_val, g59a_bind_steps, g59a_pure_val, g59a_pure_steps, List.map_cons,
      List.sum_cons, ih.1, ih.2]
    simp only [true_and]; ring

def g59a_h {n : ℕ} (s : Shot n) (a : Fin n × Fin 3) : ℝ :=
  3 * (if (s a.1).1 = a.2 then rademacherValue (s a.1).2 else 0)

lemma g59a_moment {n : ℕ} (s : Shot n) (w : SparseWord n) :
    (runRecordMoment true s w).value = w.foldl (fun acc a => acc * g59a_h s a) 1 ∧
      (runRecordMoment true s w).steps = 5 * w.length := by
  have := g59a_foldlM (fun acc a => do
    let z ← runReadWire s a.1
    let same : Execution Bool := ⟨decide (z.1 = a.2), 1⟩
    let matched ← same
    let signed : Execution ℝ := ⟨if matched then rademacherValue z.2 else 0, 1⟩
    let v ← signed
    let v ← runMul (if true = true then 3 else 1) v
    runMul acc v) (fun acc a => acc * g59a_h s a) (fun _ => 5)
    (fun b a => by
      simp only [g59a_bind_val]; simp only [runMul, runReadWire, g59a_h, decide_eq_true_eq]
      by_cases h : (s a.1).1 = a.2 <;> simp [h])
    (fun b a => by
      simp only [g59a_bind_steps, g59a_bind_val]; simp [runMul, runReadWire]) w 1
  refine ⟨this.1, ?_⟩
  rw [show (runRecordMoment true s w).steps = _ from this.2]
  simp [List.sum_replicate]; ring

def g59a_lab {n : ℕ} (s : Shot n) (acc : ℝ) (a : ℝ × SparseWord n) : ℝ :=
  acc + a.1 * (a.2.foldl (fun acc a => acc * g59a_h s a) 1)

lemma g59a_label {n : ℕ} (terms : SparseObservable n) (s : Shot n) :
    (runLabel terms s).value = terms.foldl (g59a_lab s) 0 ∧
      (runLabel terms s).steps = (terms.map (fun a => 5 * a.2.length + 3)).sum := by
  have := g59a_foldlM (fun acc a => do
    let coeff : Execution ℝ := ⟨a.1, 1⟩
    let c ← coeff
    let v ← runRecordMoment true s a.2
    let v ← runMul c v
    runAdd acc v) (g59a_lab s) (fun a => 5 * a.2.length + 3)
    (fun b a => by
      simp only [g59a_bind_val]; simp [runMul, runAdd, g59a_lab, (g59a_moment s a.2).1])
    (fun b a => by
      simp only [g59a_bind_steps, g59a_bind_val]; simp [runMul, runAdd, (g59a_moment s a.2).2]; ring)
    terms 0
  exact this

lemma g59a_labels {n N : ℕ} (terms : SparseObservable n) (data : Fin N → Shot n) :
    (runLabels terms data).value = ((List.finRange N).map (fun l => (runLabel terms (data l)).value)).toArray ∧
      (runLabels terms data).steps = ((List.finRange N).map (fun l => (runLabel terms (data l)).steps)).sum + N := by
  have h := g59a_mapM (fun l => runLabel terms (data l)) (List.finRange N)
  unfold runLabels
  simp only [g59a_bind_val, g59a_bind_steps]
  simp only [g59a_pure_val, g59a_pure_steps, h.1, h.2]
  simp
lemma g59a_nwt_trace {I : Type*} [Fintype I] [DecidableEq I] (A : I → Matrix Bool Bool ℂ) :
    (namedWireTensor A).trace = ∏ i, (A i).trace := by
  simp only [Matrix.trace, Matrix.diag, namedWireTensor]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- per-wire snapshot value -/
def g59a_f (p : Fin 4) (x : Fin 3 × Bool) : ℝ :=
  if p = 0 then 1 else if p.val = x.1.val + 1 then 3 * rademacherValue x.2 else 0

def g59a_g (p : Fin 4) (x : Fin 3 × Bool) : ℝ :=
  if p = 0 then 1 else if p.val = x.1.val + 1 then 9 else 0

def g59a_snap1 (x : Fin 3 × Bool) : Matrix Bool Bool ℂ :=
  (2⁻¹ : ℂ) • (1 + (if (!x.2) then (3 : ℂ) else -3) •
    (if x.1 = 0 then GroundStateLearning.Axis.X
     else if x.1 = 1 then GroundStateLearning.Axis.Y
     else GroundStateLearning.Axis.Z).mat)

lemma g59a_snap_eq {n : ℕ} (s : Shot n) :
    pauliSnapshot s = namedWireTensor (fun i => g59a_snap1 (s i)) := by
  ext x y; rfl

lemma g59a_wire_trace (p : Fin 4) (x : Fin 3 × Bool) :
    (singlePauli p * g59a_snap1 x).trace = (g59a_f p x : ℂ) := by
  obtain ⟨a, b⟩ := x
  fin_cases p <;> fin_cases a <;> cases b <;>
    simp [g59a_f, g59a_snap1, singlePauli, GroundStateLearning.Axis.mat, pauliX, pauliY, pauliZ,
      Matrix.trace, Fintype.sum_bool, Matrix.mul_apply, rademacherValue] <;> ring_nf <;>
    simp [Complex.I_sq] <;> norm_num


lemma g59a_foldl_mul {n : ℕ} (s : Shot n) (w : SparseWord n) (c : ℝ) :
    w.foldl (fun acc a => acc * g59a_h s a) c = c * (w.map (g59a_h s)).prod := by
  induction w generalizing c with
  | nil => simp
  | cons a w ih => rw [List.foldl_cons, ih, List.map_cons, List.prod_cons]; ring

lemma g59a_decode_cons {n : ℕ} (a : Fin n × Fin 3) (w : SparseWord n) (i : Fin n) :
    decodeSparseWord (a :: w) i = if a.1 = i then ⟨a.2.val + 1, by omega⟩ else decodeSparseWord w i := by
  unfold decodeSparseWord
  rw [List.find?_cons]
  by_cases h : a.1 = i <;> simp [h]

lemma g59a_decode_none {n : ℕ} (w : SparseWord n) (i : Fin n) (h : i ∉ w.map Prod.fst) :
    decodeSparseWord w i = 0 := by
  unfold decodeSparseWord
  rw [List.find?_eq_none.mpr]
  intro x hx
  simp only [decide_eq_true_eq]
  intro hxi; exact h (List.mem_map.mpr ⟨x, hx, hxi⟩)

lemma g59a_prod_decode {n : ℕ} (s : Shot n) (w : SparseWord n) (hw : (w.map Prod.fst).Nodup) :
    ∏ i, g59a_f (decodeSparseWord w i) (s i) = (w.map (g59a_h s)).prod := by
  induction w with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [g59a_decode_none [] i (by simp)]; simp [g59a_f]
  | cons a w ih =>
    rw [List.map_cons, List.nodup_cons] at hw
    rw [List.map_cons, List.prod_cons, ← ih hw.2]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a.1),
      ← Finset.mul_prod_erase Finset.univ (fun i => g59a_f (decodeSparseWord w i) (s i))
        (Finset.mem_univ a.1)]
    rw [g59a_decode_none w a.1 hw.1]
    have e : ∏ x ∈ Finset.univ.erase a.1, g59a_f (decodeSparseWord (a :: w) x) (s x) =
        ∏ x ∈ Finset.univ.erase a.1, g59a_f (decodeSparseWord w x) (s x) :=
      Finset.prod_congr rfl fun x hx => by
        rw [g59a_decode_cons, if_neg (Ne.symm (Finset.ne_of_mem_erase hx))]
    rw [e, g59a_decode_cons, if_pos rfl]
    have hf0 : g59a_f 0 (s a.1) = 1 := by simp [g59a_f]
    rw [hf0, one_mul]
    congr 1
    simp only [g59a_f, g59a_h]
    rw [if_neg (by intro h; have := congrArg Fin.val h; simp at this)]
    by_cases h : (s a.1).1 = a.2
    · rw [if_pos (by simp [h]), if_pos h]
    · rw [if_neg (by intro h'; apply h; ext; simp at h'; omega), if_neg h, mul_zero]

lemma g59a_word_snap {n : ℕ} (s : Shot n) (w : SparseWord n) (hw : (w.map Prod.fst).Nodup) :
    effectProb (wordMatrix (decodeSparseWord w)) (pauliSnapshot s) = (w.map (g59a_h s)).prod := by
  unfold effectProb wordMatrix
  rw [g59a_snap_eq, g59a_nwt_mul, g59a_nwt_trace]
  simp only [g59a_wire_trace]
  rw [← Complex.ofReal_prod, Complex.ofReal_re, g59a_prod_decode s w hw]

lemma g59a_ep_list {n : ℕ} (terms : SparseObservable n) (ρ : Matrix (Qubits n) (Qubits n) ℂ) :
    effectProb (decodeObservable terms) ρ =
      (terms.map (fun a => a.1 * effectProb (wordMatrix (decodeSparseWord a.2)) ρ)).sum := by
  induction terms with
  | nil => simp [decodeObservable, effectProb]
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ← ih]
    unfold decodeObservable effectProb
    rw [List.map_cons, List.sum_cons, Matrix.add_mul, Matrix.trace_add, Complex.add_re,
      Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

lemma g59a_label_value {n : ℕ} (kap : ℕ) (terms : SparseObservable n) (hv : ValidDescription kap terms)
    (s : Shot n) :
    (runLabel terms s).value = effectProb (decodeObservable terms) (pauliSnapshot s) := by
  rw [(g59a_label terms s).1, g59a_ep_list]
  have key : ∀ (t : SparseObservable n), (∀ a ∈ t, (a.2.map Prod.fst).Nodup) → ∀ c : ℝ,
      t.foldl (g59a_lab s) c =
        c + (t.map (fun a => a.1 * effectProb (wordMatrix (decodeSparseWord a.2)) (pauliSnapshot s))).sum := by
    intro t ht
    induction t with
    | nil => intro c; simp
    | cons a t ih =>
      intro c
      rw [List.foldl_cons, ih (fun b hb => ht b (List.mem_cons_of_mem _ hb)), List.map_cons,
        List.sum_cons, g59a_lab, g59a_foldl_mul, one_mul,
        g59a_word_snap s a.2 (ht a List.mem_cons_self)]
      ring
  rw [key terms (fun a ha => (hv.2 a ha).2.2) 0, zero_add]

lemma g59a_label_steps {n : ℕ} (kap : ℕ) (terms : SparseObservable n) (hv : ValidDescription kap terms)
    (s : Shot n) : (runLabel terms s).steps ≤ (5 * kap + 3) * terms.length := by
  rw [(g59a_label terms s).2]
  have := List.sum_le_card_nsmul (terms.map (fun a => 5 * a.2.length + 3)) (5 * kap + 3) (by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    have := (hv.2 a ha).2.1; omega)
  rw [List.length_map, smul_eq_mul] at this
  linarith
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


lemma g59a_coef_list {n : ℕ} (t : SparseObservable n) (P : Fin n → Fin 4) :
    coefficient (decodeObservable t) P =
      (t.map (fun b => b.1 * if decodeSparseWord b.2 = P then 1 else 0)).sum := by
  letI : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  induction t with
  | nil => simp [decodeObservable, coefficient]
  | cons b t ih =>
    rw [List.map_cons, List.sum_cons, ← ih]
    unfold decodeObservable coefficient
    rw [List.map_cons, List.sum_cons, Matrix.mul_add, Matrix.trace_add, Complex.add_re, add_div,
      Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, g59a_trWW]
    congr 1
    by_cases h : decodeSparseWord b.2 = P
    · rw [if_pos h.symm, if_pos h]
      rw [show (2 : ℂ) ^ Fintype.card (Fin n) = ((2 ^ Fintype.card (Fin n) : ℝ) : ℂ) by push_cast; rfl,
        Complex.ofReal_re]
      field_simp
    · rw [if_neg (Ne.symm h), if_neg h]; simp

lemma g59a_pick {n : ℕ} (t : SparseObservable n) (ht : (t.map fun a => decodeSparseWord a.2).Nodup)
    (a : ℝ × SparseWord n) (ha : a ∈ t) :
    (t.map (fun b => b.1 * if decodeSparseWord b.2 = decodeSparseWord a.2 then 1 else 0)).sum = a.1 := by
  induction t with
  | nil => simp at ha
  | cons b t ih =>
    rw [List.map_cons, List.nodup_cons] at ht
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp ha with rfl | ha'
    · rw [if_pos rfl, mul_one]
      have : (t.map (fun b => b.1 * if decodeSparseWord b.2 = decodeSparseWord a.2 then 1 else 0)).sum = 0 := by
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
        rw [if_neg, mul_zero]
        intro h; exact ht.1 (List.mem_map.mpr ⟨c, hc, h⟩)
      rw [this, add_zero]
    · rw [ih ht.2 ha', if_neg, mul_zero, zero_add]
      intro h; exact ht.1 (h ▸ List.mem_map.mpr ⟨a, ha', rfl⟩)

lemma g59a_coef_fsum {n m : ℕ} (T : Fin m → Matrix (Qubits n) (Qubits n) ℂ) (P : Fin n → Fin 4) :
    coefficient (∑ j, T j) P = ∑ j, coefficient (T j) P := by
  letI : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  unfold coefficient
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Finset.sum_div]

lemma g59a_cardU {n : ℕ} (S : Finset (Fin n)) :
    (Finset.univ.filter fun P : Fin n → Fin 4 => wordSupport P ⊆ S).card = 4 ^ S.card := by
  have : (Finset.univ.filter fun P : Fin n → Fin 4 => wordSupport P ⊆ S) =
      Fintype.piFinset (fun i => if i ∈ S then (Finset.univ : Finset (Fin 4)) else {0}) := by
    ext Q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hS : i ∈ S
      · simp [hS]
      · rw [if_neg hS, Finset.mem_singleton]
        by_contra hq
        exact hS (h (by simp [wordSupport, hq]))
    · intro h i hi
      simp only [wordSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_contra hS
      have := h i; rw [if_neg hS, Finset.mem_singleton] at this; exact hi this
  rw [this, Fintype.card_piFinset]
  have hc : ∀ i, (if i ∈ S then (Finset.univ : Finset (Fin 4)) else {0}).card =
      if i ∈ S then 4 else 1 := by intro i; split_ifs <;> simp
  simp only [hc]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

lemma g59a_len {n : ℕ} (hn : 1 ≤ n) (kap d : ℕ) (terms : SparseObservable n)
    (hv : ValidDescription kap terms) (hdeg : HasBoundedDegree kap d (decodeObservable terms)) :
    terms.length ≤ (1 + d * 4 ^ kap) * n := by
  set H := decodeObservable terms
  set Z := Finset.univ.filter fun P : Fin n → Fin 4 => coefficient H P ≠ 0 with hZ
  have h1 : terms.length ≤ Z.card := by
    have hl : terms.length = (terms.map fun a => decodeSparseWord a.2).toFinset.card := by
      rw [List.toFinset_card_of_nodup hv.1, List.length_map]
    rw [hl]
    refine Finset.card_le_card fun P hP => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hP)
    simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and, H]
    rw [g59a_coef_list, g59a_pick terms hv.1 a ha]
    exact (hv.2 a ha).1
  obtain ⟨m, S, T, hsum, hT, hdeg'⟩ := hdeg
  set J := Finset.univ.filter fun j : Fin m => (S j).Nonempty
  have hZsub : Z ⊆ {fun _ => 0} ∪ J.biUnion (fun j =>
      Finset.univ.filter fun P : Fin n → Fin 4 => wordSupport P ⊆ S j) := by
    intro P hP
    simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and] at hP
    rw [show H = ∑ j, T j from hsum, g59a_coef_fsum] at hP
    obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP
    have hsub : wordSupport P ⊆ S j := by
      by_contra h; exact hj ((hT j).2.2 P h)
    rw [Finset.mem_union]
    by_cases hne : (S j).Nonempty
    · right
      exact Finset.mem_biUnion.mpr ⟨j, by simp [J, hne], by simp [hsub]⟩
    · left
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.subset_empty] at hsub
      rw [Finset.mem_singleton]; funext i
      by_contra hi
      have : i ∈ wordSupport P := by simp [wordSupport, hi]
      rw [hsub] at this; simp at this
  have hJ : J.card ≤ n * d := by
    have : J ⊆ Finset.univ.biUnion (fun i : Fin n => Finset.univ.filter fun j => i ∈ S j) := by
      intro j hj
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨i, hi⟩ := hj
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [hi]⟩
    calc J.card ≤ _ := Finset.card_le_card this
      _ ≤ ∑ i : Fin n, (Finset.univ.filter fun j => i ∈ S j).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin n, d := Finset.sum_le_sum fun i _ => hdeg' i
      _ = n * d := by simp
  have hZc : Z.card ≤ 1 + n * d * 4 ^ kap := by
    calc Z.card ≤ _ := Finset.card_le_card hZsub
      _ ≤ ({fun _ => 0} : Finset (Fin n → Fin 4)).card + (J.biUnion (fun j =>
          Finset.univ.filter fun P : Fin n → Fin 4 => wordSupport P ⊆ S j)).card :=
          Finset.card_union_le _ _
      _ ≤ 1 + ∑ j ∈ J, (Finset.univ.filter fun P : Fin n → Fin 4 => wordSupport P ⊆ S j).card := by
          rw [Finset.card_singleton]; exact Nat.add_le_add_left Finset.card_biUnion_le _
      _ ≤ 1 + ∑ _j ∈ J, 4 ^ kap := by
          refine Nat.add_le_add_left (Finset.sum_le_sum fun j _ => ?_) _
          rw [g59a_cardU]; exact Nat.pow_le_pow_right (by norm_num) (hT j).2.1
      _ = 1 + J.card * 4 ^ kap := by simp
      _ ≤ 1 + n * d * 4 ^ kap := Nat.add_le_add_left (Nat.mul_le_mul_right _ hJ) _
  calc terms.length ≤ 1 + n * d * 4 ^ kap := h1.trans hZc
    _ ≤ (1 + d * 4 ^ kap) * n := by nlinarith

theorem g59a_obs (kap d : ℕ) (hk : 1 ≤ kap) (hd : 1 ≤ d) : ∃ C : ℝ, 0 < C ∧
    ∀ (n N : ℕ), 1 ≤ n → 1 ≤ N → ∀ terms : SparseObservable n,
      ValidDescription kap terms → HasBoundedDegree kap d (decodeObservable terms) →
      ∀ data : Fin N → Shot n,
        (runLabels terms data).value = ((List.finRange N).map
          (fun l => effectProb (decodeObservable terms) (pauliSnapshot (data l)))).toArray ∧
        (runLabels terms data).steps ≤ (5 * kap + 3) * terms.length * N + N ∧
        ((runLabels terms data).steps : ℝ) ≤ C * (n : ℝ) * (N : ℝ) := by
  refine ⟨((5 * kap + 3) * (1 + d * 4 ^ kap) + 1 : ℕ), by positivity, ?_⟩
  intro n N hn hN terms hv hdeg data
  have hval := (g59a_labels terms data).1
  have hst := (g59a_labels terms data).2
  have hsteps : (runLabels terms data).steps ≤ (5 * kap + 3) * terms.length * N + N := by
    rw [hst]
    have := List.sum_le_card_nsmul ((List.finRange N).map (fun l => (runLabel terms (data l)).steps))
      ((5 * kap + 3) * terms.length) (by
        intro x hx
        obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx
        exact g59a_label_steps kap terms hv _)
    rw [List.length_map, List.length_finRange, smul_eq_mul] at this
    nlinarith
  refine ⟨?_, hsteps, ?_⟩
  · rw [hval]
    congr 1
    exact List.map_congr_left fun l _ => g59a_label_value kap terms hv _
  · have hl := g59a_len hn kap d terms hv hdeg
    have h2 : (runLabels terms data).steps ≤ ((5 * kap + 3) * (1 + d * 4 ^ kap) + 1) * n * N := by
      calc _ ≤ (5 * kap + 3) * terms.length * N + N := hsteps
        _ ≤ (5 * kap + 3) * ((1 + d * 4 ^ kap) * n) * N + n * N := by
            have := Nat.mul_le_mul_left (5 * kap + 3) hl
            have h3 : N ≤ n * N := Nat.le_mul_of_pos_left N hn
            nlinarith
        _ = _ := by ring
    exact_mod_cast h2

theorem solution :
    ∀ (kap d : ℕ), 1 ≤ kap → 1 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (n N : ℕ), 1 ≤ n → 1 ≤ N → ∀ terms : SparseObservable n,
      ValidDescription kap terms → HasBoundedDegree kap d (decodeObservable terms) →
      ∀ data : Fin N → Shot n,
        (runLabels terms data).value = ((List.finRange N).map
          (fun l => effectProb (decodeObservable terms) (pauliSnapshot (data l)))).toArray ∧
        (runLabels terms data).steps ≤ (5 * kap + 3) * terms.length * N + N ∧
        ((runLabels terms data).steps : ℝ) ≤ C * (n : ℝ) * (N : ℝ) :=
  fun kap d hk hd => g59a_obs kap d hk hd
