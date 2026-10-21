-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P03.corollary10_bestTime
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:26:44.847416+00:00
-- url     : https://prove2.me/submissions/285a24bc-3292-4f19-9a83-9a8c2d50e499

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

lemma g59a_disk (k : ℕ) (a : ℕ → ℝ) (M : ℝ)
    (hM : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |∑ i ∈ Finset.Icc 1 k, a i * t ^ i| ≤ M) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * z ^ i‖ ≤ (1 + Real.sqrt 2) ^ k * M := by
  set f : ℂ → ℂ := fun w => ∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * (w ^ (k - i) * ((w ^ 2 + 1) / 2) ^ i)
    with hf
  have hf_eq : ∀ w : ℂ, w ≠ 0 → f w = w ^ k * ∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * ((w + w⁻¹) / 2) ^ i := by
    intro w hw
    rw [hf, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
    have e1 : (w ^ 2 + 1) / 2 = w * ((w + w⁻¹) / 2) := by field_simp
    rw [e1, mul_pow, show w ^ k = w ^ (k - i) * w ^ i by rw [← pow_add, Nat.sub_add_cancel hik]]
    ring
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 ⟨by norm_num, by norm_num⟩)
  have hcircle : ∀ w : ℂ, w ∈ frontier (Metric.ball (0 : ℂ) 1) → ‖f w‖ ≤ M := by
    intro w hw
    rw [frontier_ball (0 : ℂ) one_ne_zero, mem_sphere_zero_iff_norm] at hw
    have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; norm_num at hw
    rw [hf_eq w hw0, norm_mul, norm_pow, hw, one_pow, one_mul]
    have hinv : w⁻¹ = conj w := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hw]; simp
    have hre : (w + w⁻¹) / 2 = ((w.re : ℝ) : ℂ) := by
      rw [hinv, Complex.add_conj]; push_cast; ring
    rw [hre]
    have : ∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * ((w.re : ℝ) : ℂ) ^ i =
        ((∑ i ∈ Finset.Icc 1 k, a i * w.re ^ i : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    have hb := Complex.abs_re_le_norm w
    rw [hw] at hb
    exact hM _ ⟨by linarith [neg_abs_le w.re], by linarith [le_abs_self w.re]⟩
  have hdiff : Differentiable ℂ f := by
    rw [hf]; fun_prop
  have hdisk : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖f w‖ ≤ M := by
    intro w hw
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
      hdiff.diffContOnCl hcircle ?_
    rw [closure_ball (0 : ℂ) one_ne_zero, mem_closedBall_zero_iff]; exact hw
  have key : ∀ w v : ℂ, w * v = 1 → w + v = 2 * z → ‖w‖ ≤ 1 →
      ‖∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * z ^ i‖ ≤ (1 + Real.sqrt 2) ^ k * M := by
    intro w v hwv hsum hw1
    have hw0 : w ≠ 0 := by intro h; rw [h, zero_mul] at hwv; exact zero_ne_one hwv
    have hv : v = w⁻¹ := by
      field_simp; rw [mul_comm]; exact hwv
    have hz' : z = (w + w⁻¹) / 2 := by rw [← hv]; linear_combination -hsum / 2
    set r := ‖w‖ with hr
    have hr0 : 0 < r := norm_pos_iff.mpr hw0
    have hvn : ‖v‖ = r⁻¹ := by rw [hv, norm_inv]
    have hle : ‖v‖ ≤ 2 + r := by
      have : v = (w + v) - w := by ring
      rw [this, hsum]
      calc ‖2 * z - w‖ ≤ ‖2 * z‖ + ‖w‖ := norm_sub_le _ _
        _ = 2 + r := by rw [norm_mul, hz, hr]; simp
    rw [hvn] at hle
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have h1 : 1 ≤ r * (2 + r) := by
      have := mul_le_mul_of_nonneg_left hle hr0.le
      rwa [mul_inv_cancel₀ hr0.ne'] at this
    have hrinv : r⁻¹ ≤ 1 + Real.sqrt 2 := by
      rw [inv_le_iff_one_le_mul₀ hr0]
      nlinarith [sq_nonneg (r + 1 - Real.sqrt 2)]
    have hfw := hdisk w hw1
    rw [hf_eq w hw0, norm_mul, norm_pow, ← hz'] at hfw
    have hrk : 0 < r ^ k := pow_pos hr0 k
    calc ‖∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * z ^ i‖ ≤ M / r ^ k := by
          rw [le_div_iff₀ hrk, mul_comm]; exact hfw
      _ = (r⁻¹) ^ k * M := by rw [inv_pow]; ring
      _ ≤ (1 + Real.sqrt 2) ^ k * M :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_nonneg.mpr hr0.le) hrinv k) hM0
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (z ^ 2 - 1) two_pos
  have hprod : (z + s) * (z - s) = 1 := by linear_combination -hs
  by_cases h1 : ‖z + s‖ ≤ 1
  · exact key (z + s) (z - s) hprod (by ring) h1
  · refine key (z - s) (z + s) (by rw [mul_comm]; exact hprod) (by ring) ?_
    have := congrArg norm hprod
    rw [norm_mul, norm_one] at this
    push Not at h1
    nlinarith [norm_nonneg (z - s)]

lemma g59a_geom (N : ℕ) (hN : N ≠ 0) (ω : ℂ) (hω : IsPrimitiveRoot ω N) (m : ℕ) :
    ∑ l ∈ Finset.range N, (ω ^ m) ^ l = if N ∣ m then (N : ℂ) else 0 := by
  by_cases h : N ∣ m
  · rw [if_pos h, (hω.pow_eq_one_iff_dvd m).mpr h]; simp
  · rw [if_neg h]
    have h1 : ω ^ m ≠ 1 := fun h' => h ((hω.pow_eq_one_iff_dvd m).mp h')
    rw [geom_sum_eq h1, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self, zero_div]

lemma g59a_cauchy (k : ℕ) (a : ℕ → ℝ) (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) (B : ℝ)
    (hB : ∀ z : ℂ, ‖z‖ = 1 → ‖∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * z ^ i‖ ≤ B) : |a j| ≤ B := by
  set N := k + 1 with hN
  have hN0 : N ≠ 0 := by omega
  set ω := Complex.exp (2 * Real.pi * Complex.I / N) with hωdef
  have hω : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N hN0
  have hωn : ‖ω‖ = 1 := hω.norm'_eq_one hN0
  have hsum : ∑ l ∈ Finset.range N, (∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * (ω ^ l) ^ i) *
      (ω ^ l) ^ (N - j) = (N : ℂ) * (a j : ℂ) := by
    have e : ∀ l, (∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * (ω ^ l) ^ i) * (ω ^ l) ^ (N - j) =
        ∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * (ω ^ (i + (N - j))) ^ l := by
      intro l; rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← pow_mul, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]; ring_nf
    simp only [e]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, g59a_geom N hN0 ω hω]
    rw [Finset.sum_eq_single j]
    · rw [if_pos (by rw [show j + (N - j) = N by omega])]; ring
    · intro i hi hij
      rw [if_neg, mul_zero]
      rintro ⟨c, hc⟩
      have hi' := Finset.mem_Icc.mp hi
      rcases c with _ | _ | c
      · omega
      · omega
      · have h2 : N * (c + 1 + 1) = N * c + 2 * N := by ring
        omega
    · intro h; exact absurd (Finset.mem_Icc.mpr ⟨hj, hjk⟩) h
  have hbound : ‖(N : ℂ) * (a j : ℂ)‖ ≤ N * B := by
    rw [← hsum]
    calc _ ≤ ∑ l ∈ Finset.range N, ‖(∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * (ω ^ l) ^ i) *
          (ω ^ l) ^ (N - j)‖ := norm_sum_le _ _
      _ ≤ ∑ l ∈ Finset.range N, B := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [norm_mul, norm_pow, norm_pow, hωn, one_pow, one_pow, mul_one]
          exact hB _ (by rw [norm_pow, hωn, one_pow])
      _ = N * B := by simp
  rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs] at hbound
  have : (0 : ℝ) < N := by positivity
  exact le_of_mul_le_mul_left hbound this

theorem g59a_poly (k : ℕ) (a : ℕ → ℝ) (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∃ t ∈ Set.Icc (-1 : ℝ) 1,
      |a j| ≤ (1 + Real.sqrt 2) ^ k * |∑ i ∈ Finset.Icc 1 k, a i * t ^ i| := by
  have hc : ContinuousOn (fun t : ℝ => |∑ i ∈ Finset.Icc 1 k, a i * t ^ i|) (Set.Icc (-1) 1) :=
    (by fun_prop : Continuous fun t : ℝ => |∑ i ∈ Finset.Icc 1 k, a i * t ^ i|).continuousOn
  obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (-1 : ℝ) ≤ 1)) hc
  refine ⟨t0, ht0, ?_⟩
  exact g59a_cauchy k a j hj hjk _ fun z hz => g59a_disk k a _ (fun t ht => hmax ht) z hz
lemma g59a_nwt_trace {I : Type*} [Fintype I] [DecidableEq I] (A : I → Matrix Bool Bool ℂ) :
    (namedWireTensor A).trace = ∏ i, (A i).trace := by
  simp only [Matrix.trace, Matrix.diag, namedWireTensor]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma g59a_trP (p : Fin 4) : (singlePauli p).trace = if p = 0 then 2 else 0 := by
  fin_cases p <;> simp [singlePauli, pauliX, pauliY, pauliZ, Matrix.trace, Fintype.sum_bool] <;> norm_num

lemma g59a_path_wire (p : Fin 4) {k : ℕ} (c : ℂ) (rs : Fin k → ℝ) (ρ : Fin k → Matrix Bool Bool ℂ)
    (htr : ∀ s, (ρ s).trace = 1) :
    (singlePauli p * ((1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ) + (c : ℂ) • ∑ s, (rs s : ℂ) •
      (ρ s - (1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ)))).trace =
      if p = 0 then 1 else (c : ℂ) * ∑ s, (rs s : ℂ) * (singlePauli p * ρ s).trace := by
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sum, Matrix.mul_sub, Matrix.mul_one,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum, Matrix.trace_sub, g59a_trP, smul_eq_mul]
  split_ifs with h
  · subst h
    simp only [singlePauli, if_true, Matrix.one_mul, htr]
    norm_num
  · simp
lemma g59a_pure_trace (ρ : Matrix Bool Bool ℂ) (h : IsPureQubit ρ) : ρ.trace = 1 := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  have h1 : ‖ψ‖ = 1 := hψ
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h1
  simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  exact_mod_cast h1


def g59a_K {I : Type*} [Fintype I] {m : ℕ} (P : I → Fin 4) (rho : Fin m → I → Matrix Bool Bool ℂ)
    (σ : Fin m → Bool) : ℂ :=
  ∏ i, (if P i = 0 then 1 else (((1 : ℝ) / (m : ℝ) : ℝ) : ℂ) *
    ∑ s, ((rademacherValue (σ s) : ℝ) : ℂ) * (singlePauli (P i) * rho s i).trace)

lemma g59a_wordpath {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ} (P : I → Fin 4)
    (rho : Fin m → I → Matrix Bool Bool ℂ) (htr : ∀ s i, (rho s i).trace = 1) (t : ℝ)
    (σ : Fin m → Bool) :
    (wordMatrix P * productPath t rho σ).trace = (t : ℂ) ^ pauliWeight P * g59a_K P rho σ := by
  unfold wordMatrix productPath
  rw [g59a_nwt_mul, g59a_nwt_trace]
  rw [Finset.prod_congr rfl (fun i _ => g59a_path_wire (P i) ((t : ℂ) / ((m : ℝ) : ℂ))
    (fun s => rademacherValue (σ s)) (fun s => rho s i) (fun s => htr s i))]
  have : ∀ i, (if P i = 0 then (1 : ℂ) else ((t : ℂ) / ((m : ℝ) : ℂ)) *
      ∑ s, ((rademacherValue (σ s) : ℝ) : ℂ) * (singlePauli (P i) * rho s i).trace) =
      (if P i = 0 then 1 else (t : ℂ)) * (if P i = 0 then 1 else (((1 : ℝ) / (m : ℝ) : ℝ) : ℂ) *
      ∑ s, ((rademacherValue (σ s) : ℝ) : ℂ) * (singlePauli (P i) * rho s i).trace) := by
    intro i; split_ifs
    · simp
    · push_cast; ring
  rw [Finset.prod_congr rfl (fun i _ => this i), Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  rfl

lemma g59a_lm_trace (b : Fin 3 → ℝ) : (localMaximizer b).trace = 1 := by
  unfold localMaximizer
  simp only
  split_ifs
  · rw [Matrix.trace_smul, Matrix.trace_add]
    simp [pauliZ, Matrix.trace, Fintype.sum_bool]
  · rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sum]
    have : ∀ p : Fin 3, (singlePauli ⟨p.val + 1, by omega⟩).trace = 0 := by
      intro p; rw [g59a_trP, if_neg]; intro h; have := congrArg Fin.val h; simp at this
    simp only [Matrix.trace_smul, this, smul_zero, Finset.sum_const_zero, add_zero]
    simp [Matrix.trace, Fintype.sum_bool]

lemma g59a_bd_le {n : ℕ} (H : Matrix (Qubits n) (Qubits n) ℂ) (k : ℕ) (r : ℝ) (hk : 1 ≤ k) :
    1 ≤ bestDegree H k r ∧ bestDegree H k r ≤ k := by
  unfold bestDegree
  simp only
  split_ifs with h
  · exact Finset.mem_Icc.mp (Classical.choose_spec h).1
  · exact ⟨le_rfl, hk⟩

theorem g59a_cor10 (n k de q : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hde : 1 ≤ de) (hden : de ≤ n) (ce : ℝ) (hce : 1 ≤ ce)
    (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) (hloc : IsLocal k H)
    (hexp : HasExpansion H ce de)
    (hq : bestDegree H k (expansionExponent de) = q + 1)
    (rho : Fin q → Fin n → Matrix Bool Bool ℂ) (hrho : ∀ s j, IsPureQubit (rho s j))
    (sigma : Fin (q + 1) → Bool) :
    let full := completedReplicas H rho
    |effectProb (homogeneousSlice (q + 1) H) (productPath 1 full sigma)| /
      (1 + Real.sqrt 2) ^ k ≤
      |effectProb H (productPath (bestTime H full sigma) full sigma) -
        coefficient H (fun _ => 0)| := by
  intro full
  have htr : ∀ s j, (full s j).trace = 1 := by
    intro s j
    simp only [full, completedReplicas]
    split_ifs
    · exact g59a_pure_trace _ (hrho _ _)
    · exact g59a_lm_trace _
  set A : (Fin n → Fin 4) → ℝ := fun P => coefficient H P * (g59a_K P full sigma).re with hA
  set a : ℕ → ℝ := fun w => ∑ P ∈ Finset.univ.filter (fun P : Fin n → Fin 4 => pauliWeight P = w), A P
    with ha
  have hE : ∀ t : ℝ, effectProb H (productPath t full sigma) = ∑ P, A P * t ^ pauliWeight P := by
    intro t
    rw [g59a_eP H hH]
    refine Finset.sum_congr rfl fun P _ => ?_
    unfold effectProb
    rw [g59a_wordpath P full htr t sigma, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    simp only [hA]; ring
  have h0 : ∀ P : Fin n → Fin 4, pauliWeight P = 0 ↔ P = fun _ => 0 := by
    intro P
    simp only [pauliWeight, wordSupport, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.mem_univ, true_implies, not_not]
    exact ⟨fun h => funext h, fun h i => by rw [h]⟩
  have hK0 : g59a_K (fun _ : Fin n => (0 : Fin 4)) full sigma = 1 := by simp [g59a_K]
  have hpoly : ∀ t : ℝ, effectProb H (productPath t full sigma) - coefficient H (fun _ => 0) =
      ∑ i ∈ Finset.Icc 1 k, a i * t ^ i := by
    intro t
    rw [hE]
    have hsplit : ∑ P, A P * t ^ pauliWeight P =
        A (fun _ => 0) + ∑ P ∈ Finset.univ.filter (fun P : Fin n → Fin 4 =>
          1 ≤ pauliWeight P ∧ pauliWeight P ≤ k), A P * t ^ pauliWeight P := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun P : Fin n → Fin 4 => P = fun _ => 0)]
      rw [Finset.filter_eq' Finset.univ, if_pos (Finset.mem_univ _), Finset.sum_singleton,
        (h0 _).mpr rfl, pow_zero, mul_one]
      congr 1
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun P : Fin n → Fin 4 => ¬ P = fun _ => 0)
        (fun P => pauliWeight P ≤ k)]
      have hz : ∑ P ∈ (Finset.univ.filter fun P : Fin n → Fin 4 => ¬ P = fun _ => 0).filter
          (fun P => ¬ pauliWeight P ≤ k), A P * t ^ pauliWeight P = 0 := by
        refine Finset.sum_eq_zero fun P hP => ?_
        simp only [Finset.mem_filter] at hP
        simp only [hA, hloc P (by omega), zero_mul]
      rw [hz, add_zero, Finset.filter_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext P; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Nat.one_le_iff_ne_zero.mpr (fun h => h1 ((h0 P).mp h)), h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨fun h => by rw [(h0 P).mpr h] at h1; omega, h2⟩
    have hc0 : A (fun _ => 0) = coefficient H (fun _ => 0) := by simp [hA, hK0]
    rw [hsplit, hc0, add_sub_cancel_left]
    simp only [ha, Finset.sum_mul]
    have hr : ∀ x ∈ Finset.Icc 1 k, ∑ P ∈ Finset.univ.filter (fun P : Fin n → Fin 4 => pauliWeight P = x),
        A P * t ^ x = ∑ P ∈ (Finset.univ.filter (fun P : Fin n → Fin 4 =>
          1 ≤ pauliWeight P ∧ pauliWeight P ≤ k)).filter (fun P => pauliWeight P = x),
          A P * t ^ pauliWeight P := by
      intro x hx
      have hx' := Finset.mem_Icc.mp hx
      refine Finset.sum_congr ?_ fun P hP => by rw [(Finset.mem_filter.mp hP).2]
      ext P; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact ⟨⟨h ▸ hx'.1, h ▸ hx'.2⟩, h⟩
      · exact fun h => h.2
    rw [Finset.sum_congr rfl hr, Finset.sum_fiberwise_of_maps_to]
    exact fun P hP => by simp only [Finset.mem_filter] at hP; exact Finset.mem_Icc.mpr hP.2
  have hslice : effectProb (homogeneousSlice (q + 1) H) (productPath 1 full sigma) = a (q + 1) := by
    unfold effectProb homogeneousSlice
    rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun P hP => ?_
    simp only [Finset.mem_filter] at hP
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
      g59a_wordpath P full htr 1 sigma]
    simp [hA]
  obtain ⟨hq1, hqk⟩ := g59a_bd_le H k (expansionExponent de) hk
  rw [hq] at hq1 hqk
  obtain ⟨t, ht, hbound⟩ := g59a_poly k a (q + 1) hq1 hqk
  have hcont : ContinuousOn (fun u : ℝ => |effectProb H (productPath u full sigma) -
      coefficient H (fun _ => 0)|) (Set.Icc (-1) 1) := by
    simp only [hpoly]
    exact (by fun_prop : Continuous fun u : ℝ => |∑ i ∈ Finset.Icc 1 k, a i * u ^ i|).continuousOn
  obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (-1 : ℝ) ≤ 1)) hcont
  have hex : ∃ t ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |effectProb H (productPath u full sigma) - coefficient H (fun _ => 0)| ≤
      |effectProb H (productPath t full sigma) - coefficient H (fun _ => 0)| :=
    ⟨t0, ht0, fun u hu => hmax hu⟩
  have hbt : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |effectProb H (productPath u full sigma) - coefficient H (fun _ => 0)| ≤
      |effectProb H (productPath (bestTime H full sigma) full sigma) - coefficient H (fun _ => 0)| := by
    unfold bestTime
    simp only
    rw [dif_pos hex]
    exact (Classical.choose_spec hex).2
  rw [hslice, div_le_iff₀ (by positivity)]
  calc |a (q + 1)| ≤ (1 + Real.sqrt 2) ^ k * |∑ i ∈ Finset.Icc 1 k, a i * t ^ i| := hbound
    _ = (1 + Real.sqrt 2) ^ k * |effectProb H (productPath t full sigma) - coefficient H (fun _ => 0)| := by
        rw [hpoly]
    _ ≤ (1 + Real.sqrt 2) ^ k * |effectProb H (productPath (bestTime H full sigma) full sigma) -
        coefficient H (fun _ => 0)| := mul_le_mul_of_nonneg_left (hbt t ht) (by positivity)
    _ = _ := mul_comm _ _

theorem solution (n k de q : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hde : 1 ≤ de) (hden : de ≤ n) (ce : ℝ) (hce : 1 ≤ ce)
    (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) (hloc : IsLocal k H)
    (hexp : HasExpansion H ce de)
    (hq : bestDegree H k (expansionExponent de) = q + 1)
    (rho : Fin q → Fin n → Matrix Bool Bool ℂ) (hrho : ∀ s j, IsPureQubit (rho s j))
    (sigma : Fin (q + 1) → Bool) :
    let full := completedReplicas H rho
    |effectProb (homogeneousSlice (q + 1) H) (productPath 1 full sigma)| /
      (1 + Real.sqrt 2) ^ k ≤
      |effectProb H (productPath (bestTime H full sigma) full sigma) -
        coefficient H (fun _ => 0)| :=
  g59a_cor10 n k de q hn hk hde hden ce hce H hH hloc hexp hq rho hrho sigma
