-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P29.typicalCompression_fidelity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:19:57.450057+00:00
-- url     : https://prove2.me/submissions/ceaa4190-e314-414f-bca4-5e99a0467dad

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

theorem X7P29_lin_expand {I J : Type*} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (X : Matrix I I ℂ) :
    L X = ∑ i, ∑ j, X i j • L (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem X7P29_choi_psd {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (h : Entanglement.IsCompletelyPositive L) :
    (Matrix.of fun (p q : I × J) => L (Matrix.single p.1 q.1 1) p.2 q.2).PosSemidef := by
  let e := Fintype.equivFin I
  let Ω : Fin (Fintype.card I) × I → ℂ := fun q => if q.1 = e q.2 then 1 else 0
  have hY := h _ _ (Matrix.posSemidef_vecMulVec_self_star Ω)
  have hE : (Matrix.of fun (p q : I × J) => L (Matrix.single p.1 q.1 1) p.2 q.2) =
      (idTensorSuperop L (Matrix.vecMulVec Ω (star Ω))).submatrix
      (fun q : I × J => (e q.1, q.2)) (fun q => (e q.1, q.2)) := by
    ext ⟨i, o⟩ ⟨i', o'⟩
    rw [Matrix.submatrix_apply, Matrix.of_apply]
    show L (Matrix.single i i' 1) o o' =
      L (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) o o'
    have hX : (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) =
        Matrix.single i i' 1 := by
      ext j j'
      by_cases h1 : i = j <;> by_cases h2 : i' = j' <;>
        simp [Matrix.single_apply, Matrix.vecMulVec_apply, Ω, h1, h2, Ne.symm, eq_comm]
    rw [hX]
  rw [hE]
  exact hY.submatrix _

theorem X7P29_perm3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ l, f a b l = ∑ l, ∑ b, ∑ a, f a b l := by
  calc ∑ a, ∑ b, ∑ l, f a b l = ∑ a, ∑ l, ∑ b, f a b l :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ b, f a b l := Finset.sum_comm
    _ = ∑ l, ∑ b, ∑ a, f a b l := Finset.sum_congr rfl fun l _ => Finset.sum_comm

theorem X7P29_kraus {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (h : Entanglement.IsCompletelyPositive L) :
    ∃ m : ℕ, ∃ K : Fin m → Matrix J I ℂ, ∀ X, L X = krausApply K X := by
  obtain ⟨m, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (X7P29_choi_psd L h)
  have hMij : ∀ i j o o', L (Matrix.single i j 1) o o' =
      ∑ l, g l (i, o) * star (g l (j, o')) := by
    intro i j o o'
    have := congrFun (congrFun hg (i, o)) (j, o')
    rw [Matrix.of_apply] at this
    rw [this, Matrix.sum_apply]
    simp [Matrix.vecMulVec_apply]
  refine ⟨m, fun l => Matrix.of fun o i => g l (i, o), fun X => ?_⟩
  ext o o'
  rw [X7P29_lin_expand]
  simp only [krausApply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hMij,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [X7P29_perm3]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => ?_
  ring

theorem X7P29_entry {I : Type*} [Fintype I] [DecidableEq I] (K : Matrix I I ℂ) (i j k l : I) :
    (K * (Matrix.single j l (1:ℂ) : Matrix I I ℂ) * Kᴴ) i k = K i j * conj (K k l) := by
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]

theorem X7P29_fe {I : Type*} [Fintype I] [DecidableEq I] {κ : Type*} [Fintype κ]
    (rho : Matrix I I ℂ) (A : Superop I I) (K : κ → Matrix I I ℂ)
    (hA : ∀ X, A X = krausApply K X) :
    fe rho A = ∑ a, Complex.normSq ((K a * rho).trace) := by
  unfold fe
  have h5 : ∀ f : I → I → I → I → κ → ℂ, ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, f i j k l a =
      ∑ a, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l a := by
    intro f
    calc _ = ∑ i, ∑ j, ∑ k, ∑ a, ∑ l, f i j k l a :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ a, ∑ k, ∑ l, f i j k l a :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ j, ∑ k, ∑ l, f i j k l a :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have ht : ∀ a, (K a * rho).trace = ∑ i, ∑ j, K a i j * rho j i := by
    intro a; simp [Matrix.trace, Matrix.mul_apply]
  have key : (∑ i, ∑ j, ∑ k, ∑ l, rho j i * conj (rho l k) * A (Matrix.single j l (1:ℂ)) i k) =
      ∑ a, (K a * rho).trace * conj ((K a * rho).trace) := by
    simp only [hA, krausApply, Matrix.sum_apply, X7P29_entry, Finset.mul_sum]
    rw [h5]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ht, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul]
    ring
  rw [key, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re]

end QAlgorithms.Papers.Independent.Gap48.P29

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

theorem X7T_proj {ι : Type*} [Fintype ι] [DecidableEq ι] (rho : Matrix ι ι ℂ)
    (hrho : rho.IsHermitian) (f : ℝ → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1) :
    let P := cfc f rho
    P * P = P ∧ Pᴴ = P ∧ P * rho = rho * P := by
  intro P
  have hsa : IsSelfAdjoint rho := hrho
  have hcont : ContinuousOn f (spectrum ℝ rho) := Matrix.finite_real_spectrum.continuousOn f
  refine ⟨?_, ?_, ?_⟩
  · show cfc f rho * cfc f rho = cfc f rho
    rw [← cfc_mul f f rho]
    congr 1
    funext x
    rcases hf x with h | h <;> simp [h]
  · exact (cfc_predicate f rho : IsSelfAdjoint (cfc f rho))
  · show cfc f rho * rho = rho * cfc f rho
    exact (Commute.refl rho).cfc_real f |>.symm.eq.symm

end QAlgorithms.Papers.Independent.Gap48.P29

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

theorem X7T_tr_mul_ct {I L : Type*} [Fintype I] [Fintype L] (X Y : Matrix I L ℂ) :
    (X * Yᴴ).trace = ∑ i, ∑ l, X i l * star (Y i l) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Complex Cauchy–Schwarz on a finite double sum. -/
theorem X7T_cs_sum {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    Complex.normSq (∑ k, a k * star (b k)) ≤
      (∑ k, Complex.normSq (a k)) * (∑ k, Complex.normSq (b k)) := by
  have h1 : ‖∑ k, a k * star (b k)‖ ≤ ∑ k, ‖a k‖ * ‖b k‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [norm_mul, norm_star]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖a k‖) (fun k => ‖b k‖)
  rw [Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_eq_norm_sq]
  calc ‖∑ k, a k * star (b k)‖ ^ 2 ≤ (∑ k, ‖a k‖ * ‖b k‖) ^ 2 := by
        gcongr
    _ ≤ _ := h2

theorem X7T_cs {I : Type*} [Fintype I] (E sigma : Matrix I I ℂ) (hs : sigma.PosSemidef) :
    Complex.normSq (E * sigma).trace ≤ sigma.trace.re * (Eᴴ * E * sigma).trace.re := by
  obtain ⟨n, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hs
  let G : Matrix I (Fin n) ℂ := Matrix.of fun i l => g l i
  have hG : sigma = G * Gᴴ := by
    rw [hg]; ext i i'
    simp [G, Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
      Matrix.conjTranspose_apply]
  have e1 : (E * sigma).trace = ∑ i, ∑ l, (E * G) i l * star (G i l) := by
    rw [hG, ← Matrix.mul_assoc, X7T_tr_mul_ct]
  have e2 : sigma.trace = ((∑ i, ∑ l, Complex.normSq (G i l) : ℝ) : ℂ) := by
    rw [hG, X7T_tr_mul_ct]; push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.star_def, Complex.mul_conj]
  have e3 : (Eᴴ * E * sigma).trace = ((∑ i, ∑ l, Complex.normSq ((E * G) i l) : ℝ) : ℂ) := by
    have : (Eᴴ * E * sigma).trace = ((E * G) * (E * G)ᴴ).trace := by
      rw [hG, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [this, X7T_tr_mul_ct]; push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.star_def, Complex.mul_conj]
  rw [e1, e2, e3, Complex.ofReal_re, Complex.ofReal_re, mul_comm]
  have := X7T_cs_sum (fun p : I × Fin n => (E * G) p.1 p.2) (fun p => G p.1 p.2)
  simpa only [Fintype.sum_prod_type] using this

theorem X7T_fe_le {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ} (EK : Fin m → Matrix I I ℂ)
    (hK : ∑ a, (EK a)ᴴ * EK a = 1) (sigma : Matrix I I ℂ) (hs : sigma.PosSemidef) :
    ∑ a, Complex.normSq (EK a * sigma).trace ≤ sigma.trace.re ^ 2 := by
  calc ∑ a, Complex.normSq (EK a * sigma).trace
      ≤ ∑ a, sigma.trace.re * ((EK a)ᴴ * EK a * sigma).trace.re :=
        Finset.sum_le_sum fun a _ => X7T_cs _ _ hs
    _ = sigma.trace.re * ((∑ a, (EK a)ᴴ * EK a) * sigma).trace.re := by
        rw [← Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
    _ = _ := by rw [hK, Matrix.one_mul, sq]

theorem X7T_alg {m : ℕ} (u v : Fin m → ℂ) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hu : ∑ a, Complex.normSq (u a) ≤ μ ^ 2) (hv : ∑ a, Complex.normSq (v a) ≤ (1 - μ) ^ 2) :
    |∑ a, Complex.normSq (u a) / μ ^ 2 - ∑ a, Complex.normSq (u a + v a)| ≤ 4 * (1 - μ) := by
  set U := ∑ a, Complex.normSq (u a)
  set V := ∑ a, Complex.normSq (v a)
  set X := ∑ a, (u a * star (v a)).re
  have hsum : ∑ a, Complex.normSq (u a + v a) = U + V + 2 * X := by
    simp only [U, V, X, Complex.normSq_add, Finset.sum_add_distrib, ← Finset.mul_sum,
      Complex.star_def]
  have hX : |X| ≤ Real.sqrt U * Real.sqrt V := by
    have h1 : |X| ≤ ‖∑ a, u a * star (v a)‖ := by
      simp only [X, ← Complex.re_sum]
      exact Complex.abs_re_le_norm _
    have h2 := X7T_cs_sum u v
    rw [Complex.normSq_eq_norm_sq] at h2
    have h3 : ‖∑ a, u a * star (v a)‖ ≤ Real.sqrt (U * V) :=
      Real.le_sqrt_of_sq_le h2
    rw [Real.sqrt_mul (Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _)] at h3
    linarith
  have hU0 : 0 ≤ U := Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _
  have hsU : Real.sqrt U ≤ μ := Real.sqrt_le_iff.mpr ⟨hμ0.le, hu⟩
  have hsV : Real.sqrt V ≤ 1 - μ := Real.sqrt_le_iff.mpr ⟨by linarith, hv⟩
  have hXb : |X| ≤ μ * (1 - μ) :=
    hX.trans (mul_le_mul hsU hsV (Real.sqrt_nonneg _) hμ0.le)
  rw [hsum, ← Finset.sum_div]
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hq : U / μ ^ 2 ≤ 1 := (div_le_one hμ2).mpr hu
  have hq0 : 0 ≤ U / μ ^ 2 := div_nonneg hU0 hμ2.le
  have hUeq : U = μ ^ 2 * (U / μ ^ 2) := by field_simp
  rw [abs_le]
  rcases abs_le.mp hXb with ⟨hX1, hX2⟩
  set q := U / μ ^ 2
  have hA : 0 ≤ q * (1 - μ ^ 2) := mul_nonneg hq0 (by nlinarith)
  have hB : q * (1 - μ ^ 2) ≤ 1 - μ ^ 2 := by
    have : 0 ≤ 1 - μ ^ 2 := by nlinarith
    nlinarith
  have hD : q - (U + V + 2 * X) = q * (1 - μ ^ 2) - V - 2 * X := by rw [hUeq]; ring
  rw [hD]
  constructor <;> nlinarith [hX1, hX2, hA, hB, hv, hV0, hμ1, hμ0]

end QAlgorithms.Papers.Independent.Gap48.P29

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

theorem X7L8_tr_zero {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ)
    (h : ∀ X : Matrix I I ℂ, (M * X).trace = 0) : M = 0 := by
  ext i j
  have := h (Matrix.single j i 1)
  simpa [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq,
    Finset.sum_ite_eq'] using this

theorem X7L8_kraus_trace {I : Type*} [Fintype I] {ι : Type*} [Fintype ι]
    (K : ι → Matrix I I ℂ) (X : Matrix I I ℂ) :
    (krausApply K X).trace = ((∑ g, (K g)ᴴ * K g) * X).trace := by
  simp only [krausApply, Matrix.trace_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]

theorem X7L8_sum_zero {I : Type*} [Fintype I] {ι : Type*} [Fintype ι] (B : ι → Matrix I I ℂ)
    (h : ∑ g, (B g)ᴴ * B g = 0) (g : ι) : B g = 0 := by
  have htr : ∑ g, ((B g)ᴴ * B g).trace.re = 0 := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, h, Matrix.trace_zero, Complex.zero_re]
  have hnn : ∀ g, 0 ≤ ((B g)ᴴ * B g).trace.re := fun g =>
    (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self (B g)).trace_nonneg).1
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun g _ => hnn g)).mp htr g (Finset.mem_univ g)
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  apply Complex.ext
  · simpa using hz
  · have := (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self (B g)).trace_nonneg).2
    simpa using this.symm

theorem X7L8_alg {m k : ℕ} (u v : Fin m → ℂ) (W μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hu : ∑ a, Complex.normSq (u a) ≤ μ ^ 2) (hv : ∑ a, Complex.normSq (v a) ≤ (1 - μ) ^ 2)
    (hW0 : 0 ≤ W) (hW : W ≤ (1 - μ) ^ 2) :
    |(∑ a, Complex.normSq (u a) + W) - ∑ a, Complex.normSq (u a + v a)| ≤ 2 * (1 - μ) := by
  set U := ∑ a, Complex.normSq (u a)
  set V := ∑ a, Complex.normSq (v a)
  set X := ∑ a, (u a * star (v a)).re
  have hsum : ∑ a, Complex.normSq (u a + v a) = U + V + 2 * X := by
    simp only [U, V, X, Complex.normSq_add, Finset.sum_add_distrib, ← Finset.mul_sum,
      Complex.star_def]
  have hX : |X| ≤ Real.sqrt U * Real.sqrt V := by
    have h1 : |X| ≤ ‖∑ a, u a * star (v a)‖ := by
      simp only [X, ← Complex.re_sum]
      exact Complex.abs_re_le_norm _
    have h2 := X7T_cs_sum u v
    rw [Complex.normSq_eq_norm_sq] at h2
    have h3 : ‖∑ a, u a * star (v a)‖ ≤ Real.sqrt (U * V) :=
      Real.le_sqrt_of_sq_le h2
    rw [Real.sqrt_mul (Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _)] at h3
    linarith
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _
  have hsU : Real.sqrt U ≤ μ := Real.sqrt_le_iff.mpr ⟨hμ0, hu⟩
  have hsV : Real.sqrt V ≤ 1 - μ := Real.sqrt_le_iff.mpr ⟨by linarith, hv⟩
  have hXb : |X| ≤ μ * (1 - μ) :=
    hX.trans (mul_le_mul hsU hsV (Real.sqrt_nonneg _) hμ0)
  rw [hsum]
  rcases abs_le.mp hXb with ⟨hX1, hX2⟩
  rw [abs_le]
  constructor <;> nlinarith [hX1, hX2, hv, hV0, hW, hW0, hμ1, hμ0]

theorem X7L8_comp {I : Type*} [Fintype I] {ma mg : ℕ} (A C : Superop I I)
    (AK : Fin ma → Matrix I I ℂ) (GK : Fin mg → Matrix I I ℂ) (P : Matrix I I ℂ) (hPh : Pᴴ = P)
    (hA : ∀ X, A X = krausApply AK X) (hC : ∀ X, C X = P * X * P + krausApply GK X)
    (X : Matrix I I ℂ) :
    (A ∘ C) X = krausApply (fun q : Fin ma × Fin (mg + 1) =>
      AK q.1 * (Fin.cons P GK : Fin (mg + 1) → Matrix I I ℂ) q.2) X := by
  simp only [Function.comp, hA, hC, krausApply, Fintype.sum_prod_type, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul]
  refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun g _ => ?_)
  · rw [Matrix.conjTranspose_mul, hPh]; simp only [Matrix.mul_assoc]
  · rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]

theorem X7L8_main (S : BlockQuantumSource) (window : ℝ) (n : ℕ)
    (C A : Superop (SourceRegister S.dimension n) (SourceRegister S.dimension n))
    (hC : IsCompression (qaepSpectralProjector S window n) C) (hA : IsChannel A) :
    |fe (S.rho n) (A ∘ C) - fe (S.rho n) A| ≤
      2 * (1 - qaepRetainedMass S window n) := by
  have hρ := S.density n
  have hP : qaepSpectralProjector S window n * qaepSpectralProjector S window n =
        qaepSpectralProjector S window n ∧
      (qaepSpectralProjector S window n)ᴴ = qaepSpectralProjector S window n ∧
      qaepSpectralProjector S window n * S.rho n = S.rho n * qaepSpectralProjector S window n := by
    unfold qaepSpectralProjector
    exact X7T_proj (S.rho n) hρ.1.1 _ (fun x => by split_ifs <;> simp)
  set P := qaepSpectralProjector S window n with hPdef
  set ρ := S.rho n with hρdef
  obtain ⟨hPP, hPh, hPc⟩ := hP
  set α := P * ρ * P with hα
  set β := (1 - P) * ρ * (1 - P) with hβ
  have h1 : α = ρ * P := by rw [hα, hPc, Matrix.mul_assoc, hPP]
  have h2 : β = ρ - ρ * P := by
    rw [hβ, Matrix.sub_mul, Matrix.one_mul, hPc, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
      Matrix.mul_assoc, hPP]
    abel
  have hαβ : α + β = ρ := by rw [h1, h2]; abel
  have hαpsd : α.PosSemidef := by
    have := hρ.1.mul_mul_conjTranspose_same P
    rwa [hPh] at this
  have hβpsd : β.PosSemidef := by
    have := hρ.1.mul_mul_conjTranspose_same (1 - P)
    rwa [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh] at this
  set μ := qaepRetainedMass S window n with hμ
  have hμα : μ = α.trace.re := rfl
  have htr : α.trace.re + β.trace.re = 1 := by
    rw [← Complex.add_re, ← Matrix.trace_add, hαβ, hρ.2, Complex.one_re]
  have hβ0 : 0 ≤ β.trace.re := (Complex.nonneg_iff.mp hβpsd.trace_nonneg).1
  have hα0 : 0 ≤ α.trace.re := (Complex.nonneg_iff.mp hαpsd.trace_nonneg).1
  have hμ1 : μ ≤ 1 := by linarith
  have hμ0 : 0 ≤ μ := hα0
  -- structure of the compression
  obtain ⟨⟨mc, CK, hCK, hCKe⟩, ⟨Gm, ⟨L, hL, hcp⟩, hG⟩, -⟩ := hC
  obtain ⟨mg, GK, hGK⟩ := X7P29_kraus L hcp
  have hGe : ∀ X, Gm X = krausApply GK X := fun X => by rw [← hL, hGK]
  have hCX : ∀ X, C X = P * X * P + krausApply GK X := fun X => by
    rw [hG, hGe]; simp [conjSuperop, hPh]
  have hsumG : P + ∑ g, (GK g)ᴴ * GK g = 1 := by
    have key : ∀ X, ((P + ∑ g, (GK g)ᴴ * GK g - 1) * X).trace = 0 := by
      intro X
      have e1 := congrArg Matrix.trace (hCX X)
      rw [hCKe, X7L8_kraus_trace, hCK, Matrix.one_mul, Matrix.trace_add, X7L8_kraus_trace] at e1
      have e2 : (P * X * P).trace = (P * X).trace := by
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPP]
      rw [e2] at e1
      rw [Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_add, ← e1]
      ring
    have := X7L8_tr_zero _ key
    rwa [sub_eq_zero] at this
  have hGP : ∀ g, GK g * P = 0 := by
    have h0 : ∑ g, (GK g * P)ᴴ * (GK g * P) = 0 := by
      have : P * (P + ∑ g, (GK g)ᴴ * GK g) * P = P := by rw [hsumG, Matrix.mul_one, hPP]
      rw [Matrix.mul_add, Matrix.add_mul, hPP, hPP, Matrix.mul_sum, Matrix.sum_mul] at this
      have h' : ∑ g, P * ((GK g)ᴴ * GK g) * P = 0 := by
        have := congrArg (fun M => M - P) this
        simpa using this
      rw [← h']
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Matrix.conjTranspose_mul, hPh]
      simp only [Matrix.mul_assoc]
    exact fun g => X7L8_sum_zero _ h0 g
  have hGρ : ∀ g, GK g * ρ = GK g * β := by
    intro g
    rw [h2, Matrix.mul_sub, ← hPc, ← Matrix.mul_assoc, hGP g, Matrix.zero_mul, sub_zero]
  -- Kraus forms
  obtain ⟨ma, AK, hAK, hAKe⟩ := hA
  let KC : Fin (mg + 1) → Matrix (SourceRegister S.dimension n) (SourceRegister S.dimension n) ℂ :=
    Fin.cons P GK
  have hcomp : ∀ X, (A ∘ C) X = krausApply (fun q : Fin ma × Fin (mg + 1) => AK q.1 * KC q.2) X :=
    X7L8_comp A C AK GK P hPh hAKe hCX
  let u : Fin ma → ℂ := fun a => (AK a * α).trace
  let v : Fin ma → ℂ := fun a => (AK a * β).trace
  have hfeA : fe ρ A = ∑ a, Complex.normSq (u a + v a) := by
    rw [X7P29_fe ρ A AK hAKe]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [u, v]
    rw [← Matrix.trace_add, ← Matrix.mul_add, hαβ]
  set Wt : ℝ := ∑ a, ∑ g, Complex.normSq (AK a * GK g * β).trace with hWt
  have hfeAC : fe ρ (A ∘ C) = ∑ a, Complex.normSq (u a) + Wt := by
    rw [X7P29_fe ρ (A ∘ C) _ hcomp, Fintype.sum_prod_type, hWt, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.sum_univ_succ]
    simp only [KC, Fin.cons_zero, Fin.cons_succ, u]
    have e1 : (AK a * P * ρ).trace = (AK a * α).trace := by rw [Matrix.mul_assoc, hPc, ← h1]
    have e2 : ∀ g, (AK a * GK g * ρ).trace = (AK a * GK g * β).trace := fun g => by
      rw [Matrix.mul_assoc, hGρ g, ← Matrix.mul_assoc]
    rw [e1]
    simp only [e2]
  have hu : ∑ a, Complex.normSq (u a) ≤ μ ^ 2 := by
    rw [hμα]; exact X7T_fe_le AK hAK α hαpsd
  have hv : ∑ a, Complex.normSq (v a) ≤ (1 - μ) ^ 2 := by
    have : 1 - μ = β.trace.re := by rw [hμα]; linarith
    rw [this]; exact X7T_fe_le AK hAK β hβpsd
  have hW0 : 0 ≤ Wt := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun g _ =>
    Complex.normSq_nonneg _
  have hW : Wt ≤ (1 - μ) ^ 2 := by
    have hb : 1 - μ = β.trace.re := by rw [hμα]; linarith
    have hP1 : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
    have hPβ : P * β = 0 := by
      rw [hβ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP1, Matrix.zero_mul, Matrix.zero_mul]
    have hAK' : ∑ a, (AK a)ᴴ * AK a = 1 := hAK
    have key : ∀ g, ∑ a, ((AK a * GK g)ᴴ * (AK a * GK g) * β) = (GK g)ᴴ * GK g * β := by
      intro g
      simp only [Matrix.conjTranspose_mul]
      calc ∑ a, (GK g)ᴴ * (AK a)ᴴ * (AK a * GK g) * β
          = ∑ a, (GK g)ᴴ * ((AK a)ᴴ * AK a) * GK g * β := by simp only [Matrix.mul_assoc]
        _ = (GK g)ᴴ * (∑ a, (AK a)ᴴ * AK a) * GK g * β := by
            rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_mul]
        _ = _ := by rw [hAK', Matrix.mul_one]
    calc Wt ≤ ∑ a, ∑ g, β.trace.re * ((AK a * GK g)ᴴ * (AK a * GK g) * β).trace.re :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun g _ => X7T_cs _ _ hβpsd
      _ = β.trace.re * ((∑ g, (GK g)ᴴ * GK g) * β).trace.re := by
          rw [Finset.sum_comm]
          simp only [← Finset.mul_sum]
          congr 1
          rw [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [← key g, Matrix.trace_sum, Complex.re_sum]
      _ = (1 - μ) ^ 2 := by
          have : (∑ g, (GK g)ᴴ * GK g) = 1 - P := by rw [← hsumG]; abel
          rw [this, Matrix.sub_mul, Matrix.one_mul, hPβ, sub_zero, hb, sq]
  rw [hfeAC, hfeA]
  exact X7L8_alg (k := 0) u v Wt μ hμ0 hμ1 hu hv hW0 hW

end QAlgorithms.Papers.Independent.Gap48.P29

end

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P29 in
theorem solution (S : BlockQuantumSource) (hS : QAEP S)
    (window : ℝ) (hwindow : 0 < window) (n : ℕ) (hn : 0 < n)
    (C A : Superop (SourceRegister S.dimension n) (SourceRegister S.dimension n))
    (hC : IsCompression (qaepSpectralProjector S window n) C) (hA : IsChannel A) :
    |fe (S.rho n) (A ∘ C) - fe (S.rho n) A| ≤
      2 * (1 - qaepRetainedMass S window n) :=
  QAlgorithms.Papers.Independent.Gap48.P29.X7L8_main S window n C A hC hA
