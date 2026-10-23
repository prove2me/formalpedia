-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.ghzExactRobustness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T04:37:52.416502+00:00
-- url     : https://prove2.me/submissions/a1c3c2c0-3a43-4171-acba-ef47cd09848e

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_ghzWitnessBounds
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_fullySeparablePhaseMixtures
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

lemma x8r_ket (n : ℕ) (b : Bool) (x : Fin n → Fin 2) :
    constantKet n b x = if x = (fun _ => if b then 1 else 0) then 1 else 0 := by
  simp [constantKet, QAlgorithms.ket, PiLp.single_apply]

lemma x8r_conj (n : ℕ) (b : Bool) (x : Fin n → Fin 2) :
    conj (constantKet n b x) = constantKet n b x := by
  rw [x8r_ket]; split_ifs <;> simp

lemma x8r_ne (n : ℕ) (hn : 1 ≤ n) : (fun _ : Fin n => (0 : Fin 2)) ≠ (fun _ => 1) := by
  intro h; have := congrFun h ⟨0, hn⟩; simp at this

lemma x8r_tr_vv {I : Type*} [Fintype I] (a b : I → ℂ) :
    (Matrix.vecMulVec a (star a) * Matrix.vecMulVec b (star b)).trace =
      ((Complex.normSq (∑ k, star (a k) * b k) : ℝ) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [Matrix.trace, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.diag, map_sum, map_mul,
    Pi.star_apply, RCLike.star_def, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

lemma x8r_tr_psd {I : Type*} [Fintype I] {A B : Op I} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  obtain ⟨n, w, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hB
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, x8r_tr_vv, Complex.re_sum,
    Complex.ofReal_re]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

/-- GHZ density as a combination of `ghzE` and `ghzC`. -/
lemma x8r_ghz (n : ℕ) (b : Bool) :
    ghz n b = ((1/2 : ℝ) : ℂ) • (ghzE n + (if b then 1 else (-1 : ℂ)) • ghzC n) := by
  have hs : ((Real.sqrt 2)⁻¹ : ℂ) * conj ((Real.sqrt 2)⁻¹ : ℂ) = ((1/2 : ℝ) : ℂ) := by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    push_cast; ring
  ext x y
  simp only [ghz, ghzKet, proj, QAlgorithms.pureDensity, Matrix.of_apply, PiLp.smul_apply,
    PiLp.add_apply, smul_eq_mul, map_mul, map_add, Matrix.smul_apply, Matrix.add_apply,
    ghzE, ghzC, x8r_conj]
  cases b
  · simp only [Bool.false_eq_true, if_false, map_neg, map_one]
    linear_combination (constantKet n false x - constantKet n true x) *
      (constantKet n false y - constantKet n true y) * hs
  · simp only [if_true, map_one]
    linear_combination (constantKet n false x + constantKet n true x) *
      (constantKet n false y + constantKet n true y) * hs

lemma x8r_trE (n : ℕ) (hn : 1 ≤ n) : (ghzE n).trace = 2 := by
  have h := x8r_ne n hn
  simp only [ghzE, proj, QAlgorithms.pureDensity, Matrix.trace, Matrix.diag, Matrix.add_apply,
    Matrix.of_apply, x8r_ket]
  simp [Finset.sum_add_distrib, ite_mul, Finset.sum_ite_eq']
  norm_num

lemma x8r_trC (n : ℕ) (hn : 1 ≤ n) : (ghzC n).trace = 0 := by
  have h := x8r_ne n hn
  simp only [ghzC, Matrix.trace, Matrix.diag, x8r_ket]
  simp [Finset.sum_add_distrib, ite_mul, Finset.sum_ite_eq', h, Ne.symm h]

lemma x8r_psd_proj {I : Type*} [Fintype I] (v : Vec I) : (proj v).PosSemidef := by
  have : proj v = Matrix.vecMulVec (⇑v) (star ⇑v) := by
    ext x y; simp [proj, QAlgorithms.pureDensity, Matrix.vecMulVec]
  rw [this]
  exact Matrix.posSemidef_vecMulVec_self_star _

lemma x8r_ghz_density (n : ℕ) (hn : 1 ≤ n) (b : Bool) : QAlgorithms.IsDensityMatrix (ghz n b) := by
  refine ⟨x8r_psd_proj _, ?_⟩
  rw [x8r_ghz, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul, x8r_trE n hn,
    x8r_trC n hn]
  norm_num

/-- The constant kets are product kets. -/
lemma x8r_const_prod (n : ℕ) (b : Bool) :
    constantKet n b = productKet (d := fun _ : Fin n => 2)
      (fun _ => QAlgorithms.ket (if b then (1 : Fin 2) else 0)) := by
  ext x
  rw [x8r_ket]
  simp only [productKet, QAlgorithms.ket, PiLp.single_apply]
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma x8r_const_fs (n : ℕ) (b : Bool) : proj (constantKet n b) ∈ fs (fun _ : Fin n => 2) := by
  apply subset_convexHull
  refine ⟨fun _ => QAlgorithms.ket (if b then (1 : Fin 2) else 0), fun _ => ?_, ?_⟩
  · simp [QAlgorithms.ket]
  · rw [x8r_const_prod]

lemma x8r_fs_density {n : ℕ} (X : Op (Fin n → Fin 2)) (hX : X ∈ fs (fun _ : Fin n => 2)) :
    QAlgorithms.IsDensityMatrix X := by
  have hsub : fs (fun _ : Fin n => 2) ⊆ {X | QAlgorithms.IsDensityMatrix X} := by
    refine convexHull_min ?_ ?_
    · rintro X ⟨v, hv, rfl⟩
      refine ⟨x8r_psd_proj _, ?_⟩
      have : ‖productKet (d := fun _ : Fin n => 2) v‖ = 1 := by
        rw [EuclideanSpace.norm_eq]
        have hsw := Finset.sum_prod_piFinset (Finset.univ : Finset (Fin 2))
          (fun j b => ‖v j b‖ ^ 2)
        simp only [Fintype.piFinset_univ] at hsw
        simp only [productKet, norm_prod, ← Finset.prod_pow]
        rw [hsw]
        have : ∀ j, ∑ b, ‖v j b‖ ^ 2 = 1 := fun j => by
          rw [← EuclideanSpace.norm_sq_eq, hv j, one_pow]
        simp [this]
      simp only [Matrix.trace, Matrix.diag, proj, QAlgorithms.pureDensity, Matrix.of_apply,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [← Complex.ofReal_sum, ← EuclideanSpace.norm_sq_eq, this]; simp
    · intro X hX Y hY a b ha hb hab
      refine ⟨(hX.1.smul (by exact_mod_cast ha)).add (hY.1.smul (by exact_mod_cast hb)), ?_⟩
      rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hX.2, hY.2]
      simp only [smul_eq_mul, mul_one, Complex.real_smul, Complex.ofReal_one]
      exact_mod_cast hab
  exact hsub hX

lemma x8r_trproj {n : ℕ} (b : Bool) (σ : Op (Fin n → Fin 2)) :
    (proj (constantKet n b) * σ).trace =
      σ (fun _ => if b then 1 else 0) (fun _ => if b then 1 else 0) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, proj, QAlgorithms.pureDensity,
    Matrix.of_apply, x8r_ket]
  simp [ite_mul, Finset.sum_ite_eq']

lemma x8r_trC' {n : ℕ} (σ : Op (Fin n → Fin 2)) :
    (ghzC n * σ).trace = σ (fun _ => 1) (fun _ => 0) + σ (fun _ => 0) (fun _ => 1) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, ghzC, x8r_ket]
  simp [add_mul, ite_mul, Finset.sum_add_distrib, Finset.sum_ite_eq']

lemma x8r_trZ {n : ℕ} (σ : Op (Fin n → Fin 2)) :
    (ghzZ n * σ).trace = (((2^n:ℝ)/(2*((2^n:ℝ)-2)) : ℝ) : ℂ) *
      (σ.trace - σ (fun _ => 0) (fun _ => 0) - σ (fun _ => 1) (fun _ => 1)) -
      (((2^n:ℝ)/4 : ℝ) : ℂ) * (σ (fun _ => 1) (fun _ => 0) + σ (fun _ => 0) (fun _ => 1)) := by
  simp only [ghzZ, ghzE, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, x8r_trproj, x8r_trC', smul_eq_mul]
  simp only [Bool.false_eq_true, if_false, if_true]
  push_cast
  ring

lemma x8r_trZ_ghz (n : ℕ) (hn : 2 ≤ n) : (ghzZ n * ghz n true).trace.re = -((2^n : ℝ) / 4) := by
  have h := x8r_ne n (by omega)
  have htr : (ghz n true).trace = 1 := (x8r_ghz_density n (by omega) true).2
  rw [x8r_trZ, htr]
  simp only [x8r_ghz, Matrix.smul_apply, Matrix.add_apply, ghzE, ghzC, proj,
    QAlgorithms.pureDensity, Matrix.of_apply, x8r_ket, if_true, one_smul]
  simp [h, Ne.symm h]
  have h2 : ((2:ℂ)^n).re = 2^n := by
    rw [show ((2:ℂ)^n) = ((2^n : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  rw [h2]; ring

lemma x8r_trmix {I : Type*} [Fintype I] (A ρ ω : Op I) (s : ℝ) :
    (A * mix ρ ω s).trace.re = (1 + s)⁻¹ * ((A * ρ).trace.re + s * (A * ω).trace.re) := by
  simp only [mix, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add,
    smul_eq_mul, Complex.re_ofReal_mul, Complex.add_re]

lemma x8r_smul_real {I : Type*} (r : ℝ) (M : Op I) : ((r : ℂ) • M) = r • M := by
  ext x y; simp [Complex.real_smul]

lemma x8r_Q_fs (n : ℕ) :
    ((1/2 : ℝ) : ℂ) • ghzE n ∈ fs (fun _ : Fin n => 2) := by
  have := convex_convexHull ℝ _ (x8r_const_fs n false) (x8r_const_fs n true)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  rw [x8r_smul_real, ghzE, smul_add]
  exact this

lemma x8r_gen_mem (n : ℕ) (hn : 1 ≤ n) :
    mix (ghz n true) (ghz n false) 1 ∈ fs (fun _ : Fin n => 2) := by
  have h : mix (ghz n true) (ghz n false) 1 = ((1/2 : ℝ) : ℂ) • ghzE n := by
    rw [mix, x8r_ghz, x8r_ghz]
    ext x y
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Bool.false_eq_true, if_true,
      if_false]
    push_cast
    ring
  rw [h]; exact x8r_Q_fs n

lemma x8r_std_mem (n : ℕ) (hn : 2 ≤ n) :
    mix (ghz n true) (phaseMixture n false) ((2:ℝ)^(n-2)) ∈ fs (fun _ : Fin n => 2) := by
  set s : ℝ := (2:ℝ)^(n-2) with hs
  have hs0 : 0 < s := by positivity
  have hq : s * ((2:ℝ)^n)⁻¹ = 1/4 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [hs, show m + 2 - 2 = m by omega, pow_add]; field_simp; norm_num
  have hqC : ((s * ((2:ℝ)^n)⁻¹ : ℝ) : ℂ) = 1/4 := by rw [hq]; norm_num
  have hfs := (fullySeparablePhaseMixtures n hn).1
  have hcomb := convex_convexHull ℝ _ hfs (x8r_Q_fs n)
    (by positivity : (0:ℝ) ≤ s / (1 + s)) (by positivity : (0:ℝ) ≤ 1 / (1 + s))
    (by field_simp; ring)
  convert hcomb using 1
  · rfl
  unfold mix
  rw [x8r_ghz, phaseMixture, phaseMixture, x8r_smul_real, x8r_smul_real]
  ext x y
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Bool.false_eq_true, if_true,
    if_false, Complex.real_smul, Matrix.one_apply]
  have h1 : (1 + (s:ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (1 + s) ≠ 0)
  push_cast at hqC ⊢
  linear_combination (-2 * (1 + (s:ℂ))⁻¹ * ghzC n x y) * hqC

lemma x8r_trZg (n : ℕ) (σ : Op (Fin n → Fin 2)) :
    (ghzZg n * σ).trace.re = ((2^n : ℝ) / 4)⁻¹ * (ghzZ n * σ).trace.re := by
  simp only [ghzZg, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [show ((((2:ℝ)^n : ℝ) : ℂ) / 4)⁻¹ = ((((2:ℝ)^n) / 4)⁻¹ : ℝ) by push_cast; ring,
    Complex.re_ofReal_mul]

theorem x8r_main (n : ℕ) (hn : 2 ≤ n) :
    fsR (fun _ : Fin n => 2) false (ghz n true) = 1 ∧
    fsR (fun _ : Fin n => 2) true (ghz n true) = (2:ℝ)^(n-2) := by
  obtain ⟨hZ, hZg, hW, hPSD⟩ := ghzWitnessBounds n hn
  have hρ := x8r_trZ_ghz n hn
  have hpow : (2:ℝ)^(n-2) = (2^n : ℝ) / 4 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [show m + 2 - 2 = m by omega, pow_add]; norm_num
  have hP : (0:ℝ) < (2^n : ℝ) / 4 := by positivity
  constructor
  · unfold fsR robust
    apply IsLeast.csInf_eq
    refine ⟨⟨zero_le_one, ghz n false, by convert x8r_ghz_density n (by omega) false,
      fun h => absurd h (by simp), x8r_gen_mem n (by omega)⟩, ?_⟩
    rintro s ⟨hs, ω, hω, -, hmem⟩
    have h0 := (hW _ hmem).2.2
    rw [x8r_trmix, x8r_trZg, x8r_trZg, hρ] at h0
    have ht : (ghzZg n * ω).trace.re ≤ 1 := by
      have := x8r_tr_psd hPSD hω.1
      have htr : ω.trace = 1 := by convert hω.2
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, htr] at this
      simpa using this
    rw [x8r_trZg] at ht
    have h1 : 0 ≤ -1 + s * (((2^n : ℝ) / 4)⁻¹ * (ghzZ n * ω).trace.re) := by
      have h2 : (0:ℝ) < (1 + s)⁻¹ := by positivity
      have := nonneg_of_mul_nonneg_right (by linarith [h0] : 0 ≤ (1 + s)⁻¹ *
        (((2^n : ℝ) / 4)⁻¹ * -((2^n : ℝ) / 4) + s * (((2^n : ℝ) / 4)⁻¹ * (ghzZ n * ω).trace.re))) h2
      rwa [show ((2^n : ℝ) / 4)⁻¹ * -((2^n : ℝ) / 4) = -1 by field_simp] at this
    nlinarith
  · unfold fsR robust
    apply IsLeast.csInf_eq
    refine ⟨⟨by positivity, phaseMixture n false,
      by convert x8r_fs_density _ (fullySeparablePhaseMixtures n hn).2,
      fun _ => (fullySeparablePhaseMixtures n hn).2, x8r_std_mem n hn⟩, ?_⟩
    rintro s ⟨hs, ω, hω, hωF, hmem⟩
    have h0 := (hW _ hmem).1
    rw [x8r_trmix, hρ] at h0
    have ht := (hW _ (hωF rfl)).2.1
    have h2 : (0:ℝ) < (1 + s)⁻¹ := by positivity
    have h1 := nonneg_of_mul_nonneg_right h0 h2
    rw [hpow]; nlinarith [mul_le_mul_of_nonneg_left ht hs]

end QAlgorithms.Papers.Independent.Information100.P21

open QAlgorithms.Papers.Independent.Information100.P21 in
theorem solution (n : ℕ) (hn : 2≤n) :
  fsR (fun _ : Fin n => 2) false (ghz n true)=1 ∧
  fsR (fun _ : Fin n => 2) true (ghz n true)=(2:ℝ)^(n-2) := x8r_main n hn
