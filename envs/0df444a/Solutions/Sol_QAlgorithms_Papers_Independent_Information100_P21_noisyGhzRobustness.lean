-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.noisyGhzRobustness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T12:14:34.859876+00:00
-- url     : https://prove2.me/submissions/54a288cd-f122-41a6-8877-4a5356bb3727

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

/-! ## Noisy GHZ -/

lemma x8g_val {I : Type*} {_ : Fintype I} {F : Set (Op I)} {std : Bool} {ρ : Op I} {v : ℝ}
    (hv0 : 0 ≤ v)
    (hfeas : ∃ ω : Op I, QAlgorithms.IsDensityMatrix ω ∧ (std = true → ω ∈ F) ∧ mix ρ ω v ∈ F)
    (hlb : ∀ (s : ℝ) (ω : Op I), 0 ≤ s → QAlgorithms.IsDensityMatrix ω → (std = true → ω ∈ F) →
      mix ρ ω s ∈ F → v ≤ s) :
    robust F std ρ = v := by
  unfold robust
  apply IsLeast.csInf_eq
  refine ⟨⟨hv0, hfeas⟩, ?_⟩
  rintro s ⟨hs, ω, hω, hωF, hmem⟩
  exact hlb s ω hs hω hωF hmem

lemma x8g_lb {I : Type*} [Fintype I] (W ρ ω : Op I) {s : ℝ} (hs : 0 ≤ s)
    (h0 : 0 ≤ (W * mix ρ ω s).trace.re) (h1 : (W * ω).trace.re ≤ 1) :
    -(W * ρ).trace.re ≤ s := by
  rw [x8r_trmix] at h0
  have h2 : (0:ℝ) < (1 + s)⁻¹ := by positivity
  have h3 := nonneg_of_mul_nonneg_right h0 h2
  nlinarith [mul_le_mul_of_nonneg_left h1 hs]

/-- Convex combinations of the three basic fully separable states. -/
lemma x8g_mem (n : ℕ) (hn : 2 ≤ n) {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x + y + z = 1) :
    (x : ℂ) • phaseMixture n true + (y : ℂ) • phaseMixture n false +
      (z : ℂ) • (((1/2 : ℝ) : ℂ) • ghzE n) ∈ fs (fun _ : Fin n => 2) := by
  have hc := (convex_convexHull ℝ _).sum_mem (t := (Finset.univ : Finset (Fin 3)))
    (w := ![x, y, z]) (z := ![phaseMixture n true, phaseMixture n false, ((1/2 : ℝ) : ℂ) • ghzE n])
    (by intro i _; fin_cases i <;> simp [hx, hy, hz])
    (by simp [Fin.sum_univ_three, h])
    (by
      intro i _
      fin_cases i
      · exact (fullySeparablePhaseMixtures n hn).1
      · exact (fullySeparablePhaseMixtures n hn).2
      · exact x8r_Q_fs n)
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
  rw [x8r_smul_real x, x8r_smul_real y, x8r_smul_real z]
  exact hc

/-- Normal form `a·I + b·C + c·E`. -/
def x8N (n : ℕ) (a b c : ℝ) : Op (Fin n → Fin 2) :=
  (a : ℂ) • (1 : Op (Fin n → Fin 2)) + (b : ℂ) • ghzC n + (c : ℂ) • ghzE n

lemma x8N_add (n : ℕ) (a b c a' b' c' : ℝ) :
    x8N n a b c + x8N n a' b' c' = x8N n (a + a') (b + b') (c + c') := by
  unfold x8N; push_cast; module

lemma x8N_smul (n : ℕ) (r a b c : ℝ) :
    (r : ℂ) • x8N n a b c = x8N n (r * a) (r * b) (r * c) := by
  unfold x8N; push_cast; module

lemma x8N_mix (n : ℕ) (a b c a' b' c' s : ℝ) :
    mix (x8N n a b c) (x8N n a' b' c') s =
      x8N n ((1 + s)⁻¹ * (a + s * a')) ((1 + s)⁻¹ * (b + s * b')) ((1 + s)⁻¹ * (c + s * c')) := by
  unfold mix
  rw [x8N_smul n s, x8N_add, x8N_smul]

lemma x8N_congr (n : ℕ) {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') :
    x8N n a b c = x8N n a' b' c' := by rw [ha, hb, hc]

lemma x8N_noisy (n : ℕ) (p : ℝ) :
    noisyGHZ n p = x8N n (p / 2^n) ((1 - p) / 2) ((1 - p) / 2) := by
  unfold noisyGHZ x8N
  rw [x8r_ghz]
  simp only [if_true, one_smul]
  push_cast; module

lemma x8N_ghzm (n : ℕ) : ghz n false = x8N n 0 (-1/2) (1/2) := by
  unfold x8N
  rw [x8r_ghz]
  simp only [Bool.false_eq_true, if_false]
  push_cast; module

lemma x8N_sp (n : ℕ) : phaseMixture n true = x8N n (1 / 2^n) (1 / 2^n) 0 := by
  unfold phaseMixture x8N
  simp only [if_true, one_smul]
  push_cast; module

lemma x8N_sm (n : ℕ) : phaseMixture n false = x8N n (1 / 2^n) (-1 / 2^n) 0 := by
  unfold phaseMixture x8N
  simp only [Bool.false_eq_true, if_false]
  push_cast; module

lemma x8N_comb (n : ℕ) (x y z : ℝ) :
    (x : ℂ) • phaseMixture n true + (y : ℂ) • phaseMixture n false +
      (z : ℂ) • (((1/2 : ℝ) : ℂ) • ghzE n) = x8N n ((x + y) / 2^n) ((x - y) / 2^n) (z / 2) := by
  rw [x8N_sp, x8N_sm, x8N_smul, x8N_smul, x8N_add]
  unfold x8N; push_cast; module

/-- Membership criterion for normal forms. -/
lemma x8N_mem (n : ℕ) (hn : 2 ≤ n) {a b c : ℝ} (hc : 0 ≤ c) (hb : |b| ≤ a)
    (h : 2^n * a + 2 * c = 1) : x8N n a b c ∈ fs (fun _ : Fin n => 2) := by
  have hD : (0:ℝ) < 2^n := by positivity
  have := x8g_mem n hn (x := 2^n * (a + b) / 2) (y := 2^n * (a - b) / 2) (z := 2 * c)
    (div_nonneg (mul_nonneg hD.le (by linarith [neg_abs_le b])) (by norm_num))
    (div_nonneg (mul_nonneg hD.le (by linarith [le_abs_self b])) (by norm_num)) (by linarith)
    (by linarith)
  rw [x8N_comb] at this
  convert this using 1
  apply x8N_congr <;> field_simp <;> ring

lemma x8N_trZ (n : ℕ) (hn : 2 ≤ n) (a b c : ℝ) :
    (ghzZ n * x8N n a b c).trace.re = 2^n * (a - b) / 2 := by
  have h := x8r_ne n (by omega)
  have htr : (x8N n a b c).trace = ((a * 2^n + 2 * c : ℝ) : ℂ) := by
    unfold x8N
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
      x8r_trC n (by omega), x8r_trE n (by omega), Matrix.trace_one]
    simp; ring
  have hD : (2:ℝ)^n - 2 ≠ 0 := by
    have : (4:ℝ) ≤ 2^n := by
      calc (4:ℝ) = 2^2 := by norm_num
        _ ≤ 2^n := pow_le_pow_right₀ (by norm_num) hn
    linarith
  have hD' : (2:ℂ)^n - 2 ≠ 0 := by exact_mod_cast hD
  have key : (ghzZ n * x8N n a b c).trace = ((2^n * (a - b) / 2 : ℝ) : ℂ) := by
    rw [x8r_trZ, htr]
    simp only [x8N, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, ghzE, ghzC, proj,
      QAlgorithms.pureDensity, Matrix.of_apply, x8r_ket, smul_eq_mul, Matrix.add_apply]
    simp only [h, Ne.symm h, if_true, if_false, Bool.false_eq_true, map_zero, map_one]
    push_cast
    field_simp
    ring
  rw [key, Complex.ofReal_re]

lemma x8N_tr (n : ℕ) (hn : 1 ≤ n) (a b c : ℝ) :
    (x8N n a b c).trace = ((a * 2^n + 2 * c : ℝ) : ℂ) := by
  unfold x8N
  rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
    x8r_trC n hn, x8r_trE n hn, Matrix.trace_one]
  simp; ring

lemma x8g_mix_self {I : Type*} (ρ : Op I) : mix ρ ρ 0 = ρ := by
  unfold mix; simp

lemma x8N_mem' (n : ℕ) (hn : 2 ≤ n) {a b c : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b) (hba : b ≤ a)
    (h : 2^n * a + 2 * c = 1) : x8N n a b c ∈ fs (fun _ : Fin n => 2) :=
  x8N_mem n hn hc (by rw [abs_of_nonneg hb]; exact hba) h

lemma x8g_D (n : ℕ) (hn : 2 ≤ n) : (4:ℝ) ≤ 2^n :=
  calc (4:ℝ) = 2^2 := by norm_num
    _ ≤ 2^n := pow_le_pow_right₀ (by norm_num) hn

theorem x8g_main (n : ℕ) (hn : 2≤n) (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) :
  QAlgorithms.IsDensityMatrix (noisyGHZ n p) ∧
  fsR (fun _ : Fin n => 2) false (noisyGHZ n p)=max 0 (1-p-2*p/(2^n:ℝ)) ∧
  fsR (fun _ : Fin n => 2) true (noisyGHZ n p)=max 0 ((2^n:ℝ)*(1-p)/4-p/2) ∧
  fsR (fun _ : Fin n => 2) true (noisyGHZ n p)=
    (2:ℝ)^(n-2)*fsR (fun _ : Fin n => 2) false (noisyGHZ n p) ∧
  (noisyGHZ n p∈fs (fun _ : Fin n => 2) ↔ (2^n:ℝ)/((2^n:ℝ)+2)≤p) ∧
  (0<p → (noisyGHZ n p).PosDef ∧ (noisyGHZ n p-(p/(2^n:ℝ):ℂ) • 1).PosSemidef) ∧
  (3≤n → 0<p → p<(2^n:ℝ)/((2^n:ℝ)+2) →
    fsR (fun _ : Fin n => 2) false (noisyGHZ n p)<fsR (fun _ : Fin n => 2) true (noisyGHZ n p)) := by
  obtain ⟨hZ, hZg, hW, hPSD⟩ := ghzWitnessBounds n hn
  have hD4 := x8g_D n hn
  have hD0 : (0:ℝ) < 2^n := by positivity
  have hpow : (2:ℝ)^(n-2) = 2^n / 4 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [show m + 2 - 2 = m by omega, pow_add]; norm_num
  have hρ := x8N_noisy n p
  -- density
  have hpsd : (noisyGHZ n p).PosSemidef := by
    unfold noisyGHZ
    refine Matrix.PosSemidef.add ((x8r_psd_proj _).smul ?_) (Matrix.PosSemidef.one.smul ?_)
    · rw [show (1 - (p:ℂ)) = ((1 - p : ℝ) : ℂ) by push_cast; ring]; exact_mod_cast (by linarith)
    · have : (0:ℝ) ≤ p / 2^n := div_nonneg hp0 hD0.le
      exact_mod_cast this
  have hdens : QAlgorithms.IsDensityMatrix (noisyGHZ n p) := by
    refine ⟨hpsd, ?_⟩
    rw [hρ, x8N_tr n (by omega)]
    have : p / 2^n * 2^n + 2 * ((1 - p) / 2) = (1:ℝ) := by field_simp; ring
    rw [this]; simp
  -- witness traces
  have htZ : (ghzZ n * noisyGHZ n p).trace.re = p / 2 - 2^n * (1 - p) / 4 := by
    rw [hρ, x8N_trZ n hn]; field_simp; ring
  have htZg : (ghzZg n * noisyGHZ n p).trace.re = 2 * p / 2^n - (1 - p) := by
    rw [x8r_trZg, htZ]; field_simp; ring
  have hZg1 : ∀ ω : Op (Fin n → Fin 2), QAlgorithms.IsDensityMatrix ω →
      (ghzZg n * ω).trace.re ≤ 1 := by
    intro ω hω
    have := x8r_tr_psd hPSD hω.1
    have htr : ω.trace = 1 := by convert hω.2
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, htr] at this
    simpa using this
  -- membership when the noise is large
  have hmemρ : 2^n * (1 - p) ≤ 2 * p → noisyGHZ n p ∈ fs (fun _ : Fin n => 2) := by
    intro h
    rw [hρ]
    refine x8N_mem' n hn (by linarith) (by linarith) ?_ (by field_simp; ring)
    rw [le_div_iff₀ hD0]; linarith
  -- generalized robustness
  have hgen : fsR (fun _ : Fin n => 2) false (noisyGHZ n p) = max 0 (1-p-2*p/2^n) := by
    unfold fsR
    apply x8g_val (le_max_left _ _)
    · rcases le_or_gt (1-p-2*p/2^n) 0 with h | h
      · rw [max_eq_left h]
        refine ⟨noisyGHZ n p, by convert hdens, fun h => absurd h (by simp), ?_⟩
        rw [x8g_mix_self]
        apply hmemρ
        have h' : 1 - p ≤ 2 * p / 2^n := by linarith
        rw [le_div_iff₀ hD0] at h'; linarith
      · rw [max_eq_right h.le]
        refine ⟨ghz n false, by convert x8r_ghz_density n (by omega) false,
          fun h => absurd h (by simp), ?_⟩
        rw [hρ, x8N_ghzm, x8N_mix]
        have hs1 : (0:ℝ) < 1 + (1-p-2*p/2^n) := by linarith
        have hba : (1 + (1-p-2*p/2^n))⁻¹ * ((1 - p) / 2 + (1-p-2*p/2^n) * (-1/2)) =
            (1 + (1-p-2*p/2^n))⁻¹ * (p / 2^n + (1-p-2*p/2^n) * 0) := by
          congr 1; field_simp; ring
        rw [hba]
        generalize 1-p-2*p/2^n = s at hs1 h ⊢
        apply x8N_mem' n hn
        · exact mul_nonneg (inv_nonneg.mpr hs1.le) (by linarith)
        · exact mul_nonneg (inv_nonneg.mpr hs1.le) (by simp; positivity)
        · exact le_rfl
        · field_simp [hs1.ne']; ring
    · intro s ω hs hω _ hmem
      apply max_le hs
      have := x8g_lb (ghzZg n) _ ω hs (hW _ hmem).2.2 (hZg1 ω (by convert hω))
      rw [htZg] at this; linarith
  -- standard robustness
  have hstd : fsR (fun _ : Fin n => 2) true (noisyGHZ n p) = max 0 (2^n*(1-p)/4-p/2) := by
    unfold fsR
    apply x8g_val (le_max_left _ _)
    · rcases le_or_gt (2^n*(1-p)/4-p/2) 0 with h | h
      · rw [max_eq_left h]
        have hm := hmemρ (by linarith)
        refine ⟨noisyGHZ n p, by convert hdens, fun _ => hm, ?_⟩
        rw [x8g_mix_self]; exact hm
      · rw [max_eq_right h.le]
        have hsm := (fullySeparablePhaseMixtures n hn).2
        refine ⟨phaseMixture n false, by convert x8r_fs_density _ hsm, fun _ => hsm, ?_⟩
        rw [hρ, x8N_sm, x8N_mix]
        have hs1 : (0:ℝ) < 1 + (2^n*(1-p)/4-p/2) := by linarith
        have hba : (1 + (2^n*(1-p)/4-p/2))⁻¹ * ((1 - p) / 2 + (2^n*(1-p)/4-p/2) * (-1 / 2^n)) =
            (1 + (2^n*(1-p)/4-p/2))⁻¹ * (p / 2^n + (2^n*(1-p)/4-p/2) * (1 / 2^n)) := by
          congr 1; field_simp; ring
        rw [hba]
        generalize 2^n*(1-p)/4-p/2 = s at hs1 h ⊢
        apply x8N_mem' n hn
        · exact mul_nonneg (inv_nonneg.mpr hs1.le) (by linarith)
        · exact mul_nonneg (inv_nonneg.mpr hs1.le) (by positivity)
        · exact le_rfl
        · field_simp [hs1.ne']; ring
    · intro s ω hs hω hωF hmem
      apply max_le hs
      have := x8g_lb (ghzZ n) _ ω hs (hW _ hmem).1 (hW _ (hωF rfl)).2.1
      rw [htZ] at this; linarith
  refine ⟨hdens, hgen, hstd, ?_, ?_, ?_, ?_⟩
  · rw [hstd, hgen, hpow, mul_max_of_nonneg _ _ (by positivity), mul_zero]
    congr 1; field_simp; ring
  · constructor
    · intro hm
      have h0 := (hW _ hm).2.2
      rw [htZg] at h0
      rw [div_le_iff₀ (by positivity)]
      have : 2^n * (1 - p) ≤ 2 * p := by
        have h' : 1 - p ≤ 2 * p / 2^n := by linarith
        rw [le_div_iff₀ hD0] at h'; linarith
      linarith
    · intro h
      rw [div_le_iff₀ (by positivity)] at h
      exact hmemρ (by linarith)
  · intro hp
    have hsub : noisyGHZ n p - (p/(2^n:ℝ):ℂ) • 1 = (1 - (p:ℂ)) • ghz n true := by
      unfold noisyGHZ; push_cast; abel
    refine ⟨?_, ?_⟩
    · unfold noisyGHZ
      refine Matrix.PosDef.posSemidef_add ((x8r_psd_proj _).smul ?_) (Matrix.PosDef.one.smul ?_)
      · rw [show (1 - (p:ℂ)) = ((1 - p : ℝ) : ℂ) by push_cast; ring]; exact_mod_cast (by linarith)
      · have : (0:ℝ) < p / 2^n := div_pos hp hD0
        exact_mod_cast this
    · rw [hsub]
      refine (x8r_psd_proj _).smul ?_
      rw [show (1 - (p:ℂ)) = ((1 - p : ℝ) : ℂ) by push_cast; ring]; exact_mod_cast (by linarith)
  · intro h3 hp hlt
    rw [hgen, hstd]
    rw [lt_div_iff₀ (by positivity)] at hlt
    have hpos : 0 < 1 - p - 2 * p / 2^n := by
      have : 2 * p / 2^n < 1 - p := by rw [div_lt_iff₀ hD0]; linarith
      linarith
    have hD8 : (8:ℝ) ≤ 2^n :=
      calc (8:ℝ) = 2^3 := by norm_num
        _ ≤ 2^n := pow_le_pow_right₀ (by norm_num) h3
    have e : 2^n*(1-p)/4-p/2 = 2^n / 4 * (1 - p - 2 * p / 2^n) := by field_simp; ring
    rw [max_eq_right hpos.le, e, max_eq_right (by positivity)]
    nlinarith

end QAlgorithms.Papers.Independent.Information100.P21

open QAlgorithms.Papers.Independent.Information100.P21 in
theorem solution (n : ℕ) (hn : 2≤n) (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) :
  QAlgorithms.IsDensityMatrix (noisyGHZ n p) ∧
  fsR (fun _ : Fin n => 2) false (noisyGHZ n p)=max 0 (1-p-2*p/(2^n:ℝ)) ∧
  fsR (fun _ : Fin n => 2) true (noisyGHZ n p)=max 0 ((2^n:ℝ)*(1-p)/4-p/2) ∧
  fsR (fun _ : Fin n => 2) true (noisyGHZ n p)=
    (2:ℝ)^(n-2)*fsR (fun _ : Fin n => 2) false (noisyGHZ n p) ∧
  (noisyGHZ n p∈fs (fun _ : Fin n => 2) ↔ (2^n:ℝ)/((2^n:ℝ)+2)≤p) ∧
  (0<p → (noisyGHZ n p).PosDef ∧ (noisyGHZ n p-(p/(2^n:ℝ):ℂ) • 1).PosSemidef) ∧
  (3≤n → 0<p → p<(2^n:ℝ)/((2^n:ℝ)+2) →
    fsR (fun _ : Fin n => 2) false (noisyGHZ n p)<fsR (fun _ : Fin n => 2) true (noisyGHZ n p)) :=
  x8g_main n hn p hp0 hp1
