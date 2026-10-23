-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.ghzWitnessBounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T04:16:36.261075+00:00
-- url     : https://prove2.me/submissions/3d92d9d9-8b68-4b49-a1a6-5cf36bf524d7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

lemma x8_ineq : ∀ (n : ℕ) (p q : Fin (n + 1) → ℝ), (∀ j, 0 ≤ p j) → (∀ j, 0 ≤ q j) →
    (∀ j, p j ^ 2 + q j ^ 2 = 1) →
    (2 ^ (n + 1) - 2) * ∏ j, (p j * q j) ≤ 1 - (∏ j, p j) ^ 2 - (∏ j, q j) ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro p q _ _ h
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, zero_add, pow_one]
    nlinarith [h 0]
  | succ n ih =>
    intro p q hp hq h
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ (fun j => p j), Fin.prod_univ_succ (fun j => q j)]
    have IH := ih (fun j => p j.succ) (fun j => q j.succ) (fun j => hp _) (fun j => hq _)
      (fun j => h _)
    rw [Finset.prod_mul_distrib] at IH ⊢
    set a := ∏ j : Fin (n + 1), p j.succ
    set b := ∏ j : Fin (n + 1), q j.succ
    have ha : 0 ≤ a := Finset.prod_nonneg fun j _ => hp _
    have hb : 0 ≤ b := Finset.prod_nonneg fun j _ => hq _
    have h0 := h 0
    have hK : (0 : ℝ) ≤ 2 ^ (n + 1) - 2 := by
      have : (2 : ℝ) ≤ 2 ^ (n + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have h2pq : 0 ≤ 1 - 2 * (p 0 * q 0) := by nlinarith [sq_nonneg (p 0 - q 0)]
    have key : 1 - (p 0 * a) ^ 2 - (q 0 * b) ^ 2 =
        (1 - a ^ 2 - b ^ 2) + a ^ 2 * q 0 ^ 2 + b ^ 2 * p 0 ^ 2 := by
      linear_combination (-(a ^ 2 + b ^ 2)) * h0
    rw [key, pow_succ]
    nlinarith [IH, sq_nonneg (a * q 0 - b * p 0), mul_nonneg (mul_nonneg hK (mul_nonneg ha hb)) h2pq]

end QAlgorithms.Papers.Independent.Information100.P21
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

lemma x8_ket (n : ℕ) (b : Bool) (x : Fin n → Fin 2) :
    constantKet n b x = if x = (fun _ => if b then 1 else 0) then 1 else 0 := by
  simp [constantKet, QAlgorithms.ket, PiLp.single_apply]

lemma x8_trproj {n : ℕ} (b : Bool) (σ : Op (Fin n → Fin 2)) :
    (proj (constantKet n b) * σ).trace =
      σ (fun _ => if b then 1 else 0) (fun _ => if b then 1 else 0) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, proj, QAlgorithms.pureDensity,
    Matrix.of_apply, x8_ket]
  simp [ite_mul, Finset.sum_ite_eq']

lemma x8_trC {n : ℕ} (σ : Op (Fin n → Fin 2)) :
    (ghzC n * σ).trace = σ (fun _ => 1) (fun _ => 0) + σ (fun _ => 0) (fun _ => 1) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, ghzC, x8_ket]
  simp [add_mul, ite_mul, Finset.sum_add_distrib, Finset.sum_ite_eq']

lemma x8_trZ {n : ℕ} (σ : Op (Fin n → Fin 2)) :
    (ghzZ n * σ).trace = (((2^n:ℝ)/(2*((2^n:ℝ)-2)) : ℝ) : ℂ) *
      (σ.trace - σ (fun _ => 0) (fun _ => 0) - σ (fun _ => 1) (fun _ => 1)) -
      (((2^n:ℝ)/4 : ℝ) : ℂ) * (σ (fun _ => 1) (fun _ => 0) + σ (fun _ => 0) (fun _ => 1)) := by
  simp only [ghzZ, ghzE, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, x8_trproj, x8_trC, smul_eq_mul]
  simp only [Bool.false_eq_true, if_false, if_true]
  push_cast
  ring

end QAlgorithms.Papers.Independent.Information100.P21
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

lemma x8_pent {n : ℕ} (v : Fin n → Vec (Fin 2)) (x y : Fin n → Fin 2) :
    proj (productKet (d := fun _ : Fin n => 2) v) x y = ∏ j, (v j (x j) * conj (v j (y j))) := by
  simp only [proj, QAlgorithms.pureDensity, Matrix.of_apply, productKet, map_prod]
  rw [← Finset.prod_mul_distrib]

lemma x8_pdiag {n : ℕ} (v : Fin n → Vec (Fin 2)) (x : Fin n → Fin 2) :
    proj (productKet (d := fun _ : Fin n => 2) v) x x = ((∏ j, ‖v j (x j)‖ ^ 2 : ℝ) : ℂ) := by
  rw [x8_pent]
  push_cast
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

lemma x8_ptr {n : ℕ} (v : Fin n → Vec (Fin 2)) (hv : ∀ j, ‖v j‖ = 1) :
    (proj (productKet (d := fun _ : Fin n => 2) v)).trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, x8_pdiag]
  rw [← Complex.ofReal_sum]
  have hsw := Finset.sum_prod_piFinset (Finset.univ : Finset (Fin 2))
    (fun j b => ‖v j b‖ ^ 2)
  simp only [Fintype.piFinset_univ] at hsw
  rw [hsw]
  have : ∀ j, ∑ b, ‖v j b‖ ^ 2 = 1 := fun j => by
    rw [← EuclideanSpace.norm_sq_eq, hv j, one_pow]
  simp [this]

lemma x8_pbounds {n : ℕ} (hn : 2 ≤ n) (v : Fin n → Vec (Fin 2)) (hv : ∀ j, ‖v j‖ = 1) :
    0 ≤ (ghzZ n * proj (productKet (d := fun _ : Fin n => 2) v)).trace.re ∧
    (ghzZ n * proj (productKet (d := fun _ : Fin n => 2) v)).trace.re ≤ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set p : Fin (m + 1) → ℝ := fun j => ‖v j 0‖
  set q : Fin (m + 1) → ℝ := fun j => ‖v j 1‖
  have hpq : ∀ j, p j ^ 2 + q j ^ 2 = 1 := fun j => by
    have := EuclideanSpace.norm_sq_eq (v j)
    rw [hv j, Fin.sum_univ_two] at this
    simp only [p, q]; linarith
  have hp : ∀ j, 0 ≤ p j := fun j => norm_nonneg _
  have hq : ∀ j, 0 ≤ q j := fun j => norm_nonneg _
  set w : ℂ := ∏ j, (v j 1 * conj (v j 0))
  have hw : ‖w‖ = ∏ j, (p j * q j) := by
    simp only [w, norm_prod, norm_mul, Complex.norm_conj, p, q]
    exact Finset.prod_congr rfl fun j _ => by ring
  have h00 : proj (productKet (d := fun _ : Fin (m + 1) => 2) v) (fun _ => 0) (fun _ => 0) = (((∏ j, p j) ^ 2 : ℝ) : ℂ) := by
    rw [x8_pdiag, ← Finset.prod_pow]
  have h11 : proj (productKet (d := fun _ : Fin (m + 1) => 2) v) (fun _ => 1) (fun _ => 1) = (((∏ j, q j) ^ 2 : ℝ) : ℂ) := by
    rw [x8_pdiag, ← Finset.prod_pow]
  have h10 : proj (productKet (d := fun _ : Fin (m + 1) => 2) v) (fun _ => 1) (fun _ => 0) = w := x8_pent _ _ _
  have h01 : proj (productKet (d := fun _ : Fin (m + 1) => 2) v) (fun _ => 0) (fun _ => 1) = conj w := by
    rw [x8_pent]; simp only [w, map_prod, map_mul, Complex.conj_conj]
    exact Finset.prod_congr rfl fun j _ => by ring
  rw [x8_trZ, x8_ptr v hv, h00, h11, h10, h01]
  have hre : ((((2^(m+1):ℝ)/(2*((2^(m+1):ℝ)-2)) : ℝ) : ℂ) *
      (1 - (((∏ j, p j) ^ 2 : ℝ) : ℂ) - (((∏ j, q j) ^ 2 : ℝ) : ℂ)) -
      (((2^(m+1):ℝ)/4 : ℝ) : ℂ) * (w + conj w)).re =
      (2^(m+1):ℝ)/(2*((2^(m+1):ℝ)-2)) * (1 - (∏ j, p j) ^ 2 - (∏ j, q j) ^ 2) -
        (2^(m+1):ℝ)/4 * (2 * w.re) := by
    rw [Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.add_re, Complex.conj_re]
    ring
  rw [hre]
  set D : ℝ := 2 ^ (m + 1)
  have hD : 4 ≤ D := by
    simp only [D]
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hD2 : D - 2 ≠ 0 := by linarith
  have hI := x8_ineq m p q hp hq hpq
  rw [show (2 : ℝ) ^ (m + 1) = D from rfl] at hI
  set G := ∏ j, (p j * q j)
  have hG : G = (∏ j, p j) * (∏ j, q j) := Finset.prod_mul_distrib
  have hG0 : 0 ≤ G := Finset.prod_nonneg fun j _ => mul_nonneg (hp j) (hq j)
  have hGD : G * D ≤ 1 := by
    have : G ≤ ∏ _j : Fin (m + 1), (1 / 2 : ℝ) :=
      Finset.prod_le_prod (fun j _ => mul_nonneg (hp j) (hq j))
        (fun j _ => by nlinarith [hpq j, sq_nonneg (p j - q j)])
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    have hD' : D = 2 ^ (m + 1) := rfl
    rw [hD']
    calc G * 2 ^ (m + 1) ≤ (1 / 2) ^ (m + 1) * 2 ^ (m + 1) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  have hwre : |w.re| ≤ G := (Complex.abs_re_le_norm w).trans hw.le
  have hsq : 2 * G ≤ (∏ j, p j) ^ 2 + (∏ j, q j) ^ 2 := by
    rw [hG]; nlinarith [sq_nonneg ((∏ j, p j) - (∏ j, q j))]
  have hα : D / (2 * (D - 2)) * (D - 2) = D / 2 := by field_simp
  have hαpos : 0 ≤ D / (2 * (D - 2)) := by apply div_nonneg <;> linarith
  have hre1 := neg_abs_le w.re
  have hre2 := le_abs_self w.re
  constructor
  · -- α(1-P-Q) ≥ α(D-2)G = (D/2)G ≥ (D/2) w.re
    have h1 : D / (2 * (D - 2)) * ((D - 2) * G) ≤
        D / (2 * (D - 2)) * (1 - (∏ j, p j) ^ 2 - (∏ j, q j) ^ 2) :=
      mul_le_mul_of_nonneg_left hI hαpos
    have h2 : D / (2 * (D - 2)) * ((D - 2) * G) = D / 2 * G := by
      rw [← mul_assoc, hα]
    nlinarith
  · have h1 : D / (2 * (D - 2)) * (1 - (∏ j, p j) ^ 2 - (∏ j, q j) ^ 2) ≤
        D / (2 * (D - 2)) * (1 - 2 * G) := mul_le_mul_of_nonneg_left (by linarith) hαpos
    -- α(1-2G) + (D/2) G ≤ 1  ⟸  G ≤ 1/D
    have h3 : D / (2 * (D - 2)) * (1 - 2 * G) + D / 2 * G ≤ 1 := by
      have e : D / (2 * (D - 2)) * (1 - 2 * G) + D / 2 * G =
          D / (2 * (D - 2)) + G * D * (D - 4) / (2 * (D - 2)) := by
        field_simp; ring
      rw [e]
      have : G * D * (D - 4) ≤ D - 4 := by nlinarith
      have h4 : G * D * (D - 4) / (2 * (D - 2)) ≤ (D - 4) / (2 * (D - 2)) :=
        div_le_div_of_nonneg_right this (by linarith)
      have h5 : D / (2 * (D - 2)) + (D - 4) / (2 * (D - 2)) = 1 := by
        field_simp; ring
      linarith
    nlinarith

end QAlgorithms.Papers.Independent.Information100.P21
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

lemma x8_proj_herm {I : Type*} [Fintype I] (v : Vec I) : (proj v).IsHermitian := by
  ext x y
  simp [proj, QAlgorithms.pureDensity, Matrix.conjTranspose_apply, mul_comm]

lemma x8_C_herm (n : ℕ) : (ghzC n).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, ghzC, star_add, star_mul', RCLike.star_def,
    Complex.conj_conj]
  ring

lemma x8_E_herm (n : ℕ) : (ghzE n).IsHermitian :=
  (x8_proj_herm _).add (x8_proj_herm _)

lemma x8_real_sa (r : ℝ) : IsSelfAdjoint (r : ℂ) := by
  simp [IsSelfAdjoint, Complex.conj_ofReal]

lemma x8_sa (c : ℂ) (h : conj c = c) : IsSelfAdjoint c := h

lemma x8_Z_herm (n : ℕ) : (ghzZ n).IsHermitian := by
  unfold ghzZ
  apply Matrix.IsHermitian.sub
  · apply Matrix.IsHermitian.smul (Matrix.isHermitian_one.sub (x8_E_herm n))
    exact x8_sa _ (by simp [map_div₀, map_inv₀, map_sub, map_mul, map_pow, map_ofNat])
  · apply Matrix.IsHermitian.smul (x8_C_herm n)
    exact x8_sa _ (by simp [map_div₀, map_inv₀, map_sub, map_mul, map_pow, map_ofNat])

lemma x8_Zg_herm (n : ℕ) : (ghzZg n).IsHermitian := by
  unfold ghzZg
  apply Matrix.IsHermitian.smul (x8_Z_herm n)
  exact x8_sa _ (by simp [map_div₀, map_inv₀, map_sub, map_mul, map_pow, map_ofNat])

lemma x8_EC (n : ℕ) : ghzE n + ghzC n = proj (constantKet n false + constantKet n true) := by
  ext x y
  simp only [ghzE, ghzC, proj, QAlgorithms.pureDensity, Matrix.add_apply, Matrix.of_apply,
    PiLp.add_apply, map_add]
  ring

lemma x8_psd_proj {I : Type*} [Fintype I] (v : Vec I) : (proj v).PosSemidef := by
  have : proj v = Matrix.vecMulVec (⇑v) (star ⇑v) := by
    ext x y; simp [proj, QAlgorithms.pureDensity, Matrix.vecMulVec]
  rw [this]
  exact Matrix.posSemidef_vecMulVec_self_star _

lemma x8_psd_1E (n : ℕ) (hn : 1 ≤ n) : (1 - ghzE n).PosSemidef := by
  have h01 : (fun _ : Fin n => (0 : Fin 2)) ≠ (fun _ => 1) := by
    intro h; have := congrFun h ⟨0, hn⟩; simp at this
  have : 1 - ghzE n = Matrix.diagonal (fun x : Fin n → Fin 2 =>
      if x = (fun _ => 0) ∨ x = (fun _ => 1) then (0 : ℂ) else 1) := by
    ext x y
    simp only [ghzE, proj, QAlgorithms.pureDensity, Matrix.sub_apply, Matrix.add_apply,
      Matrix.of_apply, x8_ket, Matrix.one_apply, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst hxy
      by_cases h0 : x = fun _ => 0
      · subst h0; simp [Ne.symm h01, h01]
      by_cases h1 : x = fun _ => 1
      · subst h1; simp [h01, Ne.symm h01]
      simp [h0, h1]
    · simp only [hxy, if_false]
      split_ifs <;> simp_all
  rw [this]
  exact Matrix.PosSemidef.diagonal fun x => by split_ifs <;> simp

end QAlgorithms.Papers.Independent.Information100.P21
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

lemma x8_hull {n : ℕ} (hn : 2 ≤ n) (σ : Op (Fin n → Fin 2)) (hσ : σ ∈ fs (fun _ : Fin n => 2)) :
    0 ≤ (ghzZ n * σ).trace.re ∧ (ghzZ n * σ).trace.re ≤ 1 := by
  have hsub : fs (fun _ : Fin n => 2) ⊆
      {X : Op (Fin n → Fin 2) | 0 ≤ (ghzZ n * X).trace.re ∧ (ghzZ n * X).trace.re ≤ 1} := by
    refine convexHull_min ?_ ?_
    · rintro X ⟨v, hv, rfl⟩
      exact x8_pbounds hn v hv
    · intro X hX Y hY a b ha hb hab
      simp only [Set.mem_setOf_eq, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
        Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul] at hX hY ⊢
      constructor <;> nlinarith [hX.1, hX.2, hY.1, hY.2]
  exact hsub hσ

theorem x8_ghz_main (n : ℕ) (hn : 2 ≤ n) :
    (ghzZ n).IsHermitian ∧ (ghzZg n).IsHermitian ∧
    (∀ sigma : Op (Fin n → Fin 2), sigma ∈ fs (fun _ : Fin n => 2) →
      0 ≤ (ghzZ n * sigma).trace.re ∧ (ghzZ n * sigma).trace.re ≤ 1 ∧
        0 ≤ (ghzZg n * sigma).trace.re) ∧
    (1 - ghzZg n).PosSemidef := by
  refine ⟨x8_Z_herm n, x8_Zg_herm n, fun σ hσ => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := x8_hull hn σ hσ
    refine ⟨h1, h2, ?_⟩
    have e : ghzZg n * σ = ((((2 ^ n : ℝ) / 4)⁻¹ : ℝ) : ℂ) • (ghzZ n * σ) := by
      rw [ghzZg, Matrix.smul_mul]; push_cast; rfl
    rw [e, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    exact mul_nonneg (by positivity) h1
  · have hD : (4 : ℝ) ≤ 2 ^ n := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have hγ : 0 ≤ 1 - 2 / ((2 : ℝ) ^ n - 2) := by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    have hD0 : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    have hD2 : (2 : ℂ) ^ n - 2 ≠ 0 := by
      intro h
      have h' : ‖(2 : ℂ) ^ n‖ = ‖(2 : ℂ)‖ := by rw [sub_eq_zero.mp h]
      rw [norm_pow, Complex.norm_two] at h'
      linarith
    have eq : 1 - ghzZg n = (((1 - 2 / ((2 : ℝ) ^ n - 2)) : ℝ) : ℂ) • (1 - ghzE n) +
        proj (constantKet n false + constantKet n true) := by
      rw [← x8_EC]
      ext x y
      simp only [ghzZg, ghzZ, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast
      field_simp
      ring
    rw [eq]
    exact ((x8_psd_1E n (by omega)).smul (by exact_mod_cast hγ)).add (x8_psd_proj _)

end QAlgorithms.Papers.Independent.Information100.P21

open QAlgorithms.Papers.Independent.Information100.P21 in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution (n : ℕ) (hn : 2≤n) :
  (ghzZ n).IsHermitian ∧ (ghzZg n).IsHermitian ∧
  (∀ sigma : Op (Fin n → Fin 2), sigma∈fs (fun _ : Fin n => 2) →
    0≤(ghzZ n*sigma).trace.re ∧ (ghzZ n*sigma).trace.re≤1 ∧ 0≤(ghzZg n*sigma).trace.re) ∧
  (1-ghzZg n).PosSemidef :=
  QAlgorithms.Papers.Independent.Information100.P21.x8_ghz_main n hn
