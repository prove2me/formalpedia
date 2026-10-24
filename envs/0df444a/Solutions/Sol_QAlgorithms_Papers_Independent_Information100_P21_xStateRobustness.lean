-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.xStateRobustness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T11:28:45.023299+00:00
-- url     : https://prove2.me/submissions/9970481d-eede-4ea7-bb1b-64ba378cad93

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

theorem x8_xs_pt (a b c d w z : ℝ) : pt (xstate a b c d w z) = xstate a b c d z w := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp [pt, xstate]

theorem x8_xs_add (a b c d w z a' b' c' d' w' z' : ℝ) :
    xstate a b c d w z + xstate a' b' c' d' w' z' =
      xstate (a + a') (b + b') (c + c') (d + d') (w + w') (z + z') := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp [xstate]

theorem x8_xs_smul (r a b c d w z : ℝ) :
    (r : ℂ) • xstate a b c d w z = xstate (r * a) (r * b) (r * c) (r * d) (r * w) (r * z) := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp [xstate]

theorem x8_xs_trace (a b c d w z : ℝ) :
    (xstate a b c d w z).trace = ((a + b + c + d : ℝ) : ℂ) := by
  simp [Matrix.trace, xstate, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem x8_noiseEx : noiseEx = xstate 0 (1/20) (1/5) 0 0 0 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [noiseEx, compressed, xstate, proj, QAlgorithms.pureDensity, QAlgorithms.ket]

theorem x8_noiseOld : noiseOld = xstate (3/40) (3/20) (3/80) (3/40) (-3/40) (3/40) := by
  have h2 : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1/2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [noiseOld, xstate, proj, QAlgorithms.pureDensity, QAlgorithms.ket, h2] <;> (try ring_nf) <;>
    (try simp [map_ofNat]) <;> (try norm_num)

theorem x8_quad2 {a d w X Y : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (h : w ^ 2 ≤ a * d) :
    0 ≤ a * X ^ 2 + 2 * w * X * Y + d * Y ^ 2 := by
  rcases ha.eq_or_lt with h0 | h0
  · subst h0
    have : w = 0 := by nlinarith [sq_nonneg w]
    subst this; nlinarith [sq_nonneg Y]
  · have : 0 ≤ a * (a * X ^ 2 + 2 * w * X * Y + d * Y ^ 2) := by
      nlinarith [sq_nonneg (a * X + w * Y), sq_nonneg Y]
    exact (mul_nonneg_iff_of_pos_left h0).1 this

theorem x8_xs_psd {a b c d w z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hw : w ^ 2 ≤ a * d) (hz : z ^ 2 ≤ b * c) : (xstate a b c d w z).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
      simp [xstate, Matrix.conjTranspose_apply]
  · simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two, xstate]
    rw [Complex.le_def]
    simp
    refine ⟨?_, by ring⟩
    have h1 := x8_quad2 (X := (x (0, 0)).re) (Y := (x (1, 1)).re) ha hd hw
    have h2 := x8_quad2 (X := (x (0, 0)).im) (Y := (x (1, 1)).im) ha hd hw
    have h3 := x8_quad2 (X := (x (0, 1)).re) (Y := (x (1, 0)).re) hb hc hz
    have h4 := x8_quad2 (X := (x (0, 1)).im) (Y := (x (1, 0)).im) hb hc hz
    nlinarith [h1, h2, h3, h4]

theorem x8_pt_kron {I J : Type*} (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    pt (Matrix.kronecker A B) = Matrix.kronecker A Bᵀ := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩; simp [pt, Matrix.kronecker, Matrix.kroneckerMap]

theorem x8_pt_sum {I J : Type*} {q : ℕ} (X : Fin q → Op (I × J)) :
    pt (∑ j, X j) = ∑ j, pt (X j) := by
  ext p r; simp [pt, Matrix.sum_apply]

theorem x8_pt_smul {I J : Type*} (c : ℂ) (X : Op (I × J)) : pt (c • X) = c • pt X := by
  ext p r; simp [pt]

theorem x8_pt_add {I J : Type*} (X Y : Op (I × J)) : pt (X + Y) = pt X + pt Y := by
  ext p r; simp [pt]

theorem x8_sep_pt {I J : Type*} [Fintype I] [Fintype J] {X : Op (I × J)}
    (h : QAlgorithms.Entanglement.IsSeparablePositive X) : (pt X).PosSemidef := by
  obtain ⟨q, w, A, B, hw, hAB, rfl⟩ := h
  rw [x8_pt_sum]
  apply Matrix.posSemidef_sum
  intro j _
  rw [x8_pt_smul, x8_pt_kron]
  have : (w j : ℂ) • Matrix.kronecker (A j) (B j)ᵀ = (w j : ℂ) • Matrix.kronecker (A j) (B j)ᵀ := rfl
  exact ((hAB j).1.1.kronecker (hAB j).2.1.transpose).smul (by exact_mod_cast hw j)

/-- PSD gives nonnegativity on `e_a + c e_b` for real `c`. -/
theorem x8_psd_pair {M : Op QQ} (hM : M.PosSemidef) (a b : QQ) (hab : a ≠ b) (c : ℝ) :
    0 ≤ (M a a + (c : ℂ) * M a b + (c : ℂ) * M b a + (c : ℂ) ^ 2 * M b b).re := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hM
  have h := hM.2 (Pi.single a 1 + (c : ℂ) • Pi.single b 1)
  have hba : b ≠ a := hab.symm
  simp only [dotProduct, Matrix.mulVec, Pi.add_apply, Pi.smul_apply, Pi.star_apply, Pi.single_apply,
    star_add, smul_eq_mul, apply_ite (star : ℂ → ℂ), star_one, star_zero, add_mul, mul_add,
    ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, if_neg hab, if_neg hba] at h
  have h' := (Complex.le_def.1 h).1
  simp at h'
  simp [Complex.add_re, Complex.mul_re, pow_two]
  nlinarith [h']

theorem x8_sqrt2_inv : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1/2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem x8_vplus : proj (((Real.sqrt 2)⁻¹:ℂ) • (QAlgorithms.ket ((0,0) : QQ) + QAlgorithms.ket (1,1))) =
    xstate (1/2) 0 0 (1/2) (1/2) 0 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [xstate, proj, QAlgorithms.pureDensity, QAlgorithms.ket, x8_sqrt2_inv]

theorem x8_vminus : proj (((Real.sqrt 2)⁻¹:ℂ) • (QAlgorithms.ket ((0,0) : QQ) - QAlgorithms.ket (1,1))) =
    xstate (1/2) 0 0 (1/2) (-1/2) 0 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [xstate, proj, QAlgorithms.pureDensity, QAlgorithms.ket, x8_sqrt2_inv] <;> norm_num

theorem x8_ysep : compressed true (1/2) (1/2) = xstate 0 (1/2) (1/2) 0 0 0 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [compressed, xstate, proj, QAlgorithms.pureDensity, QAlgorithms.ket]

theorem x8_bell_lb {s : ℝ} {ω : Op QQ} (hs : 0 ≤ s) (hω : QAlgorithms.IsDensityMatrix ω)
    (hm : sep (mix (xstate (1/2) 0 0 (1/2) (1/2) 0) ω s)) : 1 ≤ s := by
  have hP := x8_psd_pair (x8_sep_pt hm.1) (0,1) (1,0) (by decide) (-1)
  have hW := x8_psd_pair hω.1 (0,0) (1,1) (by decide) 1
  have htr := congrArg Complex.re hω.2
  simp [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two] at htr
  simp [mix, pt, xstate] at hP
  simp at hW
  have h1 : 0 < 1 + s := by linarith
  have hk : 0 < (1 + s) / Complex.normSq (1 + (s : ℂ)) := by
    rw [show (1:ℂ) + (s : ℂ) = ((1 + s : ℝ) : ℂ) by push_cast; ring, Complex.normSq_ofReal]
    positivity
  set k := (1 + s) / Complex.normSq (1 + (s : ℂ))
  have hX : 0 ≤ -1 + s * ((ω (0,1) (0,1)).re + (ω (1,0) (1,0)).re - (ω (0,0) (1,1)).re
      - (ω (1,1) (0,0)).re) := by
    refine (mul_nonneg_iff_of_pos_left hk).1 ?_
    linarith [hP]
  nlinarith

theorem x8_vdens (u : Fin 2 → ℂ) (hu : Complex.normSq (u 0) + Complex.normSq (u 1) = 2) :
    QAlgorithms.IsDensityMatrix ((1/2 : ℂ) • Matrix.vecMulVec u (star u)) := by
  refine ⟨(Matrix.posSemidef_vecMulVec_self_star u).smul (by norm_num [Complex.le_def]), ?_⟩
  simp only [Matrix.trace, Matrix.diag, Matrix.smul_apply, Matrix.vecMulVec_apply, Fin.sum_univ_two,
    Pi.star_apply, RCLike.star_def, Complex.mul_conj, smul_eq_mul]
  rw [← mul_add, ← Complex.ofReal_add, hu]; norm_num

def x8U : Fin 4 → Fin 2 → ℂ := ![![1, 1], ![1, -1], ![1, Complex.I], ![1, -Complex.I]]
def x8V : Fin 4 → Fin 2 → ℂ := ![![1, 1], ![1, -1], ![1, -Complex.I], ![1, Complex.I]]

theorem x8_bell_sep : sep (mix (xstate (1/2) 0 0 (1/2) (1/2) 0) (xstate 0 (1/2) (1/2) 0 0 0) 1) := by
  refine ⟨⟨4, fun _ => 1/4, fun j => (1/2 : ℂ) • Matrix.vecMulVec (x8U j) (star (x8U j)),
    fun j => (1/2 : ℂ) • Matrix.vecMulVec (x8V j) (star (x8V j)), fun _ => by norm_num,
    fun j => ⟨x8_vdens _ ?_, x8_vdens _ ?_⟩, ?_⟩, ?_⟩
  · fin_cases j <;> simp [x8U] <;> norm_num
  · fin_cases j <;> simp [x8V] <;> norm_num
  · ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
      simp [mix, xstate, Fin.sum_univ_four, x8U, x8V, Matrix.vecMulVec_apply,
        Matrix.kronecker, Matrix.kroneckerMap] <;> ring_nf <;> simp [Complex.ext_iff] <;> norm_num
  · simp [mix, Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two, xstate]; norm_num

theorem x8_psd_pair2 {M : Op QQ} (hM : M.PosSemidef) (a b : QQ) (hab : a ≠ b) (x y : ℝ) :
    0 ≤ x ^ 2 * (M a a).re + x * y * (M a b).re + x * y * (M b a).re + y ^ 2 * (M b b).re := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hM
  have h := hM.2 ((x : ℂ) • Pi.single a 1 + (y : ℂ) • Pi.single b 1)
  have hba : b ≠ a := hab.symm
  simp only [dotProduct, Matrix.mulVec, Pi.add_apply, Pi.smul_apply, Pi.star_apply, Pi.single_apply,
    star_add, smul_eq_mul, apply_ite (star : ℂ → ℂ), star_one, star_zero, add_mul, mul_add,
    ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, star_mul', Complex.star_def,
    Complex.conj_ofReal] at h
  have h' := (Complex.le_def.1 h).1
  simp at h'
  nlinarith [h']

theorem x8_diag_nn {M : Op QQ} (hM : M.PosSemidef) (a : QQ) : 0 ≤ (M a a).re := by
  have := x8_psd_pair2 hM a (if a = (0,0) then (1,1) else (0,0)) (by split_ifs <;> simp_all) 1 0
  simpa using this

theorem x8_mix_pt (ρ ω : Op QQ) (s : ℝ) (p q : QQ) :
    (pt (mix ρ ω s) p q).re = (1 + s)⁻¹ * ((pt ρ p q).re + s * (pt ω p q).re) := by
  simp only [mix, pt, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Complex.re_ofReal_mul,
    Complex.add_re]

/-- Witness bound on the (01,10) block. -/
theorem x8_lb1 {ρ ω : Op QQ} {s : ℝ} (hs : 0 ≤ s) (hω : QAlgorithms.IsDensityMatrix ω)
    (hm : sep (mix ρ ω s)) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    -(x ^ 2 * (pt ρ (0,1) (0,1)).re - x * y * (pt ρ (0,1) (1,0)).re - x * y * (pt ρ (1,0) (0,1)).re
      + y ^ 2 * (pt ρ (1,0) (1,0)).re) ≤ s * max x y ^ 2 := by
  have hP := x8_psd_pair2 (x8_sep_pt hm.1) (0,1) (1,0) (by decide) x (-y)
  simp only [x8_mix_pt] at hP
  have hW := x8_psd_pair2 hω.1 (0,0) (1,1) (by decide) 1 1
  have htr := congrArg Complex.re hω.2
  simp [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two] at htr
  have d1 := x8_diag_nn hω.1 (0,0)
  have d2 := x8_diag_nn hω.1 (0,1)
  have d3 := x8_diag_nn hω.1 (1,0)
  have d4 := x8_diag_nn hω.1 (1,1)
  simp only [pt] at hP hW ⊢
  have h1 : 0 < 1 + s := by linarith
  have hk : 0 ≤ x ^ 2 * ((ρ (0, 1) (0, 1)).re + s * (ω (0, 1) (0, 1)).re) +
      x * -y * ((ρ (0, 0) (1, 1)).re + s * (ω (0, 0) (1, 1)).re) +
      x * -y * ((ρ (1, 1) (0, 0)).re + s * (ω (1, 1) (0, 0)).re) +
      y ^ 2 * ((ρ (1, 0) (1, 0)).re + s * (ω (1, 0) (1, 0)).re) := by
    have := mul_nonneg h1.le hP
    have e : (1 + s) * (1 + s)⁻¹ = 1 := mul_inv_cancel₀ h1.ne'
    nlinarith [e]
  have hmx : x ≤ max x y := le_max_left _ _
  have hmy : y ≤ max x y := le_max_right _ _
  have hxx : x ^ 2 ≤ max x y ^ 2 := pow_le_pow_left₀ hx hmx 2
  have hyy : y ^ 2 ≤ max x y ^ 2 := pow_le_pow_left₀ hy hmy 2
  have hxy : x * y ≤ max x y ^ 2 := by nlinarith
  have hb : x ^ 2 * (ω (0, 1) (0, 1)).re - x * y * (ω (0, 0) (1, 1)).re - x * y * (ω (1, 1) (0, 0)).re
      + y ^ 2 * (ω (1, 0) (1, 0)).re ≤ max x y ^ 2 := by
    simp at hW
    nlinarith [mul_le_mul_of_nonneg_right hxx d2, mul_le_mul_of_nonneg_right hyy d3,
      mul_le_mul_of_nonneg_right hxy (by linarith : 0 ≤ (ω (0,0) (0,0)).re + (ω (1,1) (1,1)).re),
      mul_le_mul_of_nonneg_left hW (mul_nonneg hx hy)]
  nlinarith [mul_le_mul_of_nonneg_left hb hs]

/-- Witness bound on the (00,11) block. -/
theorem x8_lb2 {ρ ω : Op QQ} {s : ℝ} (hs : 0 ≤ s) (hω : QAlgorithms.IsDensityMatrix ω)
    (hm : sep (mix ρ ω s)) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    -(x ^ 2 * (pt ρ (0,0) (0,0)).re - x * y * (pt ρ (0,0) (1,1)).re - x * y * (pt ρ (1,1) (0,0)).re
      + y ^ 2 * (pt ρ (1,1) (1,1)).re) ≤ s * max x y ^ 2 := by
  have hP := x8_psd_pair2 (x8_sep_pt hm.1) (0,0) (1,1) (by decide) x (-y)
  simp only [x8_mix_pt] at hP
  have hW := x8_psd_pair2 hω.1 (0,1) (1,0) (by decide) 1 1
  have htr := congrArg Complex.re hω.2
  simp [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two] at htr
  have d1 := x8_diag_nn hω.1 (0,0)
  have d2 := x8_diag_nn hω.1 (0,1)
  have d3 := x8_diag_nn hω.1 (1,0)
  have d4 := x8_diag_nn hω.1 (1,1)
  simp only [pt] at hP hW ⊢
  have h1 : 0 < 1 + s := by linarith
  have hk : 0 ≤ x ^ 2 * ((ρ (0, 0) (0, 0)).re + s * (ω (0, 0) (0, 0)).re) +
      x * -y * ((ρ (0, 1) (1, 0)).re + s * (ω (0, 1) (1, 0)).re) +
      x * -y * ((ρ (1, 0) (0, 1)).re + s * (ω (1, 0) (0, 1)).re) +
      y ^ 2 * ((ρ (1, 1) (1, 1)).re + s * (ω (1, 1) (1, 1)).re) := by
    have := mul_nonneg h1.le hP
    have e : (1 + s) * (1 + s)⁻¹ = 1 := mul_inv_cancel₀ h1.ne'
    nlinarith [e]
  have hmx : x ≤ max x y := le_max_left _ _
  have hmy : y ≤ max x y := le_max_right _ _
  have hxx : x ^ 2 ≤ max x y ^ 2 := pow_le_pow_left₀ hx hmx 2
  have hyy : y ^ 2 ≤ max x y ^ 2 := pow_le_pow_left₀ hy hmy 2
  have hxy : x * y ≤ max x y ^ 2 := by nlinarith
  have hb : x ^ 2 * (ω (0, 0) (0, 0)).re - x * y * (ω (0, 1) (1, 0)).re - x * y * (ω (1, 0) (0, 1)).re
      + y ^ 2 * (ω (1, 1) (1, 1)).re ≤ max x y ^ 2 := by
    simp at hW
    nlinarith [mul_le_mul_of_nonneg_right hxx d1, mul_le_mul_of_nonneg_right hyy d4,
      mul_le_mul_of_nonneg_right hxy (by linarith : 0 ≤ (ω (0,1) (0,1)).re + (ω (1,0) (1,0)).re),
      mul_le_mul_of_nonneg_left hW (mul_nonneg hx hy)]
  nlinarith [mul_le_mul_of_nonneg_left hb hs]

/-- The scalar optimization behind the branch value. -/
theorem x8_branch_lb {x y t s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : 0 ≤ t) (hb : x * y < t ^ 2)
    (H : ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → 2 * t * p * q - x * p ^ 2 - y * q ^ 2 ≤ s * max p q ^ 2) :
    branchValue x y t ≤ s := by
  unfold branchValue
  split_ifs with h
  · rcases le_total y x with hxy | hxy
    · rw [max_eq_left hxy] at h ⊢
      have hx0 : 0 < x := by
        rcases hx.lt_or_eq with h' | h'
        · exact h'
        · subst h'; nlinarith
      have := H (t / x) 1 (by positivity) zero_le_one
      rw [max_eq_right ((div_le_one hx0).2 h)] at this
      rw [div_le_iff₀ hx0]
      have e : 2 * t * (t / x) * 1 - x * (t / x) ^ 2 - y * 1 ^ 2 = t ^ 2 / x - y := by
        field_simp; ring
      rw [e] at this
      have := mul_le_mul_of_nonneg_right this hx0.le
      rw [sub_mul, div_mul_cancel₀ _ hx0.ne'] at this
      nlinarith
    · rw [max_eq_right hxy] at h ⊢
      have hy0 : 0 < y := by
        rcases hy.lt_or_eq with h' | h'
        · exact h'
        · subst h'; nlinarith
      have := H 1 (t / y) zero_le_one (by positivity)
      rw [max_eq_left ((div_le_one hy0).2 h)] at this
      rw [div_le_iff₀ hy0]
      have e : 2 * t * 1 * (t / y) - x * 1 ^ 2 - y * (t / y) ^ 2 = t ^ 2 / y - x := by
        field_simp; ring
      rw [e] at this
      have := mul_le_mul_of_nonneg_right this hy0.le
      rw [sub_mul, div_mul_cancel₀ _ hy0.ne'] at this
      nlinarith
  · have := H 1 1 zero_le_one zero_le_one
    simp at this; linarith

open QAlgorithms.Entanglement in
theorem x8_sp_zero {I J : Type*} [Fintype I] [Fintype J] :
    IsSeparablePositive (0 : Op (I × J)) :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, by simp⟩

open QAlgorithms.Entanglement in
theorem x8_sp_add {I J : Type*} [Fintype I] [Fintype J] {X Y : Op (I × J)}
    (hX : IsSeparablePositive X) (hY : IsSeparablePositive Y) : IsSeparablePositive (X + Y) := by
  obtain ⟨q1, w1, A1, B1, hw1, hd1, rfl⟩ := hX
  obtain ⟨q2, w2, A2, B2, hw2, hd2, rfl⟩ := hY
  refine ⟨q1 + q2, Fin.append w1 w2, Fin.append A1 A2, Fin.append B1 B2, ?_, ?_, ?_⟩
  · intro j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [hw1, hw2]
  · intro j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [hd1, hd2]
  · rw [Fin.sum_univ_add]; simp

open QAlgorithms.Entanglement in
theorem x8_sp_smul {I J : Type*} [Fintype I] [Fintype J] {X : Op (I × J)} {c : ℝ} (hc : 0 ≤ c)
    (hX : IsSeparablePositive X) : IsSeparablePositive ((c : ℂ) • X) := by
  obtain ⟨q, w, A, B, hw, hd, rfl⟩ := hX
  refine ⟨q, fun j => c * w j, A, B, fun j => mul_nonneg hc (hw j), hd, ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]; push_cast; rfl

open QAlgorithms.Entanglement in
theorem x8_sp_kron {I J : Type*} [Fintype I] [Fintype J] {A : Op I} {B : Op J}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : IsSeparablePositive (Matrix.kronecker A B) := by
  by_cases h0 : A.trace = 0 ∨ B.trace = 0
  · rcases h0 with h | h
    · rw [(hA.trace_eq_zero_iff).1 h]; simpa using (x8_sp_zero (I := I) (J := J))
    · rw [(hB.trace_eq_zero_iff).1 h]; simpa using (x8_sp_zero (I := I) (J := J))
  push_neg at h0
  have tA := hA.trace_nonneg
  have tB := hB.trace_nonneg
  have hAr : A.trace = ((A.trace.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [(Complex.le_def.1 tA).2.symm]
  have hBr : B.trace = ((B.trace.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [(Complex.le_def.1 tB).2.symm]
  have ha : 0 < A.trace.re := by
    have := (Complex.le_def.1 tA).1; simp at this
    rcases this.lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [hAr, ← h]; simp) h0.1
  have hb : 0 < B.trace.re := by
    have := (Complex.le_def.1 tB).1; simp at this
    rcases this.lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [hBr, ← h]; simp) h0.2
  refine ⟨1, fun _ => A.trace.re * B.trace.re, fun _ => ((A.trace.re)⁻¹ : ℂ) • A,
    fun _ => ((B.trace.re)⁻¹ : ℂ) • B, fun _ => by positivity, fun _ => ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · exact hA.smul (by have := inv_pos.2 ha; exact_mod_cast this.le)
  · rw [Matrix.trace_smul, hAr]; simp [ha.ne']
  · exact hB.smul (by have := inv_pos.2 hb; exact_mod_cast this.le)
  · rw [Matrix.trace_smul, hBr]; simp [hb.ne']
  · simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    have ha' : ((A.trace.re : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hb' : ((B.trace.re : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    ext p q
    simp only [Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, smul_eq_mul]
    push_cast
    field_simp

theorem x8_vv_psd (u : Fin 2 → ℂ) : (Matrix.vecMulVec u (star u)).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star u

/-- Averaging over a sign flip of a product vector gives an X piece. -/
theorem x8_piece_eq (u1 u2 v1 v2 : ℝ) (φ ψ : ℂ) :
    ((1/2 : ℝ) : ℂ) • (Matrix.kronecker (Matrix.vecMulVec ![(u1:ℂ), φ * u2] (star ![(u1:ℂ), φ * u2]))
          (Matrix.vecMulVec ![(v1:ℂ), ψ * v2] (star ![(v1:ℂ), ψ * v2])) +
        Matrix.kronecker (Matrix.vecMulVec ![(u1:ℂ), -φ * u2] (star ![(u1:ℂ), -φ * u2]))
          (Matrix.vecMulVec ![(v1:ℂ), -ψ * v2] (star ![(v1:ℂ), -ψ * v2]))) =
      fun p q => ((1/2 : ℝ) : ℂ) * (2 * (![(u1:ℂ), φ * u2] p.1 * star (![(u1:ℂ), φ * u2] q.1) *
        (![(v1:ℂ), ψ * v2] p.2 * star (![(v1:ℂ), ψ * v2] q.2))) *
        (if (p.1.val + p.2.val + q.1.val + q.2.val) % 2 = 0 then 1 else 0)) := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp <;> ring

theorem x8_piece_gen (u1 u2 v1 v2 : ℝ) (φ ψ : ℂ) :
    QAlgorithms.Entanglement.IsSeparablePositive (fun p q : QQ => ((1/2 : ℝ) : ℂ) *
      (2 * (![(u1:ℂ), φ * u2] p.1 * star (![(u1:ℂ), φ * u2] q.1) *
        (![(v1:ℂ), ψ * v2] p.2 * star (![(v1:ℂ), ψ * v2] q.2))) *
        (if (p.1.val + p.2.val + q.1.val + q.2.val) % 2 = 0 then 1 else 0))) := by
  rw [← x8_piece_eq]
  exact x8_sp_smul (by norm_num) (x8_sp_add (x8_sp_kron (x8_vv_psd _) (x8_vv_psd _))
    (x8_sp_kron (x8_vv_psd _) (x8_vv_psd _)))

theorem x8_piece_pp (u1 u2 v1 v2 : ℝ) : QAlgorithms.Entanglement.IsSeparablePositive
    (xstate (u1^2*v1^2) (u1^2*v2^2) (u2^2*v1^2) (u2^2*v2^2) (u1*u2*v1*v2) (u1*u2*v1*v2)) := by
  refine (congrArg QAlgorithms.Entanglement.IsSeparablePositive ?_).mpr (x8_piece_gen u1 u2 v1 v2 1 1)
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp [xstate] <;> ring

theorem x8_piece_pm (u1 u2 v1 v2 : ℝ) : QAlgorithms.Entanglement.IsSeparablePositive
    (xstate (u1^2*v1^2) (u1^2*v2^2) (u2^2*v1^2) (u2^2*v2^2) (u1*u2*v1*v2) (-(u1*u2*v1*v2))) := by
  refine (congrArg QAlgorithms.Entanglement.IsSeparablePositive ?_).mpr (x8_piece_gen u1 u2 v1 v2 Complex.I (-Complex.I))
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp [xstate] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem x8_piece_mp (u1 u2 v1 v2 : ℝ) : QAlgorithms.Entanglement.IsSeparablePositive
    (xstate (u1^2*v1^2) (u1^2*v2^2) (u2^2*v1^2) (u2^2*v2^2) (-(u1*u2*v1*v2)) (u1*u2*v1*v2)) := by
  refine (congrArg QAlgorithms.Entanglement.IsSeparablePositive ?_).mpr (x8_piece_gen u1 u2 v1 v2 Complex.I Complex.I)
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp [xstate] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem x8_sp_congr {a b c d w z a' b' c' d' w' z' : ℝ}
    (h : QAlgorithms.Entanglement.IsSeparablePositive (xstate a b c d w z))
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') (hw : w = w') (hz : z = z') :
    QAlgorithms.Entanglement.IsSeparablePositive (xstate a' b' c' d' w' z') := by
  subst ha hb hc hd hw hz; exact h

theorem x8_sp_diag {p q r t : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    QAlgorithms.Entanglement.IsSeparablePositive (xstate p q r t 0 0) := by
  have h1 := x8_piece_pp (Real.sqrt p) 0 1 0
  have h2 := x8_piece_pp (Real.sqrt q) 0 0 1
  have h3 := x8_piece_pp 0 (Real.sqrt r) 1 0
  have h4 := x8_piece_pp 0 (Real.sqrt t) 0 1
  have := x8_sp_add (x8_sp_add h1 h2) (x8_sp_add h3 h4)
  rw [x8_xs_add, x8_xs_add, x8_xs_add] at this
  refine x8_sp_congr this ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [Real.sq_sqrt, hp, hq, hr, ht]

theorem x8_piece_signed (u1 u2 v1 v2 t : ℝ) (ht : |t| = u1 * u2 * v1 * v2) :
    QAlgorithms.Entanglement.IsSeparablePositive
      (xstate (u1^2*v1^2) (u1^2*v2^2) (u2^2*v1^2) (u2^2*v2^2) t (-t)) := by
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h] at ht; rw [ht]; exact x8_piece_pm u1 u2 v1 v2
  · rw [abs_of_neg h] at ht
    have e : t = -(u1 * u2 * v1 * v2) := by linarith
    rw [e, neg_neg]; exact x8_piece_mp u1 u2 v1 v2

/-- The piece with prescribed coherence `r` built from square roots. -/
theorem x8_piece_r {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (r : ℝ) (sgn : Bool) :
    let K := Real.sqrt a * Real.sqrt b * Real.sqrt c * Real.sqrt d
    let e := |r| / K
    QAlgorithms.Entanglement.IsSeparablePositive
      (xstate (e * a * (Real.sqrt b * Real.sqrt c)) (e * b * (Real.sqrt a * Real.sqrt d))
        (e * c * (Real.sqrt a * Real.sqrt d)) (e * d * (Real.sqrt b * Real.sqrt c))
        (if sgn then |r| else r) (if sgn then |r| else -r)) := by
  intro K e
  set A := Real.sqrt a; set B := Real.sqrt b; set C := Real.sqrt c; set D := Real.sqrt d
  have hA : 0 < A := Real.sqrt_pos.2 ha
  have hB : 0 < B := Real.sqrt_pos.2 hb
  have hC : 0 < C := Real.sqrt_pos.2 hc
  have hD : 0 < D := Real.sqrt_pos.2 hd
  have hA2 : A ^ 2 = a := Real.sq_sqrt ha.le
  have hB2 : B ^ 2 = b := Real.sq_sqrt hb.le
  have hC2 : C ^ 2 = c := Real.sq_sqrt hc.le
  have hD2 : D ^ 2 = d := Real.sq_sqrt hd.le
  have hK : 0 < K := by positivity
  have he : 0 ≤ e := by positivity
  have heK : e * K = |r| := by simp only [e]; field_simp
  set se := Real.sqrt e; set sA := Real.sqrt A; set sB := Real.sqrt B
  set sC := Real.sqrt C; set sD := Real.sqrt D
  have hse : se ^ 2 = e := Real.sq_sqrt he
  have hsA : sA ^ 2 = A := Real.sq_sqrt hA.le
  have hsB : sB ^ 2 = B := Real.sq_sqrt hB.le
  have hsC : sC ^ 2 = C := Real.sq_sqrt hC.le
  have hsD : sD ^ 2 = D := Real.sq_sqrt hD.le
  have hm : (se * sA * sB) * (se * sC * sD) * (sA * sC) * (sB * sD) = |r| := by
    have : (se * sA * sB) * (se * sC * sD) * (sA * sC) * (sB * sD) =
        se ^ 2 * sA ^ 2 * sB ^ 2 * sC ^ 2 * sD ^ 2 := by ring
    rw [this, hse, hsA, hsB, hsC, hsD, ← heK]
    show e * A * B * C * D = e * (A * B * C * D); ring
  have p1 : (se * sA * sB) ^ 2 * (sA * sC) ^ 2 = e * a * (B * C) := by
    rw [show (se * sA * sB) ^ 2 * (sA * sC) ^ 2 = se^2 * (sA^2)^2 * sB^2 * sC^2 by ring,
      hse, hsA, hsB, hsC, ← hA2]; ring
  have p2 : (se * sA * sB) ^ 2 * (sB * sD) ^ 2 = e * b * (A * D) := by
    rw [show (se * sA * sB) ^ 2 * (sB * sD) ^ 2 = se^2 * sA^2 * (sB^2)^2 * sD^2 by ring,
      hse, hsA, hsB, hsD, ← hB2]; ring
  have p3 : (se * sC * sD) ^ 2 * (sA * sC) ^ 2 = e * c * (A * D) := by
    rw [show (se * sC * sD) ^ 2 * (sA * sC) ^ 2 = se^2 * sA^2 * (sC^2)^2 * sD^2 by ring,
      hse, hsA, hsC, hsD, ← hC2]; ring
  have p4 : (se * sC * sD) ^ 2 * (sB * sD) ^ 2 = e * d * (B * C) := by
    rw [show (se * sC * sD) ^ 2 * (sB * sD) ^ 2 = se^2 * sB^2 * sC^2 * (sD^2)^2 by ring,
      hse, hsB, hsC, hsD, ← hD2]; ring
  cases sgn
  · have := x8_piece_signed (se * sA * sB) (se * sC * sD) (sA * sC) (sB * sD) r hm.symm
    exact x8_sp_congr this p1 p2 p3 p4 rfl rfl
  · have := x8_piece_pp (se * sA * sB) (se * sC * sD) (sA * sC) (sB * sD)
    exact x8_sp_congr this p1 p2 p3 p4 hm hm

theorem x8_le_sqrt_mul {w a d : ℝ} (hw : 0 ≤ w) (ha : 0 ≤ a) (hd : 0 ≤ d) (h : w ^ 2 ≤ a * d) :
    w ≤ Real.sqrt a * Real.sqrt d := by
  rw [← Real.sqrt_mul ha]; exact Real.le_sqrt_of_sq_le h

/-- PPT X-states with nonnegative coherences are separable. -/
theorem x8_ppt_sep {a b c d w z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hw : 0 ≤ w) (hz : 0 ≤ z) (h1 : w ^ 2 ≤ a * d) (h2 : w ^ 2 ≤ b * c) (h3 : z ^ 2 ≤ a * d)
    (h4 : z ^ 2 ≤ b * c) : QAlgorithms.Entanglement.IsSeparablePositive (xstate a b c d w z) := by
  by_cases h0 : a * d = 0 ∨ b * c = 0
  · have hw0 : w = 0 := by rcases h0 with h | h <;> nlinarith
    have hz0 : z = 0 := by rcases h0 with h | h <;> nlinarith
    subst hw0 hz0; exact x8_sp_diag ha hb hc hd
  push_neg at h0
  have ha' : 0 < a := lt_of_le_of_ne ha (fun h => h0.1 (by rw [← h]; ring))
  have hd' : 0 < d := lt_of_le_of_ne hd (fun h => h0.1 (by rw [← h]; ring))
  have hb' : 0 < b := lt_of_le_of_ne hb (fun h => h0.2 (by rw [← h]; ring))
  have hc' : 0 < c := lt_of_le_of_ne hc (fun h => h0.2 (by rw [← h]; ring))
  have P1 := x8_piece_r ha' hb' hc' hd' ((w + z) / 2) true
  have P2 := x8_piece_r ha' hb' hc' hd' ((w - z) / 2) false
  simp only [if_true, Bool.false_eq_true, if_false] at P1 P2
  set A := Real.sqrt a; set B := Real.sqrt b; set C := Real.sqrt c; set D := Real.sqrt d
  have hA : 0 < A := Real.sqrt_pos.2 ha'
  have hB : 0 < B := Real.sqrt_pos.2 hb'
  have hC : 0 < C := Real.sqrt_pos.2 hc'
  have hD : 0 < D := Real.sqrt_pos.2 hd'
  have hwAD := x8_le_sqrt_mul hw ha hd h1
  have hwBC := x8_le_sqrt_mul hw hb hc h2
  have hzAD := x8_le_sqrt_mul hz ha hd h3
  have hzBC := x8_le_sqrt_mul hz hb hc h4
  have r1 : |(w + z) / 2| = (w + z) / 2 := abs_of_nonneg (by linarith)
  rw [r1] at P1
  set K := A * B * C * D
  have hK : 0 < K := by positivity
  set t := |(w - z) / 2|
  have ht : t = max w z - (w + z) / 2 := by
    simp only [t]; rcases le_total w z with h | h
    · rw [max_eq_right h, abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]; ring
  have hsum : ((w + z) / 2 / K + t / K) * K = max w z := by field_simp; rw [ht]; ring
  have hmBC : ((w + z) / 2 / K + t / K) * (B * C) ≤ 1 := by
    have : ((w + z) / 2 / K + t / K) * (B * C) = max w z / (A * D) := by
      rw [← hsum]; field_simp; ring
    rw [this, div_le_one (by positivity)]; exact max_le hwAD hzAD
  have hmAD : ((w + z) / 2 / K + t / K) * (A * D) ≤ 1 := by
    have : ((w + z) / 2 / K + t / K) * (A * D) = max w z / (B * C) := by
      rw [← hsum]; field_simp; ring
    rw [this, div_le_one (by positivity)]; exact max_le hwBC hzBC
  set E := (w + z) / 2 / K + t / K
  have R := x8_sp_diag (p := a * (1 - E * (B * C))) (q := b * (1 - E * (A * D)))
    (r := c * (1 - E * (A * D))) (t := d * (1 - E * (B * C)))
    (mul_nonneg ha (by linarith)) (mul_nonneg hb (by linarith)) (mul_nonneg hc (by linarith))
    (mul_nonneg hd (by linarith))
  have S := x8_sp_add (x8_sp_add P1 P2) R
  rw [x8_xs_add, x8_xs_add] at S
  refine x8_sp_congr S ?_ ?_ ?_ ?_ ?_ ?_ <;> first | ring | (simp only [E]; ring) | (rw [show E = (w + z) / 2 / K + t / K from rfl]; ring)

theorem x8_comp_true (u v : ℝ) : compressed true u v = xstate 0 u v 0 0 0 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [compressed, xstate, proj, QAlgorithms.pureDensity, QAlgorithms.ket]

theorem x8_comp_false (u v : ℝ) : compressed false u v = xstate u 0 0 v 0 0 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [compressed, xstate, proj, QAlgorithms.pureDensity, QAlgorithms.ket]

theorem x8_phys_dens {a b c d w z : ℝ} (h : physicalX a b c d w z) :
    QAlgorithms.IsDensityMatrix (xstate a b c d w z) := by
  obtain ⟨ha, hb, hc, hd, hw, hz, hs, h1, h2⟩ := h
  exact ⟨x8_xs_psd ha hb hc hd h1 h2, by rw [x8_xs_trace, hs]; simp⟩

theorem x8_mix_xs (a b c d w z a' b' c' d' w' z' s : ℝ) :
    mix (xstate a b c d w z) (xstate a' b' c' d' w' z') s =
      xstate ((1+s)⁻¹ * (a + s * a')) ((1+s)⁻¹ * (b + s * b')) ((1+s)⁻¹ * (c + s * c'))
        ((1+s)⁻¹ * (d + s * d')) ((1+s)⁻¹ * (w + s * w')) ((1+s)⁻¹ * (z + s * z')) := by
  unfold mix; rw [x8_xs_smul, x8_xs_add, x8_xs_smul]

/-- A diagonal noise of total weight `L` that makes the state PPT is feasible. -/
theorem x8_mem {a b c d w z p q r t : ℝ} (h : physicalX a b c d w z) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (hL : 0 < p + q + r + t)
    (h1 : w ^ 2 ≤ (a + p) * (d + t)) (h2 : w ^ 2 ≤ (b + q) * (c + r))
    (h3 : z ^ 2 ≤ (a + p) * (d + t)) (h4 : z ^ 2 ≤ (b + q) * (c + r)) (standard : Bool) :
    (p + q + r + t) ∈ {s : ℝ | 0 ≤ s ∧ ∃ omega : Op QQ, QAlgorithms.IsDensityMatrix omega ∧
      (standard = true → omega ∈ {X | sep X}) ∧ mix (xstate a b c d w z) omega s ∈ {X | sep X}} := by
  obtain ⟨ha, hb, hc, hd, hw, hz, hs, -, -⟩ := h
  set L := p + q + r + t
  have hω : QAlgorithms.IsDensityMatrix (xstate (p/L) (q/L) (r/L) (t/L) 0 0) :=
    ⟨x8_xs_psd (by positivity) (by positivity) (by positivity) (by positivity) (by simp; positivity)
      (by simp; positivity), by
        rw [x8_xs_trace]
        have e : p / L + q / L + r / L + t / L = 1 := by
          rw [← add_div, ← add_div, ← add_div, div_self hL.ne']
        rw [e]; simp⟩
  have hωs : sep (xstate (p/L) (q/L) (r/L) (t/L) 0 0) :=
    ⟨x8_sp_diag (by positivity) (by positivity) (by positivity) (by positivity), hω.2⟩
  refine ⟨hL.le, _, hω, fun _ => hωs, ?_⟩
  show sep _
  rw [x8_mix_xs]
  have hL1 : 0 < 1 + L := by linarith
  refine ⟨?_, ?_⟩
  · have S := x8_sp_smul (inv_nonneg.2 hL1.le)
      (x8_ppt_sep (by linarith) (by linarith) (by linarith) (by linarith) hw hz h1 h2 h3 h4)
    rw [x8_xs_smul] at S
    refine x8_sp_congr S ?_ ?_ ?_ ?_ ?_ ?_ <;> first | (simp; done) | field_simp
  · rw [x8_xs_trace]
    have : (1 + L)⁻¹ * (a + L * (p / L)) + (1 + L)⁻¹ * (b + L * (q / L)) +
        (1 + L)⁻¹ * (c + L * (r / L)) + (1 + L)⁻¹ * (d + L * (t / L)) = 1 := by
      field_simp; simp only [L]; linarith
    rw [this]; simp

theorem x8_rob_eq {ρ : Op QQ} {L : ℝ} {standard : Bool}
    (hmem : L ∈ {s : ℝ | 0 ≤ s ∧ ∃ omega : Op QQ, QAlgorithms.IsDensityMatrix omega ∧
      (standard = true → omega ∈ {X | sep X}) ∧ mix ρ omega s ∈ {X | sep X}})
    (hlb : ∀ s omega, 0 ≤ s → QAlgorithms.IsDensityMatrix omega → sep (mix ρ omega s) → L ≤ s) :
    robust {X | sep X} standard ρ = L := by
  unfold robust
  apply le_antisymm (csInf_le ⟨0, fun s hs => hs.1⟩ hmem)
  exact le_csInf ⟨L, hmem⟩ (fun s ⟨hs, ω, hω, _, hm⟩ => hlb s ω hs hω hm)

theorem x8_weights {x y t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : 0 ≤ t) (hb : x * y < t ^ 2) :
    0 ≤ (weights x y t).1 ∧ 0 ≤ (weights x y t).2 ∧
    (weights x y t).1 + (weights x y t).2 = branchValue x y t ∧
    0 < (weights x y t).1 + (weights x y t).2 ∧
    t ^ 2 ≤ (x + (weights x y t).1) * (y + (weights x y t).2) := by
  by_cases h1 : max x y ≤ t
  · simp only [weights, if_pos h1, branchValue]
    have hx' : x ≤ t := le_trans (le_max_left _ _) h1
    have hy' : y ≤ t := le_trans (le_max_right _ _) h1
    refine ⟨by linarith, by linarith, ?_, by nlinarith, by nlinarith⟩
    split_ifs with h2
    · have hm : max x y = t := le_antisymm h1 h2
      have ht0 : 0 < t := by
        rcases ht.lt_or_eq with h | h
        · exact h
        · subst h; nlinarith
      rw [hm]; field_simp
      rcases le_total y x with hxy | hxy
      · rw [max_eq_left hxy] at hm; subst hm; ring
      · rw [max_eq_right hxy] at hm; subst hm; ring
    · ring
  · push_neg at h1
    simp only [weights, if_neg (not_le.2 h1), branchValue, if_pos h1.le]
    by_cases h3 : t < x
    · simp only [if_pos h3]
      have hx0 : 0 < x := lt_of_le_of_lt ht h3
      have hyx : y ≤ x := by
        by_contra hyx; push_neg at hyx; nlinarith
      rw [max_eq_left hyx]
      have hv : 0 < t ^ 2 / x - y := by rw [sub_pos, lt_div_iff₀ hx0]; nlinarith
      refine ⟨le_refl _, hv.le, ?_, by linarith, ?_⟩
      · field_simp; ring
      · field_simp; nlinarith
    · simp only [if_neg h3]
      push_neg at h3
      have hxy : x ≤ y := by
        by_contra hxy; push_neg at hxy; rw [max_eq_left hxy.le] at h1; linarith
      rw [max_eq_right hxy] at h1 ⊢
      have hy0 : 0 < y := lt_of_le_of_lt ht h1
      have hv : 0 < t ^ 2 / y - x := by rw [sub_pos, lt_div_iff₀ hy0]; nlinarith
      refine ⟨hv.le, le_refl _, ?_, by linarith, ?_⟩
      · field_simp; ring
      · field_simp; nlinarith

theorem x8_phys_sep {a b c d w z : ℝ} (h : physicalX a b c d w z) (hw : w ^ 2 ≤ b * c)
    (hz : z ^ 2 ≤ a * d) : sep (xstate a b c d w z) := by
  obtain ⟨ha, hb, hc, hd, hw0, hz0, hs, h1, h2⟩ := h
  exact ⟨x8_ppt_sep ha hb hc hd hw0 hz0 h1 hw hz h2, by rw [x8_xs_trace, hs]; simp⟩

theorem x8_xsr {a b c d w z : ℝ} (h : physicalX a b c d w z) (standard : Bool) :
    robust {X | sep X} standard (xstate a b c d w z) =
      if b * c < w ^ 2 then branchValue b c w else if a * d < z ^ 2 then branchValue a d z else 0 := by
  have h' := h
  obtain ⟨ha, hb, hc, hd, hw0, hz0, hs, h1, h2⟩ := h'
  split_ifs with hw hz
  · obtain ⟨u0, v0, hsum, hpos, hppt⟩ := x8_weights hb hc hw0 hw
    apply x8_rob_eq
    · have := x8_mem h (le_refl 0) u0 v0 (le_refl 0) (by linarith) (by simpa using h1) hppt
        (by nlinarith) (by nlinarith) standard
      rwa [show (0:ℝ) + (weights b c w).1 + (weights b c w).2 + 0 = branchValue b c w by linarith] at this
    · intro s ω hs hω hm
      refine x8_branch_lb hb hc hw0 hw (fun p q hp hq => ?_)
      have := x8_lb1 hs hω hm hp hq
      simp [pt, xstate] at this
      linarith
  · obtain ⟨u0, v0, hsum, hpos, hppt⟩ := x8_weights ha hd hz0 hz
    push_neg at hw
    apply x8_rob_eq
    · have := x8_mem h u0 (le_refl 0) (le_refl 0) v0 (by linarith) (by nlinarith) (by simpa using hw)
        hppt (by simpa using h2) standard
      rwa [show (weights a d z).1 + 0 + 0 + (weights a d z).2 = branchValue a d z by linarith] at this
    · intro s ω hs hω hm
      refine x8_branch_lb ha hd hz0 hz (fun p q hp hq => ?_)
      have := x8_lb2 hs hω hm hp hq
      simp [pt, xstate] at this
      linarith
  · push_neg at hw hz
    have hX := x8_phys_sep h hw hz
    apply x8_rob_eq
    · refine ⟨le_refl 0, _, x8_phys_dens h, fun _ => hX, ?_⟩
      show sep _
      simpa [mix] using hX
    · intro s _ hs _ _; exact hs

theorem x8_main (a b c d w z : ℝ) (h : physicalX a b c d w z) :
  rs (xstate a b c d w z)=rg (xstate a b c d w z) ∧
  (a*d<z^2 → rg (xstate a b c d w z)=branchValue a d z) ∧
  (b*c<w^2 → rg (xstate a b c d w z)=branchValue b c w) ∧
  (z^2≤a*d → w^2≤b*c → rg (xstate a b c d w z)=0) := by
  have h' := h
  obtain ⟨ha, hb, hc, hd, hw0, hz0, hs, h1, h2⟩ := h'
  unfold rs rg
  rw [x8_xsr h true, x8_xsr h false]
  refine ⟨rfl, fun hz => ?_, fun hw => by rw [if_pos hw], fun hz hw => ?_⟩
  · have : ¬ b * c < w ^ 2 := by intro hw; nlinarith
    rw [if_neg this, if_pos hz]
  · rw [if_neg (not_lt.2 hw), if_neg (not_lt.2 hz)]

end QAlgorithms.Papers.Independent.Information100.P21

open QAlgorithms.Papers.Independent.Information100.P21 in
theorem solution (a b c d w z : ℝ) (h : physicalX a b c d w z) :
  rs (xstate a b c d w z)=rg (xstate a b c d w z) ∧
  (a*d<z^2 → rg (xstate a b c d w z)=branchValue a d z) ∧
  (b*c<w^2 → rg (xstate a b c d w z)=branchValue b c w) ∧
  (z^2≤a*d → w^2≤b*c → rg (xstate a b c d w z)=0) := x8_main a b c d w z h
