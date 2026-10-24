-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.bellDifferentOptimizers
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T11:11:47.640841+00:00
-- url     : https://prove2.me/submissions/1ccc54c7-6f67-45fa-9114-239010672c63

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

theorem x8_vdens1 (u : Fin 2 → ℂ) (hu : Complex.normSq (u 0) + Complex.normSq (u 1) = 1) :
    QAlgorithms.IsDensityMatrix (Matrix.vecMulVec u (star u)) := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star u, ?_⟩
  simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Fin.sum_univ_two,
    Pi.star_apply, RCLike.star_def, Complex.mul_conj]
  rw [← Complex.ofReal_add, hu]; norm_num

def x8e0 : Fin 2 → ℂ := ![1, 0]
def x8e1 : Fin 2 → ℂ := ![0, 1]
def x8P0 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.vecMulVec x8e0 (star x8e0)
def x8P1 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.vecMulVec x8e1 (star x8e1)

theorem x8_P0d : QAlgorithms.IsDensityMatrix x8P0 := x8_vdens1 _ (by simp [x8e0])
theorem x8_P1d : QAlgorithms.IsDensityMatrix x8P1 := x8_vdens1 _ (by simp [x8e1])

theorem x8_ys_eq : xstate 0 (1/2) (1/2) 0 0 0 =
    ∑ j : Fin 2, (((fun _ : Fin 2 => (1/2 : ℝ)) j : ℝ) : ℂ) •
      Matrix.kronecker (![x8P0, x8P1] j) (![x8P1, x8P0] j) := by
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    x8P0, x8P1, Matrix.vecMulVec_apply, x8e0, x8e1]
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp [xstate]

theorem x8_ys_sep : sep (xstate 0 (1/2) (1/2) 0 0 0) := by
  refine ⟨⟨2, fun _ => 1/2, ![x8P0, x8P1], ![x8P1, x8P0], fun _ => by norm_num, fun j => ?_, x8_ys_eq⟩, ?_⟩
  · fin_cases j
    · exact ⟨x8_P0d, x8_P1d⟩
    · exact ⟨x8_P1d, x8_P0d⟩
  · rw [x8_xs_trace]; norm_num

theorem x8_ys_dens : QAlgorithms.IsDensityMatrix (xstate 0 (1/2) (1/2) 0 0 0) :=
  ⟨x8_xs_psd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    by rw [x8_xs_trace]; norm_num⟩

theorem x8_bell_rob (standard : Bool) :
    robust {X | sep X} standard (xstate (1/2) 0 0 (1/2) (1/2) 0) = 1 := by
  unfold robust
  apply le_antisymm
  · exact csInf_le ⟨0, fun s hs => hs.1⟩
      ⟨zero_le_one, _, x8_ys_dens, fun _ => x8_ys_sep, x8_bell_sep⟩
  · exact le_csInf ⟨1, zero_le_one, _, x8_ys_dens, fun _ => x8_ys_sep, x8_bell_sep⟩
      (fun s ⟨hs, ω, hω, _, hm⟩ => x8_bell_lb hs hω hm)

theorem x8_core :
  rs (xstate (1/2) 0 0 (1/2) (1/2) 0)=1 ∧ rg (xstate (1/2) 0 0 (1/2) (1/2) 0)=1 ∧
  optG (xstate (1/2) 0 0 (1/2) (1/2) 0) (xstate 0 (1/2) (1/2) 0 0 0) ∧
  optG (xstate (1/2) 0 0 (1/2) (1/2) 0) (xstate (1/2) 0 0 (1/2) (-1/2) 0) ∧
  QAlgorithms.IsDensityMatrix (xstate 0 (1/2) (1/2) 0 0 0) ∧
  QAlgorithms.IsDensityMatrix (xstate (1/2) 0 0 (1/2) (-1/2) 0) ∧
  sep (xstate 0 (1/2) (1/2) 0 0 0) ∧ ¬sep (xstate (1/2) 0 0 (1/2) (-1/2) 0) ∧
  xstate 0 (1/2) (1/2) 0 0 0 ≠ xstate (1/2) 0 0 (1/2) (-1/2) 0 := by
  have hrs : rs (xstate (1/2) 0 0 (1/2) (1/2) 0) = 1 := x8_bell_rob true
  have hrg : rg (xstate (1/2) 0 0 (1/2) (1/2) 0) = 1 := x8_bell_rob false
  refine ⟨hrs, hrg, ⟨⟨x8_ys_dens.1, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩, x8_ys_dens, ⟨?_, ?_⟩, x8_ys_sep, ?_, ?_⟩
  · rw [x8_xs_pt, x8_xs_pt, x8_xs_add]
    exact x8_xs_psd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [hrg, x8_xs_trace]; norm_num
  · exact x8_xs_psd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [x8_xs_pt, x8_xs_pt, x8_xs_add]
    exact x8_xs_psd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [hrg, x8_xs_trace]; norm_num
  · exact x8_xs_psd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [x8_xs_trace]; norm_num
  · intro h
    have := x8_psd_pair (x8_sep_pt h.1) (0,1) (1,0) (by decide) 1
    simp [pt, xstate] at this
    norm_num at this
  · intro h
    have := congrFun (congrFun h (0,0)) (0,0)
    simp [xstate] at this

theorem x8_main :
  let vplus : Vec QQ := ((Real.sqrt 2)⁻¹:ℂ) • (QAlgorithms.ket (0,0)+QAlgorithms.ket (1,1))
  let vminus : Vec QQ := ((Real.sqrt 2)⁻¹:ℂ) • (QAlgorithms.ket (0,0)-QAlgorithms.ket (1,1))
  let rho := proj vplus
  let Ysep := compressed true (1/2) (1/2)
  let Yent := proj vminus
  rs rho=1 ∧ rg rho=1 ∧ optG rho Ysep ∧ optG rho Yent ∧
  QAlgorithms.IsDensityMatrix Ysep ∧ QAlgorithms.IsDensityMatrix Yent ∧
  sep Ysep ∧ ¬sep Yent ∧ Ysep≠Yent := by
  intro vplus vminus rho Ysep Yent
  have h1 : rho = xstate (1/2) 0 0 (1/2) (1/2) 0 := x8_vplus
  have h2 : Ysep = xstate 0 (1/2) (1/2) 0 0 0 := x8_ysep
  have h3 : Yent = xstate (1/2) 0 0 (1/2) (-1/2) 0 := x8_vminus
  rw [h1, h2, h3]
  exact x8_core

end QAlgorithms.Papers.Independent.Information100.P21

open QAlgorithms.Papers.Independent.Information100.P21 in
theorem solution :
  let vplus : Vec QQ := ((Real.sqrt 2)⁻¹:ℂ) • (QAlgorithms.ket (0,0)+QAlgorithms.ket (1,1))
  let vminus : Vec QQ := ((Real.sqrt 2)⁻¹:ℂ) • (QAlgorithms.ket (0,0)-QAlgorithms.ket (1,1))
  let rho := proj vplus
  let Ysep := compressed true (1/2) (1/2)
  let Yent := proj vminus
  rs rho=1 ∧ rg rho=1 ∧ optG rho Ysep ∧ optG rho Yent ∧
  QAlgorithms.IsDensityMatrix Ysep ∧ QAlgorithms.IsDensityMatrix Yent ∧
  sep Ysep ∧ ¬sep Yent ∧ Ysep≠Yent := x8_main
