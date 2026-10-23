-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.proposition_6_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T23:33:44.666766+00:00
-- url     : https://prove2.me/submissions/f13ab732-7afb-4912-a253-594c6e32da69

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

theorem x8_ap {d : ℕ} (t : Map d) (X : Mat d) (i j : Fin d) :
    applyMap t X i j = ∑ p : Fin d × Fin d, t (i, j) p * X p.1 p.2 := by
  simp [applyMap, QAlgorithms.act, Matrix.mulVec, dotProduct]

theorem x8_ap_add {d : ℕ} (t : Map d) (X Y : Mat d) :
    applyMap t (X + Y) = applyMap t X + applyMap t Y := by
  ext i j
  simp only [x8_ap, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem x8_ap_smul {d : ℕ} (t : Map d) (c : ℂ) (X : Mat d) :
    applyMap t (c • X) = c • applyMap t X := by
  ext i j
  simp only [x8_ap, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem x8_ap_mul {d : ℕ} (s r : Map d) (X : Mat d) :
    applyMap (s * r) X = applyMap s (applyMap r X) := by
  ext i j
  simp only [x8_ap, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  ring

theorem x8_ap_T {d : ℕ} (X : Mat d) : applyMap (transposition d) X = Xᵀ := by
  ext i j
  rw [x8_ap]
  simp [transposition, Prod.ext_iff, ite_and, Fintype.sum_prod_type, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Matrix.transpose_apply]

/-- Kraus maps are k-positive. -/
theorem x8_kpos_of_kraus {d m : ℕ} (t : Map d) (E : Fin m → Mat d)
    (hE : ∀ X, applyMap t X = QAlgorithms.krausApply E X) (k : ℕ) : KPositive k t := by
  have ht : ∀ i j a b, t (i, j) (a, b) = ∑ l, E l i a * conj (E l j b) := by
    intro i j a b
    have h1 : applyMap t (Matrix.single a b 1) i j = t (i, j) (a, b) := by
      rw [x8_ap]
      simp [Matrix.single_apply, Fintype.sum_prod_type, ite_and, Finset.sum_ite_eq]
    rw [← h1, hE]
    simp [QAlgorithms.krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
      Matrix.conjTranspose_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  intro Z hZ
  let L : Fin m → Matrix (Fin d × Fin k) (Fin d × Fin k) ℂ :=
    fun l => Matrix.kronecker (E l) (1 : Matrix (Fin k) (Fin k) ℂ)
  have hsum : amplify t k Z = ∑ l, L l * Z * (L l)ᴴ := by
    ext p q
    simp [amplify, ht, L, Matrix.mul_apply, Matrix.sum_apply, Matrix.kronecker,
      Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum,
      Matrix.conjTranspose_apply, apply_ite (starRingEnd ℂ), mul_ite, Finset.sum_ite_eq]
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [hsum]
  exact Matrix.posSemidef_sum _ fun l _ => hZ.mul_mul_conjTranspose_same (L l)

/-- block matrix of a map on a pair of matrices -/
def x8blk {d : ℕ} (φ : Mat d → Mat d) (A : Fin 2 → Mat d) :
    Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ :=
  fun p q => φ (A p.2 * (A q.2)ᴴ) p.1 q.1

theorem x8_blk_psd {d : ℕ} {t : Map d} (ht : KPositive 2 t) (A : Fin 2 → Mat d) :
    (x8blk (applyMap t) A).PosSemidef := by
  let B : Matrix (Fin d × Fin 2) (Fin d) ℂ := fun p c => A p.2 p.1 c
  have := ht _ (Matrix.posSemidef_self_mul_conjTranspose B)
  convert this using 1
  ext p q
  simp only [x8blk, amplify, x8_ap, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1

section core

variable {d : ℕ} (φ : Mat d →ₗ[ℂ] Mat d) (hpos : ∀ A, (x8blk φ A).PosSemidef) (h1 : φ 1 = 1)
include hpos

theorem x8_herm (Y : Mat d) : φ Yᴴ = (φ Y)ᴴ := by
  have hH := (hpos ![1, Yᴴ]).1
  ext i j
  have := hH.apply (j, 0) (i, 1)
  simp [x8blk] at this
  rw [Matrix.conjTranspose_apply, ← this]
  simp

include h1 in
theorem x8_schwarz (w : Mat d) : (φ (wᴴ * w) - (φ w)ᴴ * φ w).PosSemidef := by
  let V : Matrix (Fin d × Fin 2) (Fin d) ℂ :=
    Matrix.of fun p c => if p.2 = 0 then -(φ w) p.1 c else (1 : Mat d) p.1 c
  have hV := (hpos ![1, wᴴ]).conjTranspose_mul_mul_same V
  convert hV using 1
  have hw := x8_herm φ hpos w
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    V, x8blk, Matrix.of_apply]
  simp [h1, hw, Matrix.one_apply, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  ring

omit hpos in
theorem x8_polar (D : Mat d) (h : ∀ u : Fin d → ℂ, star u ⬝ᵥ (D *ᵥ u) = 0) : D = 0 := by
  have hq : ∀ (a b : Fin d) (c : ℂ), star (Pi.single a 1 + c • Pi.single b 1 : Fin d → ℂ) ⬝ᵥ
      (D *ᵥ (Pi.single a 1 + c • Pi.single b 1)) =
        D a a + c * D a b + conj c * D b a + conj c * c * D b b := by
    intro a b c
    simp only [dotProduct, Matrix.mulVec, Pi.add_apply, Pi.smul_apply, Pi.star_apply, star_add,
      star_smul, Pi.single_apply, smul_eq_mul, mul_add, add_mul, Finset.sum_add_distrib]
    simp [apply_ite (star : ℂ → ℂ), Finset.sum_ite_eq', Finset.sum_ite_eq]
    ring
  have hd : ∀ a, D a a = 0 := by
    intro a
    have := h (Pi.single a 1)
    simpa [dotProduct, Matrix.mulVec, Pi.single_apply, apply_ite (star : ℂ → ℂ)] using this
  ext a b
  have e1 := hq a b 1
  have e2 := hq a b Complex.I
  rw [h, hd, hd] at e1 e2
  simp only [map_one, Complex.conj_I] at e1 e2
  simp only [Matrix.zero_apply]
  have : (2 : ℂ) * D a b = 0 := by
    linear_combination -e1 + Complex.I * e2 + (D a b - D b a) * Complex.I_sq
  simpa using this

include h1 in
theorem x8_mdom (x : Mat d) (hx : φ (xᴴ * x) = (φ x)ᴴ * φ x) (y : Mat d) :
    φ (y * x) = φ y * φ x := by
  set D := φ (y * x) - φ y * φ x with hD
  set C := φ ((yᴴ)ᴴ * yᴴ) - (φ yᴴ)ᴴ * φ yᴴ with hC
  have hCp := x8_schwarz φ hpos h1 yᴴ
  have hy := x8_herm φ hpos y
  have hyx := x8_herm φ hpos (y * x)
  have hS : ∀ l : ℂ, φ ((x + l • yᴴ)ᴴ * (x + l • yᴴ)) - (φ (x + l • yᴴ))ᴴ * φ (x + l • yᴴ) =
      l • Dᴴ + conj l • D + (conj l * l) • C := by
    intro l
    simp only [hD, hC, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, map_add, map_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hx,
      smul_smul]
    have hyx' : φ (xᴴ * yᴴ) = (φ (y * x))ᴴ := by rw [← Matrix.conjTranspose_mul]; exact hyx
    simp only [hy, hyx', Matrix.conjTranspose_conjTranspose, RCLike.star_def]
    module
  apply sub_eq_zero.mp
  rw [← hD]
  apply x8_polar
  intro u
  set z := star u ⬝ᵥ (D *ᵥ u) with hz
  set c := star u ⬝ᵥ (C *ᵥ u) with hc
  have hc0 : 0 ≤ c := hCp.dotProduct_mulVec_nonneg u
  have hcre : c = (c.re : ℂ) := by
    apply Complex.ext <;> simp [(Complex.nonneg_iff.mp hc0).2.symm]
  have hcpos : 0 ≤ c.re := (Complex.nonneg_iff.mp hc0).1
  have hzH : star u ⬝ᵥ (Dᴴ *ᵥ u) = conj z := by
    simp only [hz, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Finset.mul_sum,
      map_sum, map_mul, Pi.star_apply, RCLike.star_def, Complex.conj_conj]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  set s : ℝ := 1 / (c.re + 1) with hs
  have hs0 : 0 < s := by positivity
  have hsc : s * c.re < 1 := by
    rw [hs, div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]; linarith
  have hw := (x8_schwarz φ hpos h1 (x + (-(s : ℂ) * z) • yᴴ)).dotProduct_mulVec_nonneg u
  rw [hS, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
    dotProduct_smul, hzH, ← hz, ← hc] at hw
  have hN : z * conj z = (Complex.normSq z : ℂ) := Complex.mul_conj z
  have hval : (-(s : ℂ) * z) • conj z + conj (-(s : ℂ) * z) • z +
      (conj (-(s : ℂ) * z) * (-(s : ℂ) * z)) • c =
        (((s ^ 2 * c.re - 2 * s) * Complex.normSq z : ℝ) : ℂ) := by
    rw [hcre]
    simp only [smul_eq_mul, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj]
    push_cast
    linear_combination ((s : ℂ) ^ 2 * (c.re : ℂ) - 2 * (s : ℂ)) * hN
  rw [hval] at hw
  have hre := Complex.zero_le_real.mp hw
  have hneg : s ^ 2 * c.re - 2 * s < 0 := by nlinarith
  have hn0 : Complex.normSq z = 0 := by
    have := Complex.normSq_nonneg z
    nlinarith
  exact Complex.normSq_eq_zero.mp hn0

end core

/-- applyMap as a linear map -/
def x8L {d : ℕ} (t : Map d) : Mat d →ₗ[ℂ] Mat d where
  toFun := applyMap t
  map_add' := x8_ap_add t
  map_smul' := x8_ap_smul t

theorem x8_L_apply {d : ℕ} (t : Map d) (X : Mat d) : x8L t X = applyMap t X := rfl

theorem x8_tT_apply {d : ℕ} (t : Map d) (X : Mat d) :
    applyMap (t * transposition d) X = applyMap t Xᵀ := by
  rw [x8_ap_mul, x8_ap_T]

theorem x8_main {d : ℕ} (A : Submodule ℂ (Mat d))
    (hA : CStar A) (hcomm : Commutative A) (t : Map d)
    (ht : UnitalChannel t) (hcop : TwoCopositive t) (hfix : Fixes t A) :
    ∀ X : Mat d, applyMap t X ∈ commutant (A : Set (Mat d)) := by
  intro X a ha
  obtain ⟨m, E, -, hE⟩ := ht.1
  have hk : KPositive 2 t := x8_kpos_of_kraus t E hE 2
  have hp1 : ∀ B, (x8blk (x8L t) B).PosSemidef := fun B => x8_blk_psd hk B
  have hp2 : ∀ B, (x8blk (x8L (t * transposition d)) B).PosSemidef := fun B => x8_blk_psd hcop B
  have h11 : x8L t 1 = 1 := ht.2
  have h12 : x8L (t * transposition d) 1 = 1 := by
    rw [x8_L_apply, x8_tT_apply, Matrix.transpose_one]; exact ht.2
  have haH : aᴴ ∈ A := hA.2.2 a ha
  have haa : a * aᴴ ∈ A := hA.2.1 a ha aᴴ haH
  have hfa : applyMap t a = a := hfix a ha
  have hfaH : applyMap t aᴴ = aᴴ := hfix aᴴ haH
  have hfaa : applyMap t (a * aᴴ) = a * aᴴ := hfix _ haa
  -- left multiplicativity
  have hL : applyMap t (a * X) = a * applyMap t X := by
    have hx : x8L t (aᴴᴴ * aᴴ) = (x8L t aᴴ)ᴴ * x8L t aᴴ := by
      simp only [x8_L_apply, Matrix.conjTranspose_conjTranspose, hfaa, hfaH]
    have hm := x8_mdom (x8L t) hp1 h11 aᴴ hx Xᴴ
    have hh := congrArg Matrix.conjTranspose hm
    rw [← x8_herm (x8L t) hp1, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose,
      ← x8_herm (x8L t) hp1, Matrix.conjTranspose_conjTranspose] at hh
    have hXH : (applyMap t Xᴴ)ᴴ = applyMap t X := by
      rw [← x8_L_apply, x8_herm (x8L t) hp1, Matrix.conjTranspose_conjTranspose, x8_L_apply]
    simpa only [x8_L_apply, hfaH, Matrix.conjTranspose_conjTranspose, hfa, hXH] using hh
  -- right multiplicativity through the co-map
  have hR : applyMap t (a * X) = applyMap t X * a := by
    have hx : x8L (t * transposition d) ((aᵀ)ᴴ * aᵀ) =
        (x8L (t * transposition d) aᵀ)ᴴ * x8L (t * transposition d) aᵀ := by
      simp only [x8_L_apply, x8_tT_apply, Matrix.transpose_mul, Matrix.transpose_transpose, hfa]
      have : ((aᵀ)ᴴ)ᵀ = aᴴ := by ext i j; simp
      rw [this, hfaa]
      exact hcomm a ha aᴴ haH
    have hm := x8_mdom (x8L (t * transposition d)) hp2 h12 aᵀ hx Xᵀ
    simpa only [x8_L_apply, x8_tT_apply, Matrix.transpose_mul, Matrix.transpose_transpose,
      hfa] using hm
  rw [← hL, hR]

/-- Schwarz equality from a trace identity. -/
theorem x8_tp_eq {d : ℕ} (φ : Mat d →ₗ[ℂ] Mat d) (hpos : ∀ A, (x8blk φ A).PosSemidef)
    (h1 : φ 1 = 1) (w : Mat d) (h : (φ (wᴴ * w)).trace = ((φ w)ᴴ * φ w).trace) :
    φ (wᴴ * w) = (φ w)ᴴ * φ w := by
  have hS := x8_schwarz φ hpos h1 w
  have h0 := hS.trace_eq_zero_iff.mp (by rw [Matrix.trace_sub, h, sub_self])
  exact sub_eq_zero.mp h0

theorem x8_tp_of_channel {d : ℕ} {t : Map d} (ht : UnitalChannel t) (X : Mat d) :
    (applyMap t X).trace = X.trace := by
  obtain ⟨m, E, hE, hE'⟩ := ht.1
  rw [hE']
  unfold QAlgorithms.krausApply
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (E _) X (E _)ᴴ]
  rw [← Matrix.trace_sum, ← Finset.sum_mul]
  unfold QAlgorithms.IsKrausFamily at hE
  rw [hE, Matrix.one_mul]

theorem x8_trace_HT {d : ℕ} (P : Mat d) : ((Pᵀ)ᴴ * Pᵀ).trace = (Pᴴ * P).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply]
  exact Finset.sum_comm

theorem x8_trace_smulH {d : ℕ} (a : ℂ) (ha : ‖a‖ = 1) (P : Mat d) :
    ((a • P)ᴴ * (a • P)).trace = (Pᴴ * P).trace := by
  have : star a * a = 1 := by
    rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]; simp
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, this, one_smul]

/-- the three multiplicativity relations of a peripheral eigenvector -/
theorem x8_periph {d : ℕ} {t : Map d} (ht : UnitalChannel t) (hcop : TwoCopositive t)
    (P : Mat d) (a : ℂ) (ha : ‖a‖ = 1) (hP : applyMap t P = a • P) (Z : Mat d) :
    applyMap t (P * Z) = a • (P * applyMap t Z) ∧
    applyMap t (P * Z) = a • (applyMap t Z * P) ∧
    applyMap t (Z * P) = a • (applyMap t Z * P) := by
  obtain ⟨m, E, -, hE⟩ := ht.1
  have hk : KPositive 2 t := x8_kpos_of_kraus t E hE 2
  have hp1 : ∀ B, (x8blk (x8L t) B).PosSemidef := fun B => x8_blk_psd hk B
  have hp2 : ∀ B, (x8blk (x8L (t * transposition d)) B).PosSemidef := fun B => x8_blk_psd hcop B
  have h11 : x8L t 1 = 1 := ht.2
  have h12 : x8L (t * transposition d) 1 = 1 := by
    rw [x8_L_apply, x8_tT_apply, Matrix.transpose_one]; exact ht.2
  have htp := x8_tp_of_channel ht
  have hca : ‖(starRingEnd ℂ) a‖ = 1 := by rw [Complex.norm_conj]; exact ha
  have hPH : applyMap t Pᴴ = (starRingEnd ℂ) a • Pᴴ := by
    rw [← x8_L_apply, x8_herm (x8L t) hp1, x8_L_apply, hP, Matrix.conjTranspose_smul,
      RCLike.star_def]
  -- Schwarz equalities
  have e1 : x8L t (Pᴴ * P) = (x8L t P)ᴴ * x8L t P := by
    apply x8_tp_eq _ hp1 h11
    simp only [x8_L_apply, htp, hP, x8_trace_smulH a ha]
  have e2 : x8L t (Pᴴᴴ * Pᴴ) = (x8L t Pᴴ)ᴴ * x8L t Pᴴ := by
    apply x8_tp_eq _ hp1 h11
    simp only [x8_L_apply, htp, hPH, x8_trace_smulH _ hca]
  have e3 : x8L (t * transposition d) ((Pᵀ)ᴴ * Pᵀ) =
      (x8L (t * transposition d) Pᵀ)ᴴ * x8L (t * transposition d) Pᵀ := by
    apply x8_tp_eq _ hp2 h12
    simp only [x8_L_apply, x8_tT_apply, htp, Matrix.trace_transpose, Matrix.transpose_transpose,
      hP, x8_trace_smulH a ha, x8_trace_HT]
  refine ⟨?_, ?_, ?_⟩
  · -- left multiplicativity from Pᴴ
    have hm := x8_mdom (x8L t) hp1 h11 Pᴴ e2 Zᴴ
    have hh := congrArg Matrix.conjTranspose hm
    rw [← x8_herm (x8L t) hp1, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose,
      ← x8_herm (x8L t) hp1, Matrix.conjTranspose_conjTranspose] at hh
    have hZH : (applyMap t Zᴴ)ᴴ = applyMap t Z := by
      rw [← x8_L_apply, x8_herm (x8L t) hp1, Matrix.conjTranspose_conjTranspose, x8_L_apply]
    simp only [x8_L_apply, hPH, hZH, Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose,
      RCLike.star_def, Complex.conj_conj, Matrix.smul_mul] at hh
    rw [hh, hP, Matrix.smul_mul]
  · have hm := x8_mdom (x8L (t * transposition d)) hp2 h12 Pᵀ e3 Zᵀ
    simpa only [x8_L_apply, x8_tT_apply, Matrix.transpose_mul, Matrix.transpose_transpose, hP,
      Matrix.mul_smul] using hm
  · have hm := x8_mdom (x8L t) hp1 h11 P e1 Z
    simpa only [x8_L_apply, hP, Matrix.mul_smul] using hm

theorem x8_herm_t {d : ℕ} {t : Map d} (ht : UnitalChannel t) (Y : Mat d) :
    applyMap t Yᴴ = (applyMap t Y)ᴴ := by
  obtain ⟨m, E, -, hE⟩ := ht.1
  exact x8_herm (x8L t) (fun B => x8_blk_psd (x8_kpos_of_kraus t E hE 2) B) Y

theorem x8_prop68 {d : ℕ} {t : Map d} (ht : UnitalChannel t) (hcop : TwoCopositive t)
    (X : Mat d) : applyMap t X ∈ commutant (peripheral t : Set (Mat d)) := by
  intro Y hY
  induction hY using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨a, ha, hPa⟩ := hP
    obtain ⟨h1, h2, -⟩ := x8_periph ht hcop P a ha hPa X
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    rw [h1] at h2
    exact (smul_right_injective (Mat d) ha0 h2).symm
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul, hx, hy]
  | smul c x _ hx => rw [Matrix.mul_smul, Matrix.smul_mul, hx]

theorem x8_prop64 {d : ℕ} {t : Map d} (ht : UnitalChannel t) (hcop : TwoCopositive t) :
    CStar (peripheral t) ∧ Commutative (peripheral t) := by
  have hG : ∀ P Q : Mat d, (∃ a : ℂ, ‖a‖ = 1 ∧ applyMap t P = a • P) →
      (∃ b : ℂ, ‖b‖ = 1 ∧ applyMap t Q = b • Q) →
      (∃ c : ℂ, ‖c‖ = 1 ∧ applyMap t (P * Q) = c • (P * Q)) ∧ P * Q = Q * P := by
    rintro P Q ⟨a, ha, hPa⟩ ⟨b, hb, hQb⟩
    obtain ⟨h1, h2, -⟩ := x8_periph ht hcop P a ha hPa Q
    rw [hQb] at h1 h2
    refine ⟨⟨a * b, by rw [norm_mul, ha, hb, one_mul], ?_⟩, ?_⟩
    · rw [h1, Matrix.mul_smul, smul_smul]
    · have ha0 : a ≠ 0 := by rintro rfl; simp at ha
      have hb0 : b ≠ 0 := by rintro rfl; simp at hb
      rw [h1, Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul] at h2
      exact smul_right_injective (Mat d) (mul_ne_zero ha0 hb0) h2
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact Submodule.subset_span ⟨1, by simp, by rw [ht.2, one_smul]⟩
  · intro X hX Y hY
    induction hX using Submodule.span_induction with
    | mem P hP =>
      induction hY using Submodule.span_induction with
      | mem Q hQ => exact Submodule.subset_span (hG P Q hP hQ).1
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mul_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ _ hx
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ _ hx
  · intro X hX
    induction hX using Submodule.span_induction with
    | mem P hP =>
      obtain ⟨a, ha, hPa⟩ := hP
      refine Submodule.subset_span ⟨(starRingEnd ℂ) a, by rw [Complex.norm_conj]; exact ha, ?_⟩
      rw [x8_herm_t ht, hPa, Matrix.conjTranspose_smul, RCLike.star_def]
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.conjTranspose_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.conjTranspose_smul]; exact Submodule.smul_mem _ _ hx
  · intro X hX Y hY
    induction hX using Submodule.span_induction with
    | mem P hP =>
      induction hY using Submodule.span_induction with
      | mem Q hQ => exact (hG P Q hP hQ).2
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul, hx, hy]
      | smul c x _ hx => rw [Matrix.mul_smul, Matrix.smul_mul, hx]
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul, hx, hy]
    | smul c x _ hx => rw [Matrix.mul_smul, Matrix.smul_mul, hx]

end QAlgorithms.Papers.Independent.Information100.P26

open QAlgorithms.Papers.Independent.Information100.P26 in
theorem solution {d : ℕ} (_hd : 0 < d) (t : Map d) (ht : UnitalChannel t)
    (hcop : TwoCopositive t) : CStar (peripheral t) ∧ Commutative (peripheral t) :=
  x8_prop64 ht hcop
