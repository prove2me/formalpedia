-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.proposition_6_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T23:41:22.606985+00:00
-- url     : https://prove2.me/submissions/86bd9940-645a-4f78-943a-522ca9887a9c

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

theorem x8_t_entry {d m : ℕ} (t : Map d) (E : Fin m → Mat d)
    (hE : ∀ X, applyMap t X = QAlgorithms.krausApply E X) (i j a b : Fin d) :
    t (i, j) (a, b) = ∑ l, E l i a * conj (E l j b) := by
  have h1 : applyMap t (Matrix.single a b 1) i j = t (i, j) (a, b) := by
    rw [x8_ap]
    simp [Matrix.single_apply, Fintype.sum_prod_type, ite_and, Finset.sum_ite_eq]
  rw [← h1, hE]
  simp [QAlgorithms.krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply, ite_and, Finset.sum_ite_eq]

theorem x8_adj_apply {d m : ℕ} (t : Map d) (E : Fin m → Mat d)
    (hE : ∀ X, applyMap t X = QAlgorithms.krausApply E X) (Y : Mat d) :
    applyMap tᴴ Y = ∑ l, (E l)ᴴ * Y * E l := by
  ext a b
  rw [x8_ap]
  simp only [Matrix.conjTranspose_apply, x8_t_entry t E hE]
  simp [Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem x8_inner_adj {d : ℕ} (t : Map d) (X Y : Mat d) :
    matrixInner Y (applyMap t X) = matrixInner (applyMap tᴴ Y) X := by
  have key : ∀ Y Z : Mat d, matrixInner Y Z =
      star (fun p : Fin d × Fin d => Y p.1 p.2) ⬝ᵥ (fun p => Z p.1 p.2) := by
    intro Y Z
    simp only [matrixInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      dotProduct, Fintype.sum_prod_type, Pi.star_apply]
    exact Finset.sum_comm
  have hv : ∀ (s : Map d) (X : Mat d),
      (fun p : Fin d × Fin d => applyMap s X p.1 p.2) = s *ᵥ (fun p => X p.1 p.2) := by
    intro s X; funext p; simp [x8_ap, Matrix.mulVec, dotProduct]
  rw [key, key, hv, hv, Matrix.dotProduct_mulVec, Matrix.star_mulVec,
    Matrix.conjTranspose_conjTranspose]

theorem x8_unital_kraus {d m : ℕ} {t : Map d} (ht : UnitalChannel t) (E : Fin m → Mat d)
    (hE : ∀ X, applyMap t X = QAlgorithms.krausApply E X) : ∑ l, E l * (E l)ᴴ = 1 := by
  have := ht.2
  rw [hE] at this
  simpa [QAlgorithms.krausApply] using this

theorem x8_adj_unital {d : ℕ} {t : Map d} (ht : UnitalChannel t) : UnitalChannel tᴴ := by
  obtain ⟨m, E, hK, hE⟩ := ht.1
  have hu := x8_unital_kraus ht E hE
  refine ⟨⟨m, fun l => (E l)ᴴ, ?_, ?_⟩, ?_⟩
  · unfold QAlgorithms.IsKrausFamily
    simpa only [Matrix.conjTranspose_conjTranspose] using hu
  · intro ρ
    rw [x8_adj_apply t E hE]
    simp [QAlgorithms.krausApply]
  · rw [x8_adj_apply t E hE]
    unfold QAlgorithms.IsKrausFamily at hK
    simpa using hK

section unital

variable {d : ℕ} {t : Map d} (ht : UnitalChannel t)
include ht

theorem x8_hp1 : ∀ B, (x8blk (x8L t) B).PosSemidef := by
  obtain ⟨m, E, -, hE⟩ := ht.1
  exact fun B => x8_blk_psd (x8_kpos_of_kraus t E hE 2) B

/-- a peripheral eigenvector lies in the two-sided multiplicative domain -/
theorem x8_mult (P : Mat d) (a : ℂ) (ha : ‖a‖ = 1) (hP : applyMap t P = a • P) (Z : Mat d) :
    applyMap t (Z * P) = applyMap t Z * applyMap t P ∧
    applyMap t (P * Z) = applyMap t P * applyMap t Z := by
  have hp1 := x8_hp1 ht
  have h11 : x8L t 1 = 1 := ht.2
  have htp := x8_tp_of_channel ht
  have hca : ‖(starRingEnd ℂ) a‖ = 1 := by rw [Complex.norm_conj]; exact ha
  have hPH : applyMap t Pᴴ = (starRingEnd ℂ) a • Pᴴ := by
    rw [← x8_L_apply, x8_herm (x8L t) hp1, x8_L_apply, hP, Matrix.conjTranspose_smul,
      RCLike.star_def]
  have e1 : x8L t (Pᴴ * P) = (x8L t P)ᴴ * x8L t P := by
    apply x8_tp_eq _ hp1 h11
    simp only [x8_L_apply, htp, hP, x8_trace_smulH a ha]
  have e2 : x8L t (Pᴴᴴ * Pᴴ) = (x8L t Pᴴ)ᴴ * x8L t Pᴴ := by
    apply x8_tp_eq _ hp1 h11
    simp only [x8_L_apply, htp, hPH, x8_trace_smulH _ hca]
  refine ⟨x8_mdom (x8L t) hp1 h11 P e1 Z, ?_⟩
  have hm := x8_mdom (x8L t) hp1 h11 Pᴴ e2 Zᴴ
  have hh := congrArg Matrix.conjTranspose hm
  rw [← x8_herm (x8L t) hp1, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose,
    ← x8_herm (x8L t) hp1, Matrix.conjTranspose_conjTranspose, ← x8_herm (x8L t) hp1,
    Matrix.conjTranspose_conjTranspose] at hh
  exact hh

theorem x8_mult_V (C : Mat d) (hC : C ∈ peripheral t) (Z : Mat d) :
    applyMap t (Z * C) = applyMap t Z * applyMap t C ∧
    applyMap t (C * Z) = applyMap t C * applyMap t Z := by
  induction hC using Submodule.span_induction with
  | mem P hP => obtain ⟨a, ha, hPa⟩ := hP; exact x8_mult ht P a ha hPa Z
  | zero => simp [← x8_L_apply]
  | add x y _ _ hx hy =>
    simp only [Matrix.mul_add, Matrix.add_mul, x8_ap_add, hx.1, hy.1, hx.2, hy.2]
    exact ⟨trivial, trivial⟩
  | smul c x _ hx =>
    simp only [Matrix.mul_smul, Matrix.smul_mul, x8_ap_smul, hx.1, hx.2]
    exact ⟨trivial, trivial⟩

theorem x8_V_inv : ∀ C ∈ peripheral t, applyMap t C ∈ peripheral t := by
  intro C hC
  induction hC using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨a, ha, hPa⟩ := hP
    rw [hPa]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, hPa⟩)
  | zero => simp [← x8_L_apply]
  | add x y _ _ hx hy => rw [x8_ap_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [x8_ap_smul]; exact Submodule.smul_mem _ _ hx

theorem x8_V_onto : ∀ C ∈ peripheral t, ∃ C' ∈ peripheral t, applyMap t C' = C := by
  intro C hC
  induction hC using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨a, ha, hPa⟩ := hP
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    refine ⟨a⁻¹ • P, Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, hPa⟩), ?_⟩
    rw [x8_ap_smul, hPa, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp [← x8_L_apply]⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨x' + y', Submodule.add_mem _ hx' hy', x8_ap_add _ _ _⟩
  | smul c x _ hx =>
    obtain ⟨x', hx', rfl⟩ := hx
    exact ⟨c • x', Submodule.smul_mem _ _ hx', x8_ap_smul _ _ _⟩

/-- the center of the peripheral space as a submodule -/
def x8Zc (t : Map d) : Submodule ℂ (Mat d) where
  carrier := center (peripheral t : Set (Mat d))
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨Submodule.add_mem _ hx hy, fun Y hY => ?_⟩
    rw [Matrix.add_mul, Matrix.mul_add, hx' Y hY, hy' Y hY]
  zero_mem' := ⟨Submodule.zero_mem _, fun Y _ => by simp⟩
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    refine ⟨Submodule.smul_mem _ _ hx, fun Y hY => ?_⟩
    rw [Matrix.smul_mul, Matrix.mul_smul, hx' Y hY]

omit ht in
theorem x8_mem_Zc (C : Mat d) : C ∈ x8Zc t ↔ C ∈ center (peripheral t : Set (Mat d)) := Iff.rfl

theorem x8_Zc_inv : ∀ C ∈ x8Zc t, applyMap t C ∈ x8Zc t := by
  rintro C ⟨hC, hC'⟩
  refine ⟨x8_V_inv ht C hC, fun Q hQ => ?_⟩
  obtain ⟨Q', hQ', rfl⟩ := x8_V_onto ht Q hQ
  rw [← (x8_mult_V ht Q' hQ' C).1, ← (x8_mult_V ht C hC Q').1, hC' Q' hQ']

theorem x8_Zc_onto : ∀ C ∈ x8Zc t, ∃ C' ∈ x8Zc t, applyMap t C' = C := by
  -- injective on the peripheral space, hence on the center, hence onto the center
  let f : peripheral t →ₗ[ℂ] peripheral t := (x8L t).restrict (fun C hC => x8_V_inv ht C hC)
  have hfs : Function.Surjective f := by
    rintro ⟨C, hC⟩
    obtain ⟨C', hC', h⟩ := x8_V_onto ht C hC
    exact ⟨⟨C', hC'⟩, Subtype.ext h⟩
  have hfi : Function.Injective f := LinearMap.injective_iff_surjective.mpr hfs
  let g : x8Zc t →ₗ[ℂ] x8Zc t := (x8L t).restrict (fun C hC => x8_Zc_inv ht C hC)
  have hgi : Function.Injective g := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    have h' : applyMap t x = applyMap t y := congrArg Subtype.val h
    have := @hfi ⟨x, hx.1⟩ ⟨y, hy.1⟩ (Subtype.ext h')
    have hxy : x = y := congrArg Subtype.val this
    subst hxy; rfl
  have hgs : Function.Surjective g := LinearMap.injective_iff_surjective.mp hgi
  intro C hC
  obtain ⟨⟨C', hC'⟩, h⟩ := hgs ⟨C, hC⟩
  exact ⟨C', hC', congrArg Subtype.val h⟩

theorem x8_S_inv : ∀ Y ∈ commutant (center (peripheral t : Set (Mat d))),
    applyMap t Y ∈ commutant (center (peripheral t : Set (Mat d))) := by
  intro Y hY C hC
  obtain ⟨C', hC', rfl⟩ := x8_Zc_onto ht C hC
  rw [← (x8_mult_V ht C' hC'.1 Y).1, ← (x8_mult_V ht C' hC'.1 Y).2, hY C' hC']

theorem x8_kraus_rel {m : ℕ} (E : Fin m → Mat d)
    (hE : ∀ X, applyMap t X = QAlgorithms.krausApply E X)
    (P : Mat d) (a : ℂ) (ha : ‖a‖ = 1) (hP : applyMap t P = a • P) :
    ∀ i, E i * P = a • (P * E i) := by
  have hp1 := x8_hp1 ht
  have h11 : x8L t 1 = 1 := ht.2
  have htp := x8_tp_of_channel ht
  have hca : ‖(starRingEnd ℂ) a‖ = 1 := by rw [Complex.norm_conj]; exact ha
  have haa : a * (starRingEnd ℂ) a = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]; simp
  have hPH : applyMap t Pᴴ = (starRingEnd ℂ) a • Pᴴ := by
    rw [← x8_L_apply, x8_herm (x8L t) hp1, x8_L_apply, hP, Matrix.conjTranspose_smul,
      RCLike.star_def]
  have e2 : x8L t (Pᴴᴴ * Pᴴ) = (x8L t Pᴴ)ᴴ * x8L t Pᴴ := by
    apply x8_tp_eq _ hp1 h11
    simp only [x8_L_apply, htp, hPH, x8_trace_smulH _ hca]
  have hPP : applyMap t (P * Pᴴ) = P * Pᴴ := by
    have := e2
    simp only [x8_L_apply, Matrix.conjTranspose_conjTranspose, hPH, Matrix.conjTranspose_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, RCLike.star_def, Complex.conj_conj] at this
    rw [this, mul_comm, haa, one_smul]
  have hu := x8_unital_kraus ht E hE
  have ht' : ∀ X, ∑ i, E i * X * (E i)ᴴ = applyMap t X := fun X => by
    rw [hE]; rfl
  set D : Fin m → Mat d := fun i => E i * P - a • (P * E i) with hD
  have hsum : ∑ i, D i * (D i)ᴴ = (∑ i, E i * (P * Pᴴ) * (E i)ᴴ) -
      (starRingEnd ℂ) a • ((∑ i, E i * P * (E i)ᴴ) * Pᴴ) -
      a • (P * ∑ i, E i * Pᴴ * (E i)ᴴ) +
      (a * (starRingEnd ℂ) a) • (P * (∑ i, E i * (E i)ᴴ) * Pᴴ) := by
    simp only [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hD, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc,
      RCLike.star_def]
    module
  have hsum0 : ∑ i, D i * (D i)ᴴ = 0 := by
    rw [hsum, ht', ht', ht', hu, hPP, hP, hPH, haa]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one, one_smul]
    rw [mul_comm, haa, one_smul]
    abel
  have htr : ∑ i, (D i * (D i)ᴴ).trace = 0 := by rw [← Matrix.trace_sum, hsum0, Matrix.trace_zero]
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ (D i * (D i)ᴴ).trace :=
    fun i _ => (Matrix.posSemidef_self_mul_conjTranspose (D i)).trace_nonneg
  intro i
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp htr i (Finset.mem_univ _)
  have := Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp h0
  exact sub_eq_zero.mp this

theorem x8_adj_eig (P : Mat d) (a : ℂ) (ha : ‖a‖ = 1) (hP : applyMap t P = a • P) :
    applyMap tᴴ P = (starRingEnd ℂ) a • P := by
  obtain ⟨m, E, hK, hE⟩ := ht.1
  have hp1 := x8_hp1 ht
  have hca : ‖(starRingEnd ℂ) a‖ = 1 := by rw [Complex.norm_conj]; exact ha
  have haa : (starRingEnd ℂ) a * a = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]; simp
  have hPH : applyMap t Pᴴ = (starRingEnd ℂ) a • Pᴴ := by
    rw [← x8_L_apply, x8_herm (x8L t) hp1, x8_L_apply, hP, Matrix.conjTranspose_smul,
      RCLike.star_def]
  have hr := x8_kraus_rel ht E hE Pᴴ _ hca hPH
  have hr' : ∀ i, (E i)ᴴ * P = (starRingEnd ℂ) a • (P * (E i)ᴴ) := by
    intro i
    have := congrArg Matrix.conjTranspose (hr i)
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_smul, RCLike.star_def, Complex.conj_conj] at this
    rw [this, smul_smul, haa, one_smul]
  rw [x8_adj_apply t E hE]
  simp_rw [hr', Matrix.smul_mul, Matrix.mul_assoc]
  rw [← Finset.smul_sum, ← Finset.mul_sum]
  unfold QAlgorithms.IsKrausFamily at hK
  rw [hK, Matrix.mul_one]

theorem x8_periph_adj : peripheral t ≤ peripheral tᴴ := by
  rw [peripheral, Submodule.span_le]
  rintro P ⟨a, ha, hP⟩
  exact Submodule.subset_span ⟨(starRingEnd ℂ) a, by rw [Complex.norm_conj]; exact ha,
    x8_adj_eig ht P a ha hP⟩

theorem x8_periph_eq : peripheral tᴴ = peripheral t := by
  apply le_antisymm _ (x8_periph_adj ht)
  have := x8_periph_adj (x8_adj_unital ht)
  rwa [Matrix.conjTranspose_conjTranspose] at this

theorem x8_prop63 : Reduces t (commutant (center (peripheral t : Set (Mat d)))) := by
  refine ⟨x8_S_inv ht, fun X hX Y hY => ?_⟩
  rw [x8_inner_adj]
  apply hX
  have := x8_S_inv (x8_adj_unital ht) Y
  rw [x8_periph_eq ht] at this
  exact this hY

end unital

end QAlgorithms.Papers.Independent.Information100.P26

open QAlgorithms.Papers.Independent.Information100.P26 in
theorem solution {d : ℕ} (_hd : 0 < d) (t : Map d) (ht : UnitalChannel t) :
    Reduces t (commutant (center (peripheral t : Set (Mat d)))) :=
  x8_prop63 ht
