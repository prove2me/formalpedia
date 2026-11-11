-- Prove2me | solution 1 for PauliUnclonable531.Pauli.filtered_product
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T10:38:31.585679+00:00
-- url     : https://prove2.me/submissions/c7e9756c-97a6-4f8d-bde4-fed6dec97200

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Correlations
import Theorems.Thm_PauliUnclonable531_Pauli_insert_powers
import Theorems.Thm_PauliUnclonable531_Pauli_filter_properties

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli.Resolvent



open PauliUnclonable531.Pauli
open scoped MatrixOrder

/-! ## Kronecker algebra -/

lemma kron_mul {a b c d e f : Type} [Fintype b] [Fintype e] (A : Matrix a b ℂ) (A' : Matrix b c ℂ)
    (Bm : Matrix d e ℂ) (B' : Matrix e f ℂ) :
    Matrix.kronecker A Bm * Matrix.kronecker A' B' = Matrix.kronecker (A * A') (Bm * B') :=
  (Matrix.mul_kronecker_mul A A' Bm B').symm

lemma kron_conjTranspose {X Y : Type} (x : Op X) (y : Op Y) :
    (Matrix.kronecker x y).conjTranspose = Matrix.kronecker x.conjTranspose y.conjTranspose :=
  Matrix.conjTranspose_kronecker x y

lemma kron_sub {l m p q : Type} (A : Matrix l m ℂ) (B₁ B₂ : Matrix p q ℂ) :
    Matrix.kronecker A (B₁ - B₂) = Matrix.kronecker A B₁ - Matrix.kronecker A B₂ := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [mul_sub]

lemma sub_kron {l m p q : Type} (A₁ A₂ : Matrix l m ℂ) (B : Matrix p q ℂ) :
    Matrix.kronecker (A₁ - A₂) B = Matrix.kronecker A₁ B - Matrix.kronecker A₂ B := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [sub_mul]

lemma kron_add {l m p q : Type} (A : Matrix l m ℂ) (B₁ B₂ : Matrix p q ℂ) :
    Matrix.kronecker A (B₁ + B₂) = Matrix.kronecker A B₁ + Matrix.kronecker A B₂ := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [mul_add]

lemma add_kron {l m p q : Type} (A₁ A₂ : Matrix l m ℂ) (B : Matrix p q ℂ) :
    Matrix.kronecker (A₁ + A₂) B = Matrix.kronecker A₁ B + Matrix.kronecker A₂ B := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [add_mul]

lemma smul_kron {l m p q : Type} (c : ℂ) (A : Matrix l m ℂ) (B : Matrix p q ℂ) :
    Matrix.kronecker (c • A) B = c • Matrix.kronecker A B := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [mul_assoc]

lemma kron_one_one {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] :
    Matrix.kronecker (1 : Op X) (1 : Op Y) = 1 := Matrix.one_kronecker_one

lemma psd_kron {X Y : Type} [Fintype X] [Fintype Y] {x : Op X} {y : Op Y}
    (hx : x.PosSemidef) (hy : y.PosSemidef) : (Matrix.kronecker x y).PosSemidef :=
  hx.kronecker hy

/-! ## Norm bounds from Loewner bounds -/

variable {A : Type} [Fintype A] [DecidableEq A]

lemma one_sub_sq_psd (X : Op A) (hX : X.IsHermitian) (h1 : (1 - X).PosSemidef)
    (h2 : (1 + X).PosSemidef) : (1 - X * X).PosSemidef := by
  have ha := h2.conjTranspose_mul_mul_same (1 - X)
  have hb := h1.conjTranspose_mul_mul_same (1 + X)
  have hsum := (ha.add hb).smul (show (0:ℝ) ≤ 1/2 by norm_num)
  have hc1 : (1 - X).conjTranspose = 1 - X := by simp [hX.eq]
  have hc2 : (1 + X).conjTranspose = 1 + X := by simp [hX.eq]
  rw [hc1, hc2] at hsum
  convert hsum using 1
  simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one]
  module

lemma norm_one_le : ‖(1 : Op A)‖ ≤ 1 := by
  rcases isEmpty_or_nonempty A with hA | hA
  · simp [Subsingleton.elim (1 : Op A) 0]
  · simp

lemma norm_le_one_of_contraction (X : Op A) (hX : X.IsHermitian) (h1 : (1 - X).PosSemidef)
    (h2 : (1 + X).PosSemidef) : ‖X‖ ≤ 1 := by
  have hsq : ‖X * X‖ ≤ ‖(1 : Op A)‖ := by
    apply CStarAlgebra.norm_le_norm_of_nonneg_of_le
    · have := Matrix.posSemidef_conjTranspose_mul_self X
      rw [hX.eq] at this
      exact this.nonneg
    · rw [Matrix.le_iff]; exact one_sub_sq_psd X hX h1 h2
  have : ‖X‖ * ‖X‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, Matrix.star_eq_conjTranspose, hX.eq]
    exact hsq.trans norm_one_le
  nlinarith [norm_nonneg X]

lemma norm_le_of_two_sided (X : Op A) (hX : X.IsHermitian) {c : ℝ} (hc : 0 < c)
    (h1 : (c • 1 - X).PosSemidef) (h2 : (c • 1 + X).PosSemidef) : ‖X‖ ≤ c := by
  have hY : (c⁻¹ • X).IsHermitian := by
    unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_smul, hX.eq]; simp
  have e1 : 1 - c⁻¹ • X = c⁻¹ • (c • 1 - X) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  have e2 : 1 + c⁻¹ • X = c⁻¹ • (c • 1 + X) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  have := norm_le_one_of_contraction (c⁻¹ • X) hY
    (by rw [e1]; exact h1.smul (inv_nonneg.mpr hc.le))
    (by rw [e2]; exact h2.smul (inv_nonneg.mpr hc.le))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)] at this
  rwa [inv_mul_le_iff₀ hc, mul_one] at this

/-- A positive semidefinite operator below `c • 1` has norm at most `c`. -/
lemma norm_le_of_psd_le (M : Op A) (hM : M.PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (h : (c • 1 - M).PosSemidef) : ‖M‖ ≤ c := by
  have := CStarAlgebra.norm_le_norm_of_nonneg_of_le hM.nonneg (Matrix.le_iff.mpr h)
  refine this.trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  exact mul_le_of_le_one_right hc norm_one_le



/-- Geometric expansion of the regularized resolvent: a uniform bound `ε` on the moments
`L Eˡ R` gives `‖L (s • 1 + (1 - E))⁻¹ R‖ ≤ ε / s` for `s > 0` and `‖E‖ ≤ 1`. -/
lemma resolvent_sandwich (E L R : Op A) (hE : ‖E‖ ≤ 1) {s ε : ℝ} (hs : 0 < s)
    (hdet : IsUnit (((s : ℂ)) • (1 : Op A) + (1 - E)).det)
    (hpow : ∀ ℓ : ℕ, ‖L * E ^ ℓ * R‖ ≤ ε) :
    ‖L * (((s : ℂ)) • (1 : Op A) + (1 - E))⁻¹ * R‖ ≤ ε / s := by
  set c : ℝ := (1 + s)⁻¹ with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : c < 1 := by rw [hc, inv_lt_one₀ (by linarith)]; linarith
  set x : Op A := ((c : ℂ)) • E with hx
  have hxn : ‖x‖ < 1 := by
    rw [hx, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    calc c * ‖E‖ ≤ c * 1 := mul_le_mul_of_nonneg_left hE hc0.le
      _ < 1 := by simpa using hc1
  have hgeom : HasSum (fun ℓ : ℕ => x ^ ℓ) (1 - x)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    exact hasSum_geom_series_inverse x hxn
  set M : Op A := ((s : ℂ)) • (1 : Op A) + (1 - E) with hM
  have hk : ((c : ℂ)) ≠ 0 := by exact_mod_cast hc0.ne'
  letI : Invertible ((c : ℂ)) := invertibleOfNonzero hk
  have hone : 1 - x = ((c : ℂ)) • M := by
    rw [hx, hM, smul_add, smul_sub, smul_smul, ← add_sub_assoc]
    congr 1
    rw [← add_smul, ← mul_add_one, show ((c : ℂ)) * ((s : ℂ) + 1) = 1 by
      rw [hc]; push_cast; field_simp; ring, one_smul]
  have hinv : ((c : ℂ)) • (1 - x)⁻¹ = M⁻¹ := by
    rw [hone, Matrix.inv_smul M _ hdet, smul_smul]
    simp
  have hsum := ((hgeom.const_smul ((c : ℂ))).mul_left L).mul_right R
  rw [hinv] at hsum
  rw [← hsum.tsum_eq]
  have hreal : HasSum (fun ℓ : ℕ => (c * ε) * c ^ ℓ) (ε / s) := by
    have e : c * ε * (1 - c)⁻¹ = ε / s := by
      have h1 : (1 : ℝ) + s ≠ 0 := by linarith
      have h2 : (1 : ℝ) - (1 + s)⁻¹ = s * (1 + s)⁻¹ := by field_simp; ring
      rw [hc, h2, mul_inv, inv_inv]
      field_simp
    rw [← e]
    exact (hasSum_geometric_of_lt_one hc0.le hc1).mul_left (c * ε)
  apply tsum_of_norm_bounded hreal
  intro ℓ
  have hterm : L * (((c : ℂ)) • x ^ ℓ) * R = ((c * c ^ ℓ : ℝ) : ℂ) • (L * E ^ ℓ * R) := by
    rw [hx, smul_pow, smul_smul, Matrix.mul_smul, Matrix.smul_mul]
    push_cast; ring_nf
  rw [hterm, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc c * c ^ ℓ * ‖L * E ^ ℓ * R‖ ≤ c * c ^ ℓ * ε :=
        mul_le_mul_of_nonneg_left (hpow ℓ) (by positivity)
    _ = c * ε * c ^ ℓ := by ring

end PauliUnclonable531.Pauli.Resolvent

open scoped MatrixOrder

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.Resolvent in
theorem solution {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] (n : ℕ) (hn : 1 ≤ n) (a : Decoders n B C) (t : ℝ) (ht : 0 < t) :
    PauliUnclonable531.Pauli.spectralNorm (EB a * filterOperator a t * EC a) ≤ gamma n := by
  unfold PauliUnclonable531.Pauli.spectralNorm
  have hγ : ∀ ℓ : ℕ, ‖EB a * EBC a ^ ℓ * EC a‖ ≤ gamma n := fun ℓ =>
    (insert_powers n hn a ℓ).1.trans (insert_powers n hn a ℓ).2
  obtain ⟨hApd, -, -, -, -⟩ := filter_properties n hn a t ht
  have hdet : IsUnit ((((2 * t : ℝ) : ℂ)) • (1 : Op (Bits n × (B × C))) + (1 - EBC a)).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).mp hApd.isUnit
    have e : (((2 * t : ℝ) : ℂ)) • (1 : Op (Bits n × (B × C))) + (1 - EBC a) =
        (2 * (t : ℂ)) • 1 + disagreement a := by
      unfold disagreement; push_cast; rfl
    rw [e]; exact this
  -- `‖EBC‖ ≤ 1`
  set b : Key n → Op (Bits n × (B × C)) := fun k =>
    Matrix.kronecker (1 : Op (Bits n)) (Matrix.kronecker (a.bob k) (1 : Op C))
  set c : Key n → Op (Bits n × (B × C)) := fun k =>
    Matrix.kronecker (1 : Op (Bits n)) (Matrix.kronecker (1 : Op B) (a.charlie k))
  have hbn : ∀ θ, ‖b θ‖ ≤ 1 := by
    intro θ
    apply norm_le_one_of_contraction
    · unfold Matrix.IsHermitian
      simp only [b, kron_conjTranspose, Matrix.conjTranspose_one, (a.bob_hermitian θ).eq]
    · have := psd_kron (Matrix.PosSemidef.one (n := Bits n))
        (psd_kron (a.bob_upper θ) (Matrix.PosSemidef.one (n := C)))
      simpa only [b, sub_kron, kron_sub, kron_one_one] using this
    · have h1 := a.bob_lower θ
      unfold Below at h1
      rw [sub_neg_eq_add, add_comm] at h1
      have := psd_kron (Matrix.PosSemidef.one (n := Bits n))
        (psd_kron h1 (Matrix.PosSemidef.one (n := C)))
      simpa only [b, add_kron, kron_add, kron_one_one] using this
  have hcn : ∀ θ, ‖c θ‖ ≤ 1 := by
    intro θ
    apply norm_le_one_of_contraction
    · unfold Matrix.IsHermitian
      simp only [c, kron_conjTranspose, Matrix.conjTranspose_one, (a.charlie_hermitian θ).eq]
    · have := psd_kron (Matrix.PosSemidef.one (n := Bits n))
        (psd_kron (Matrix.PosSemidef.one (n := B)) (a.charlie_upper θ))
      simpa only [c, sub_kron, kron_sub, kron_one_one] using this
    · have h1 := a.charlie_lower θ
      unfold Below at h1
      rw [sub_neg_eq_add, add_comm] at h1
      have := psd_kron (Matrix.PosSemidef.one (n := Bits n))
        (psd_kron (Matrix.PosSemidef.one (n := B)) h1)
      simpa only [c, add_kron, kron_add, kron_one_one] using this
  have hE : ‖EBC a‖ ≤ 1 := by
    unfold EBC
    have hK : (0 : ℝ) < Fintype.card (Key n) := by
      exact_mod_cast Fintype.card_pos_iff.mpr (⟨⟨(fun _ => 1, 0), by
        intro h; have := congrFun (congrArg Prod.fst h) ⟨0, hn⟩; simp at this⟩⟩ : Nonempty (Key n))
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    have hterm : ∀ k : Key n, ‖Matrix.kronecker (1 : Op (Bits n))
        (Matrix.kronecker (a.bob k) (a.charlie k))‖ ≤ 1 := by
      intro k
      have e : Matrix.kronecker (1 : Op (Bits n)) (Matrix.kronecker (a.bob k) (a.charlie k)) =
          b k * c k := by
        simp only [b, c, kron_mul, Matrix.mul_one, Matrix.one_mul]
      rw [e]
      calc ‖b k * c k‖ ≤ ‖b k‖ * ‖c k‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul (hbn k) (hcn k) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    calc (Fintype.card (Key n) : ℝ)⁻¹ * ‖∑ k : Key n, Matrix.kronecker (1 : Op (Bits n))
          (Matrix.kronecker (a.bob k) (a.charlie k))‖
        ≤ (Fintype.card (Key n) : ℝ)⁻¹ * ∑ _k : Key n, (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (norm_sum_le_of_le _ fun k _ => hterm k) (by positivity)
      _ = 1 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]; field_simp
  have h2t : (0 : ℝ) < 2 * t := by linarith
  have hres := resolvent_sandwich (EBC a) (EB a) (EC a) hE h2t hdet hγ
  have hF : filterOperator a t = (((2 * t : ℝ) : ℂ)) •
      ((((2 * t : ℝ) : ℂ)) • (1 : Op (Bits n × (B × C))) + (1 - EBC a))⁻¹ := by
    unfold filterOperator disagreement; push_cast; rfl
  rw [hF, Matrix.mul_smul, Matrix.smul_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos h2t]
  calc 2 * t * ‖EB a * ((((2 * t : ℝ) : ℂ)) • 1 + (1 - EBC a))⁻¹ * EC a‖
      ≤ 2 * t * (gamma n / (2 * t)) := mul_le_mul_of_nonneg_left hres h2t.le
    _ = gamma n := by field_simp
