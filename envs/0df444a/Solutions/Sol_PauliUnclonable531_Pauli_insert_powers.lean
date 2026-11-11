-- Prove2me | solution 1 for PauliUnclonable531.Pauli.insert_powers
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T10:34:15.65461+00:00
-- url     : https://prove2.me/submissions/cfc3cd4c-33d4-410e-98a1-d0355372adfb

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Correlations
import Theorems.Thm_PauliUnclonable531_Pauli_correlation_product

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli.Words


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


/-! ## Ordered words -/

variable {κ : Type} [Fintype κ]

def ordProd (f : κ → Op A) : List κ → Op A
  | [] => 1
  | θ :: w => f θ * ordProd f w

lemma comm_word (f g : κ → Op A) (hfg : ∀ θ φ, f θ * g φ = g φ * f θ) (θ : κ) (w : List κ) :
    f θ * ordProd g w = ordProd g w * f θ := by
  induction w with
  | nil => simp [ordProd]
  | cons φ w ih =>
    simp only [ordProd]
    rw [← Matrix.mul_assoc, hfg, Matrix.mul_assoc, ih, Matrix.mul_assoc]

lemma words_comm (f g : κ → Op A) (hfg : ∀ θ φ, f θ * g φ = g φ * f θ) (w v : List κ) :
    ordProd f w * ordProd g v = ordProd g v * ordProd f w := by
  induction w with
  | nil => simp [ordProd]
  | cons θ w ih =>
    simp only [ordProd]
    rw [Matrix.mul_assoc, ih, ← Matrix.mul_assoc, comm_word f g hfg, Matrix.mul_assoc]

lemma split_word (f g : κ → Op A) (hfg : ∀ θ φ, f θ * g φ = g φ * f θ) (w : List κ) :
    ordProd (fun θ => f θ * g θ) w = ordProd f w * ordProd g w := by
  induction w with
  | nil => simp [ordProd]
  | cons θ w ih =>
    simp only [ordProd]
    rw [ih]
    have hc := comm_word g f (fun φ ψ => (hfg ψ φ).symm) θ w
    calc f θ * g θ * (ordProd f w * ordProd g w)
        = f θ * (g θ * ordProd f w) * ordProd g w := by simp only [Matrix.mul_assoc]
      _ = f θ * (ordProd f w * g θ) * ordProd g w := by rw [hc]
      _ = f θ * ordProd f w * (g θ * ordProd g w) := by simp only [Matrix.mul_assoc]

lemma word_norm_le (f : κ → Op A) (hf : ∀ θ, ‖f θ‖ ≤ 1) (w : List κ) : ‖ordProd f w‖ ≤ 1 := by
  induction w with
  | nil => exact norm_one_le
  | cons θ w ih =>
    simp only [ordProd]
    calc ‖f θ * ordProd f w‖ ≤ ‖f θ‖ * ‖ordProd f w‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul (hf θ) ih (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- Normalized average with the complex weight used by the mission's definitions. -/
noncomputable def avg (f : κ → Op A) : Op A := (Fintype.card κ : ℂ)⁻¹ • ∑ θ, f θ

lemma avg_comm (f : κ → Op A) (X : Op A) (h : ∀ θ, f θ * X = X * f θ) :
    avg f * X = X * avg f := by
  unfold avg
  rw [Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul, Finset.mul_sum]
  simp only [h]

lemma avg_norm_le [Nonempty κ] (f : κ → Op A) {ε : ℝ} (hε : 0 ≤ ε) (hf : ∀ θ, ‖f θ‖ ≤ ε) :
    ‖avg f‖ ≤ ε := by
  unfold avg
  have hcard : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  calc (Fintype.card κ : ℝ)⁻¹ * ‖∑ θ, f θ‖ ≤ (Fintype.card κ : ℝ)⁻¹ * ∑ _θ : κ, ε :=
        mul_le_mul_of_nonneg_left (norm_sum_le_of_le _ fun θ _ => hf θ) (inv_nonneg.mpr hcard.le)
    _ = ε := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

lemma mul_avg (X : Op A) (f : κ → Op A) : X * avg f = avg (fun θ => X * f θ) := by
  unfold avg; rw [Matrix.mul_smul, Finset.mul_sum]

lemma avg_mul (f : κ → Op A) (X : Op A) : avg f * X = avg (fun θ => f θ * X) := by
  unfold avg; rw [Matrix.smul_mul, Finset.sum_mul]

lemma ordProd_append (f : κ → Op A) (w : List κ) (θ : κ) :
    ordProd f (w ++ [θ]) = ordProd f w * f θ := by
  induction w with
  | nil => simp [ordProd]
  | cons φ w ih => simp only [List.cons_append, ordProd, ih, Matrix.mul_assoc]

lemma pow_sandwich_aux [Nonempty κ] (f : κ → Op A) (L R : Op A) {ε : ℝ} (hε : 0 ≤ ε)
    (hword : ∀ w : List κ, ‖L * ordProd f w * R‖ ≤ ε) (ℓ : ℕ) (w : List κ) :
    ‖L * (ordProd f w * avg f ^ ℓ) * R‖ ≤ ε := by
  induction ℓ generalizing w with
  | zero => simpa [Matrix.mul_assoc] using hword w
  | succ ℓ ih =>
    have e : ordProd f w * avg f ^ (ℓ + 1) =
        avg (fun θ => ordProd f (w ++ [θ]) * avg f ^ ℓ) := by
      rw [pow_succ', ← Matrix.mul_assoc, mul_avg, avg_mul]
      congr 1
      funext θ
      rw [ordProd_append]
    rw [e, mul_avg, avg_mul]
    exact avg_norm_le _ hε fun θ => ih (w ++ [θ])

end PauliUnclonable531.Pauli.Words

open scoped MatrixOrder

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.Words in
theorem solution {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] (n : ℕ) (hn : 1 ≤ n) (a : Decoders n B C) (ℓ : ℕ) :
    PauliUnclonable531.Pauli.spectralNorm (EB a * EBC a ^ ℓ * EC a) ≤
      PauliUnclonable531.Pauli.spectralNorm (EB a * EC a) ∧
    PauliUnclonable531.Pauli.spectralNorm (EB a * EC a) ≤ gamma n := by
  refine ⟨?_, correlation_product n hn a⟩
  unfold PauliUnclonable531.Pauli.spectralNorm
  haveI : Nonempty (Key n) := ⟨⟨(fun _ => 1, 0), by
    intro h; have := congrFun (congrArg Prod.fst h) ⟨0, hn⟩; simp at this⟩⟩
  set U : Key n → Op (Bits n × (B × C)) := fun k =>
    Matrix.kronecker (pauli k.val).transpose (Matrix.kronecker (a.bob k) (1 : Op C))
  set V : Key n → Op (Bits n × (B × C)) := fun k =>
    Matrix.kronecker (pauli k.val).transpose (Matrix.kronecker (1 : Op B) (a.charlie k))
  set b : Key n → Op (Bits n × (B × C)) := fun k =>
    Matrix.kronecker (1 : Op (Bits n)) (Matrix.kronecker (a.bob k) (1 : Op C))
  set c : Key n → Op (Bits n × (B × C)) := fun k =>
    Matrix.kronecker (1 : Op (Bits n)) (Matrix.kronecker (1 : Op B) (a.charlie k))
  have hEB : EB a = avg U := rfl
  have hEC : EC a = avg V := rfl
  have hEBC : EBC a = avg (fun k => b k * c k) := by
    unfold EBC avg
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [b, c, kron_mul, Matrix.mul_one, Matrix.one_mul]
  have hbc : ∀ θ φ, b θ * c φ = c φ * b θ := by
    intro θ φ; simp only [b, c, kron_mul, Matrix.mul_one, Matrix.one_mul]
  have hUc : ∀ θ φ, U θ * c φ = c φ * U θ := by
    intro θ φ; simp only [U, c, kron_mul, Matrix.mul_one, Matrix.one_mul]
  have hbV : ∀ θ φ, b θ * V φ = V φ * b θ := by
    intro θ φ; simp only [V, b, kron_mul, Matrix.mul_one, Matrix.one_mul]
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
  -- each ordered word obeys the product bound
  have hword : ∀ w : List (Key n),
      ‖EB a * ordProd (fun θ => b θ * c θ) w * EC a‖ ≤ ‖EB a * EC a‖ := by
    intro w
    rw [split_word b c hbc w]
    have h1 : EB a * ordProd c w = ordProd c w * EB a := by
      rw [hEB]
      apply avg_comm
      intro θ
      exact comm_word (fun θ => U θ) c hUc θ w
    have h2 : ordProd b w * EC a = EC a * ordProd b w := by
      rw [hEC]
      symm
      apply avg_comm
      intro θ
      exact comm_word (fun θ => V θ) b (fun θ φ => (hbV φ θ).symm) θ w
    have h3 : ordProd b w * ordProd c w = ordProd c w * ordProd b w := words_comm b c hbc w w
    have hid : EB a * (ordProd b w * ordProd c w) * EC a =
        ordProd c w * (EB a * EC a) * ordProd b w := by
      calc EB a * (ordProd b w * ordProd c w) * EC a
          = EB a * (ordProd c w * ordProd b w) * EC a := by rw [h3]
        _ = (EB a * ordProd c w) * (ordProd b w * EC a) := by simp only [Matrix.mul_assoc]
        _ = (ordProd c w * EB a) * (EC a * ordProd b w) := by rw [h1, h2]
        _ = ordProd c w * (EB a * EC a) * ordProd b w := by simp only [Matrix.mul_assoc]
    rw [hid]
    calc ‖ordProd c w * (EB a * EC a) * ordProd b w‖
        ≤ ‖ordProd c w‖ * ‖EB a * EC a‖ * ‖ordProd b w‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ 1 * ‖EB a * EC a‖ * 1 := by
          gcongr
          · exact word_norm_le c hcn w
          · exact word_norm_le b hbn w
      _ = ‖EB a * EC a‖ := by ring
  have := pow_sandwich_aux (fun θ => b θ * c θ) (EB a) (EC a) (norm_nonneg _) hword ℓ []
  rw [hEBC]
  simpa [ordProd, Matrix.mul_assoc] using this
