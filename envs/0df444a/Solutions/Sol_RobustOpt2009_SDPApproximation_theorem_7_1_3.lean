-- Prove2me | solution 1 for RobustOpt2009.SDPApproximation.theorem_7_1_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T06:31:41.825714+00:00
-- url     : https://prove2.me/submissions/f681ac27-ba8b-4fe0-9c67-e775628a54b4

import Theorems.Thm_RobustOpt2009_SDPApproximation_theorem_7_1_3_ii

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RLMI713Aux

theorem opsq {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℝ) (hZ : ‖Z‖ ≤ 1) (b : Fin q → ℝ) :
    (Z *ᵥ b) ⬝ᵥ (Z *ᵥ b) ≤ b ⬝ᵥ b := by
  have h := Matrix.l2_opNorm_mulVec Z ((EuclideanSpace.equiv (Fin q) ℝ).symm b)
  have h2 : ‖(EuclideanSpace.equiv (Fin p) ℝ).symm (Z *ᵥ b)‖ ≤
      ‖(EuclideanSpace.equiv (Fin q) ℝ).symm b‖ := by
    calc _ ≤ ‖Z‖ * ‖(EuclideanSpace.equiv (Fin q) ℝ).symm b‖ := by simpa using h
      _ ≤ 1 * _ := by gcongr
      _ = _ := one_mul _
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h3
  simpa [dotProduct, sq] using h3

theorem trq {a b : ℕ} (x : Fin a → ℝ) (M : Matrix (Fin b) (Fin a) ℝ) (y : Fin b → ℝ) :
    x ⬝ᵥ (Mᵀ *ᵥ y) = (M *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, vecMul_transpose]

theorem symm_part {m p q : ℕ} (L : Matrix (Fin p) (Fin m) ℝ) (R : Matrix (Fin q) (Fin m) ℝ)
    (Z : Matrix (Fin p) (Fin q) ℝ) : (Lᵀ * Z * R + Rᵀ * Zᵀ * L).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_eq_transpose_of_trivial]
  simp [transpose_add, transpose_mul, Matrix.mul_assoc, add_comm]

theorem psd_sum {m k : ℕ} (M : Fin k → Matrix (Fin m) (Fin m) ℝ) (h : ∀ i, (M i).PosSemidef) :
    (∑ i, M i).PosSemidef :=
  Finset.sum_induction M (fun X => X.PosSemidef) (fun _ _ ha hb => ha.add hb)
    PosSemidef.zero (fun i _ => h i)

/-- `ρ U + z B ⪰ 0` when `U ⪰ ±B` and `|z| ≤ ρ`. -/
theorem scal_term {m : ℕ} (U B : Matrix (Fin m) (Fin m) ℝ) (h1 : (U - B).PosSemidef)
    (h2 : (U + B).PosSemidef) (ρ z : ℝ) (hz : |z| ≤ ρ) : (ρ • U + z • B).PosSemidef := by
  have ha : 0 ≤ (ρ + z) / 2 := by have := neg_abs_le z; linarith
  have hb : 0 ≤ (ρ - z) / 2 := by have := le_abs_self z; linarith
  have := (h2.smul ha).add (h1.smul hb)
  convert this using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- `ρ V + (Lᵀ Z R + Rᵀ Zᵀ L) ⪰ 0` when `V` dominates the unit full block and `‖Z‖ ≤ ρ`. -/
theorem full_term {m p q : ℕ} (L : Matrix (Fin p) (Fin m) ℝ) (R : Matrix (Fin q) (Fin m) ℝ)
    (V : Matrix (Fin m) (Fin m) ℝ)
    (hV : ∀ Z : Matrix (Fin p) (Fin q) ℝ, ‖Z‖ ≤ 1 → (V - (Lᵀ * Z * R + Rᵀ * Zᵀ * L)).PosSemidef)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (Z : Matrix (Fin p) (Fin q) ℝ) (hZ : ‖Z‖ ≤ ρ) :
    (ρ • V + (Lᵀ * Z * R + Rᵀ * Zᵀ * L)).PosSemidef := by
  rcases hρ.lt_or_eq with hρ | hρ
  · have hZ' : ‖-(ρ⁻¹ • Z)‖ ≤ 1 := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hρ)]
      calc ρ⁻¹ * ‖Z‖ ≤ ρ⁻¹ * ρ := by gcongr
        _ = 1 := inv_mul_cancel₀ hρ.ne'
    have := (hV _ hZ').smul hρ.le
    convert this using 1
    simp only [transpose_neg, transpose_smul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_add, smul_sub, smul_neg, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
    abel
  · subst hρ
    have : Z = 0 := norm_le_zero_iff.mp hZ
    subst this
    simpa using PosSemidef.zero

theorem herm_smul {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsHermitian) (c : ℝ) :
    (c • A).IsHermitian := by
  unfold IsHermitian; rw [conjTranspose_smul, hA.eq, star_trivial]

/-- For `ρ = 0` a single full block admits the certificate `V = LᵀL + RᵀR`. -/
theorem full_cert {m p q : ℕ} (L : Matrix (Fin p) (Fin m) ℝ) (R : Matrix (Fin q) (Fin m) ℝ)
    (Z : Matrix (Fin p) (Fin q) ℝ) (hZ : ‖Z‖ ≤ 1) :
    (Lᵀ * L + Rᵀ * R - (Lᵀ * Z * R + Rᵀ * Zᵀ * L)).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine IsHermitian.sub ?_ (symm_part L R Z)
    unfold IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]
    simp [transpose_add, transpose_mul]
  · have hc := opsq Z hZ (R *ᵥ x)
    have hsq : 0 ≤ (L *ᵥ x - Z *ᵥ (R *ᵥ x)) ⬝ᵥ (L *ᵥ x - Z *ᵥ (R *ᵥ x)) := by
      simpa using dotProduct_star_self_nonneg (L *ᵥ x - Z *ᵥ (R *ᵥ x))
    simp only [star_trivial, sub_mulVec, add_mulVec, dotProduct_sub, dotProduct_add, sub_dotProduct,
      ← mulVec_mulVec, trq] at hsq ⊢
    have e1 : (L *ᵥ x) ⬝ᵥ (Z *ᵥ (R *ᵥ x)) = (Z *ᵥ (R *ᵥ x)) ⬝ᵥ (L *ᵥ x) := dotProduct_comm _ _
    have e2 : (R *ᵥ x) ⬝ᵥ (Zᵀ *ᵥ (L *ᵥ x)) = (Z *ᵥ (R *ᵥ x)) ⬝ᵥ (L *ᵥ x) := by rw [trq]
    linarith

theorem part_i {m s f : ℕ} {p q : Fin f → ℕ}
    (B₀ : Matrix (Fin m) (Fin m) ℝ) (B : Fin s → Matrix (Fin m) (Fin m) ℝ)
    (L : (j : Fin f) → Matrix (Fin (p j)) (Fin m) ℝ)
    (R : (j : Fin f) → Matrix (Fin (q j)) (Fin m) ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (U : Fin s → Matrix (Fin m) (Fin m) ℝ) (V : Fin f → Matrix (Fin m) (Fin m) ℝ)
    (hUB : ∀ i, (U i - B i).PosSemidef ∧ (U i + B i).PosSemidef)
    (hV : ∀ j, ∀ Z : Matrix (Fin (p j)) (Fin (q j)) ℝ, ‖Z‖ ≤ 1 →
            (V j - ((L j)ᵀ * Z * R j + (R j)ᵀ * Zᵀ * L j)).PosSemidef)
    (hfin : (B₀ - ρ • (∑ i, U i) - ρ • (∑ j, V j)).PosSemidef)
    (z : Fin s → ℝ) (Z : (j : Fin f) → Matrix (Fin (p j)) (Fin (q j)) ℝ)
    (hz : ∀ i, |z i| ≤ ρ) (hZ : ∀ j, ‖Z j‖ ≤ ρ) :
    (B₀ + (∑ i, z i • B i) +
      ∑ j, ((L j)ᵀ * Z j * R j + (R j)ᵀ * (Z j)ᵀ * L j)).PosSemidef := by
  have h1 := psd_sum _ fun i => scal_term (U i) (B i) (hUB i).1 (hUB i).2 ρ (z i) (hz i)
  have h2 := psd_sum _ fun j => full_term (L j) (R j) (V j) (hV j) ρ hρ (Z j) (hZ j)
  have := (hfin.add h1).add h2
  convert this using 1
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum]
  abel

end RLMI713Aux

open RLMI713Aux

theorem solution :
    ∃ θ : ℕ → ℝ, Monotone θ ∧ θ 2 = Real.pi / 2 ∧ θ 4 = 2 ∧
      (∀ μ : ℕ, 2 ≤ μ → θ μ ≤ Real.pi * Real.sqrt ((μ : ℝ) / 2)) ∧
      ∀ (m s f : ℕ), 0 < m → ∀ (p q : Fin f → ℕ),
      (∀ j, 0 < p j) → (∀ j, 0 < q j) →
      ∀ (B₀ : Matrix (Fin m) (Fin m) ℝ) (B : Fin s → Matrix (Fin m) (Fin m) ℝ)
        (L : (j : Fin f) → Matrix (Fin (p j)) (Fin m) ℝ)
        (R : (j : Fin f) → Matrix (Fin (q j)) (Fin m) ℝ),
      B₀.IsHermitian → (∀ i, (B i).IsHermitian) → ∀ ρ : ℝ, 0 ≤ ρ →
      let a : ℝ → Prop := fun r =>
        ∀ (z : Fin s → ℝ) (Z : (j : Fin f) → Matrix (Fin (p j)) (Fin (q j)) ℝ),
          (∀ i, |z i| ≤ r) → (∀ j, ‖Z j‖ ≤ r) →
          (B₀ + (∑ i, z i • B i) +
            ∑ j, ((L j)ᵀ * Z j * R j + (R j)ᵀ * (Z j)ᵀ * L j)).PosSemidef
      let b : Prop :=
        ∃ (U : Fin s → Matrix (Fin m) (Fin m) ℝ)
          (V : Fin f → Matrix (Fin m) (Fin m) ℝ),
          (∀ i, (U i).IsHermitian) ∧ (∀ j, (V j).IsHermitian) ∧
          (∀ i, (U i - B i).PosSemidef ∧ (U i + B i).PosSemidef) ∧
          (∀ j, ∀ Z : Matrix (Fin (p j)) (Fin (q j)) ℝ, ‖Z‖ ≤ 1 →
            (V j - ((L j)ᵀ * Z * R j + (R j)ᵀ * Zᵀ * L j)).PosSemidef) ∧
          (B₀ - ρ • (∑ i, U i) - ρ • (∑ j, V j)).PosSemidef
      (b → a ρ) ∧ (s + f = 1 → (b ↔ a ρ)) ∧
      (∀ μ : ℕ, 2 ≤ μ → (∀ i, (B i).rank ≤ μ) → ¬ b → ¬ a (θ μ * ρ)) := by
  obtain ⟨θ, hmono, h2, h4, hle, H⟩ := RobustOpt2009.SDPApproximation.theorem_7_1_3_ii
  refine ⟨θ, hmono, h2, h4, hle, ?_⟩
  intro m s f hm p q hp hq B₀ B L R hB₀ hB ρ hρ a b
  have hsuff : b → a ρ := by
    rintro ⟨U, V, -, -, hUB, hV, hfin⟩ z Z hz hZ
    exact part_i B₀ B L R ρ hρ U V hUB hV hfin z Z hz hZ
  refine ⟨hsuff, fun h1 => ⟨hsuff, fun ha => ?_⟩, H m s f hm p q hp hq B₀ B L R hB₀ hB ρ hρ⟩
  rcases (by omega : (s = 1 ∧ f = 0) ∨ (s = 0 ∧ f = 1)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- one scalar block
    have hpm : ∀ t : ℝ, |t| ≤ ρ → (B₀ + t • B 0).PosSemidef := by
      intro t ht
      simpa using ha (fun _ => t) (fun j => j.elim0) (fun _ => ht) (fun j => j.elim0)
    rcases hρ.lt_or_eq with hρ' | hρ'
    · refine ⟨fun _ => ρ⁻¹ • B₀, fun j => j.elim0, fun _ => herm_smul _ hB₀ _, fun j => j.elim0,
        fun i => ?_, fun j => j.elim0, ?_⟩
      · obtain rfl : i = 0 := Subsingleton.elim _ _
        have hm := (hpm (-ρ) (by simp [abs_of_nonneg hρ])).smul (inv_nonneg.2 hρ)
        have hp' := (hpm ρ (by simp [abs_of_nonneg hρ])).smul (inv_nonneg.2 hρ)
        rw [smul_add, smul_smul] at hm hp'
        rw [mul_neg, inv_mul_cancel₀ hρ'.ne', neg_smul, one_smul] at hm
        rw [inv_mul_cancel₀ hρ'.ne', one_smul] at hp'
        exact ⟨by simpa [sub_eq_add_neg] using hm, by simpa using hp'⟩
      · simp [smul_smul, mul_inv_cancel₀ hρ'.ne', PosSemidef.zero]
    · subst hρ'
      have h0 := hpm 0 (by simp)
      simp only [zero_smul, add_zero] at h0
      refine ⟨fun _ => (1 / 2 : ℝ) • (B 0 * B 0 + 1), fun j => j.elim0, fun _ => ?_,
        fun j => j.elim0, fun i => ?_, fun j => j.elim0, by simpa using h0⟩
      · refine herm_smul _ ?_ _
        unfold IsHermitian; rw [conjTranspose_add, conjTranspose_mul, (hB 0).eq, conjTranspose_one]
      · obtain rfl : i = 0 := Subsingleton.elim _ _
        have hA := (posSemidef_conjTranspose_mul_self (B 0 - 1)).smul (by norm_num : (0:ℝ) ≤ 1 / 2)
        have hC := (posSemidef_conjTranspose_mul_self (B 0 + 1)).smul (by norm_num : (0:ℝ) ≤ 1 / 2)
        rw [conjTranspose_sub, (hB 0).eq, conjTranspose_one] at hA
        rw [conjTranspose_add, (hB 0).eq, conjTranspose_one] at hC
        refine ⟨?_, ?_⟩
        · convert hA using 1
          simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one]
          module
        · convert hC using 1
          simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one]
          module
  · -- one full block
    have hfz : ∀ W : Matrix (Fin (p 0)) (Fin (q 0)) ℝ, ‖W‖ ≤ ρ →
        (B₀ + ((L 0)ᵀ * W * R 0 + (R 0)ᵀ * Wᵀ * L 0)).PosSemidef := by
      intro W hW
      have := ha (fun i => i.elim0)
        (fun j => Fin.cases (motive := fun j => Matrix (Fin (p j)) (Fin (q j)) ℝ) W
          (fun i => i.elim0) j) (fun i => i.elim0)
        (fun j => Fin.cases (motive := fun j => ‖Fin.cases (motive := fun j =>
            Matrix (Fin (p j)) (Fin (q j)) ℝ) W (fun i => i.elim0) j‖ ≤ ρ) hW
          (fun i => i.elim0) j)
      simpa using this
    have h0 : B₀.PosSemidef := by simpa using hfz 0 (by simpa using hρ)
    rcases hρ.lt_or_eq with hρ' | hρ'
    · refine ⟨fun i => i.elim0, fun _ => ρ⁻¹ • B₀, fun i => i.elim0, fun _ => herm_smul _ hB₀ _,
        fun i => i.elim0, fun j Z hZ => ?_, ?_⟩
      · obtain rfl : j = 0 := Subsingleton.elim _ _
        have hW : ‖-(ρ • Z)‖ ≤ ρ := by
          rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hρ']
          calc ρ * ‖Z‖ ≤ ρ * 1 := by gcongr
            _ = ρ := mul_one ρ
        have := (hfz _ hW).smul (inv_nonneg.2 hρ)
        convert this using 1
        simp only [transpose_neg, transpose_smul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
          Matrix.smul_mul, smul_add, smul_neg, smul_smul, inv_mul_cancel₀ hρ'.ne', one_smul]
        abel
      · simp [smul_smul, mul_inv_cancel₀ hρ'.ne', PosSemidef.zero]
    · subst hρ'
      refine ⟨fun i => i.elim0, fun j => (L j)ᵀ * L j + (R j)ᵀ * R j, fun i => i.elim0,
        fun j => ?_, fun i => i.elim0, fun j Z hZ => full_cert (L j) (R j) Z hZ, by simpa using h0⟩
      unfold IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]
      simp [transpose_add, transpose_mul]
