-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P13.inverse_condition_blocks
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T03:00:34.271266+00:00
-- url     : https://prove2.me/submissions/5482d0fd-e500-426a-af3f-783240d6a2b0

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P13
noncomputable section

open Filter MeasureTheory

open scoped BigOperators Topology ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.Papers.Independent.Gap48.P13

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]


set_option linter.unusedSectionVars false

theorem g75h_blk {α β : Type*} (M N : Mat (I ⊕ (J ⊕ K))) (f : α → I ⊕ (J ⊕ K))
    (g : β → I ⊕ (J ⊕ K)) :
    (M * N).submatrix f g = M.submatrix f in1 * N.submatrix in1 g +
      M.submatrix f in2 * N.submatrix in2 g + M.submatrix f in3 * N.submatrix in3 g := by
  ext x y
  simp [Matrix.mul_apply, Fintype.sum_sum_type, in1, in2, in3, add_assoc]

theorem g75h_blk2 {α β : Type*} (M N : Mat (J ⊕ K)) (f : α → J ⊕ K) (g : β → J ⊕ K) :
    (M * N).submatrix f g = M.submatrix f Sum.inl * N.submatrix Sum.inl g +
      M.submatrix f Sum.inr * N.submatrix Sum.inr g := by
  ext x y
  simp [Matrix.mul_apply, Fintype.sum_sum_type]

theorem g75h_sadd {L α β : Type*} (M N : Matrix L L ℂ) (f : α → L) (g : β → L) :
    (M + N).submatrix f g = M.submatrix f g + N.submatrix f g := rfl

theorem g75h_hblk (M : Mat (I ⊕ (J ⊕ K))) (h : Mᴴ = M) {α β : Type*}
    (f : α → I ⊕ (J ⊕ K)) (g : β → I ⊕ (J ⊕ K)) :
    M.submatrix f g = (M.submatrix g f)ᴴ := by
  ext x y
  rw [Matrix.conjTranspose_apply, Matrix.submatrix_apply, Matrix.submatrix_apply]
  conv_lhs => rw [← h]
  rfl

theorem solution (A : Mat (I ⊕ (J ⊕ K))) (hA : A.PosDef)
    (hcondition : A⁻¹ * (1 + A) * dMatrix A * (1 + dMatrix A)⁻¹ =
      (bMatrix A)⁻¹ * (1 + bMatrix A) * cMatrix A * (1 + cMatrix A)⁻¹) :
    a13 A = a12 A * (a22 A)⁻¹ * a23 A ∧
    a13 A = a12 A * (a22 A + 1)⁻¹ * a23 A := by
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
  have hAa : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hAu
  have haA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAu
  have haH : (A⁻¹)ᴴ = A⁻¹ := hA.1.inv
  have h22 : (a22 A).PosDef := hA.submatrix (fun x y h => by simpa [in2] using h)
  have h22u : IsUnit (a22 A).det := (Matrix.isUnit_iff_isUnit_det _).1 h22.isUnit
  have hp1 : (a22 A)⁻¹ * a22 A = 1 := Matrix.nonsing_inv_mul _ h22u
  have hq : (1 + a22 A).PosDef := Matrix.PosDef.posSemidef_add Matrix.PosSemidef.one h22
  have hqu : IsUnit (1 + a22 A).det := (Matrix.isUnit_iff_isUnit_det _).1 hq.isUnit
  have hq1 : (1 + a22 A)⁻¹ * (1 + a22 A) = 1 := Matrix.nonsing_inv_mul _ hqu
  have hq2 : (1 + a22 A) * (1 + a22 A)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hqu
  have hG : (1 + marginal23 A).PosDef :=
    Matrix.PosDef.posSemidef_add Matrix.PosSemidef.one (hA.submatrix Sum.inr_injective)
  have hGu : IsUnit (1 + marginal23 A).det := (Matrix.isUnit_iff_isUnit_det _).1 hG.isUnit
  have hG2 : (1 + marginal23 A) * (1 + marginal23 A)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hGu
  set G := (1 + marginal23 A)⁻¹ with hGdef
  set q := (1 + a22 A)⁻¹ with hqdef
  have hD : (1 + dMatrix A)⁻¹ = Matrix.fromBlocks ((1/2 : ℂ) • 1) 0 0 G := by
    apply Matrix.inv_eq_right_inv
    ext x y
    rcases x with x | x <;> rcases y with y | y
    · simp [dMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
      split_ifs <;> norm_num
    · simp [dMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    · simp [dMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    · simp [dMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
      have := congrFun (congrFun hG2 x) y
      simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] using this
  have hY : dMatrix A * (1 + dMatrix A)⁻¹ = Matrix.fromBlocks ((1/2 : ℂ) • 1) 0 0 (1 - G) := by
    rw [hD, dMatrix, Matrix.fromBlocks_multiply]
    have h1 : marginal23 A * G = 1 - G := by
      rw [Matrix.add_mul, Matrix.one_mul] at hG2
      exact eq_sub_of_add_eq' hG2
    simp [h1]
  have hC : (1 + cMatrix A)⁻¹ = diagonal3 ((1/2 : ℂ) • 1) q ((1/2 : ℂ) • 1) := by
    apply Matrix.inv_eq_right_inv
    ext x y
    rcases x with x | x | x <;> rcases y with y | y | y <;>
      simp [cMatrix, diagonal3, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    all_goals first
      | (have := congrFun (congrFun hq2 x) y
         simpa [Matrix.mul_apply, Matrix.one_apply] using this)
      | (split_ifs <;> norm_num)
  have hZ : cMatrix A * (1 + cMatrix A)⁻¹ =
      diagonal3 ((1/2 : ℂ) • 1) (a22 A * q) ((1/2 : ℂ) • 1) := by
    rw [hC, cMatrix, diagonal3, diagonal3, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
    rfl
  have hE : (A⁻¹ + 1) * Matrix.fromBlocks ((1/2 : ℂ) • 1) 0 0 (1 - G) =
      ((bMatrix A)⁻¹ + (bMatrix A)⁻¹ * bMatrix A) *
        diagonal3 ((1/2 : ℂ) • 1) (a22 A * q) ((1/2 : ℂ) • 1) := by
    have e1 : A⁻¹ * (1 + A) = A⁻¹ + 1 := by rw [Matrix.mul_add, Matrix.mul_one, haA]
    have e2 : (bMatrix A)⁻¹ * (1 + bMatrix A) =
        (bMatrix A)⁻¹ + (bMatrix A)⁻¹ * bMatrix A := by rw [Matrix.mul_add, Matrix.mul_one]
    rw [e1, e2, Matrix.mul_assoc (A⁻¹ + 1) (dMatrix A),
      Matrix.mul_assoc ((bMatrix A)⁻¹ + (bMatrix A)⁻¹ * bMatrix A) (cMatrix A), hY, hZ]
      at hcondition
    exact hcondition
  have o31 : (1 : Mat (I ⊕ (J ⊕ K))).submatrix in3 in1 = 0 := by
    ext x y; simp [in1, in3, Matrix.one_apply]
  have o13 : (1 : Mat (I ⊕ (J ⊕ K))).submatrix in1 in3 = 0 := by
    ext x y; simp [in1, in3, Matrix.one_apply]
  have o12 : (1 : Mat (I ⊕ (J ⊕ K))).submatrix in1 in2 = 0 := by
    ext x y; simp [in1, in2, Matrix.one_apply]
  have o23 : (1 : Mat (I ⊕ (J ⊕ K))).submatrix in2 in3 = 0 := by
    ext x y; simp [in2, in3, Matrix.one_apply]
  have o11 : (1 : Mat (I ⊕ (J ⊕ K))).submatrix in1 in1 = 1 := by
    ext x y; simp [in1, Matrix.one_apply]
  have o33 : (1 : Mat (I ⊕ (J ⊕ K))).submatrix in3 in3 = 1 := by
    ext x y; simp [in3, Matrix.one_apply]
  have hb : ((bMatrix A)⁻¹ + (bMatrix A)⁻¹ * bMatrix A).submatrix in3 in1 = 0 ∧
      ((bMatrix A)⁻¹ + (bMatrix A)⁻¹ * bMatrix A).submatrix in1 in3 = 0 := by
    by_cases hu : IsUnit (bMatrix A).det
    · have h1 := Matrix.mul_nonsing_inv _ hu
      have h2 := Matrix.nonsing_inv_mul _ hu
      have e31 := congrArg (fun M => M.submatrix in3 in1) h1
      have e13 := congrArg (fun M => M.submatrix in1 in3) h2
      simp only [g75h_blk] at e31 e13
      have b31 : (bMatrix A).submatrix in3 in1 = 0 := by ext x y; rfl
      have b32 : (bMatrix A).submatrix in3 in2 = 0 := by ext x y; rfl
      have b33 : (bMatrix A).submatrix in3 in3 = 1 := by
        ext x y; simp [bMatrix, assemble3, in3, Matrix.one_apply]
      have b13 : (bMatrix A).submatrix in1 in3 = 0 := by ext x y; rfl
      have b23 : (bMatrix A).submatrix in2 in3 = 0 := by ext x y; rfl
      rw [b31, b32, b33, o31] at e31
      rw [b13, b23, b33, o13] at e13
      simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul,
        zero_add] at e31 e13
      rw [h2, g75h_sadd, g75h_sadd, e31, e13, o31, o13]
      simp
    · rw [Matrix.nonsing_inv_apply_not_isUnit _ hu]
      simp
  obtain ⟨hb31, hb13⟩ := hb
  have E31 := congrArg (fun M => M.submatrix in3 in1) hE
  have E13 := congrArg (fun M => M.submatrix in1 in3) hE
  simp only [g75h_blk] at E31 E13
  have Y11 : (Matrix.fromBlocks ((1/2 : ℂ) • (1 : Mat I)) 0 0 (1 - G)).submatrix in1 in1 =
      (1/2 : ℂ) • 1 := by ext x y; rfl
  have Y21 : (Matrix.fromBlocks ((1/2 : ℂ) • (1 : Mat I)) 0 0 (1 - G)).submatrix in2 in1 = 0 := by
    ext x y; rfl
  have Y31 : (Matrix.fromBlocks ((1/2 : ℂ) • (1 : Mat I)) 0 0 (1 - G)).submatrix in3 in1 = 0 := by
    ext x y; rfl
  have Y13 : (Matrix.fromBlocks ((1/2 : ℂ) • (1 : Mat I)) 0 0 (1 - G)).submatrix in1 in3 = 0 := by
    ext x y; rfl
  have Y23 : (Matrix.fromBlocks ((1/2 : ℂ) • (1 : Mat I)) 0 0 (1 - G)).submatrix in2 in3 =
      -(G.submatrix Sum.inl Sum.inr) := by
    ext x y; simp [in2, in3, Matrix.one_apply]
  have Z21 : (diagonal3 ((1/2 : ℂ) • (1 : Mat I)) (a22 A * q) ((1/2 : ℂ) • (1 : Mat K))).submatrix in2 in1
      = 0 := by ext x y; rfl
  have Z31 : (diagonal3 ((1/2 : ℂ) • (1 : Mat I)) (a22 A * q) ((1/2 : ℂ) • (1 : Mat K))).submatrix in3 in1
      = 0 := by ext x y; rfl
  have Z13 : (diagonal3 ((1/2 : ℂ) • (1 : Mat I)) (a22 A * q) ((1/2 : ℂ) • (1 : Mat K))).submatrix in1 in3
      = 0 := by ext x y; rfl
  have Z23 : (diagonal3 ((1/2 : ℂ) • (1 : Mat I)) (a22 A * q) ((1/2 : ℂ) • (1 : Mat K))).submatrix in2 in3
      = 0 := by ext x y; rfl
  rw [Y11, Y21, Y31, Z21, Z31, hb31] at E31
  rw [Y13, Y23, Z13, Z23, hb13] at E13
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, g75h_sadd,
    o31, o13, o12] at E31 E13
  rw [Matrix.mul_smul, Matrix.mul_one, smul_eq_zero] at E31
  have hx31 : A⁻¹.submatrix in3 in1 = 0 := E31.resolve_left (by norm_num)
  have hx13 : A⁻¹.submatrix in1 in3 = 0 := by
    rw [g75h_hblk _ haH, hx31, Matrix.conjTranspose_zero]
  rw [hx13] at E13
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg,
    neg_eq_zero] at E13
  -- E13 : A⁻¹.submatrix in1 in2 * G.submatrix Sum.inl Sum.inr = 0
  have F13 := congrArg (fun M => M.submatrix in1 in3) hAa
  have F23 := congrArg (fun M => M.submatrix in2 in3) hAa
  have F33 := congrArg (fun M => M.submatrix in3 in3) hAa
  have H11 := congrArg (fun M => M.submatrix in1 in1) haA
  have H12 := congrArg (fun M => M.submatrix in1 in2) haA
  simp only [g75h_blk, hx13, o13, o23, o33, o11, o12, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero] at F13 F23 F33 H11 H12
  have hp1' : (a22 A)⁻¹ * A.submatrix in2 in2 = 1 := hp1
  have hp2' : A.submatrix in2 in2 * (a22 A)⁻¹ = 1 := mul_eq_one_comm.mp hp1
  have hx23 : A⁻¹.submatrix in2 in3 =
      -((a22 A)⁻¹ * A.submatrix in2 in3 * A⁻¹.submatrix in3 in3) := by
    have := congrArg (fun M : Matrix J K ℂ => (a22 A)⁻¹ * M) F23
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, hp1', Matrix.one_mul, Matrix.mul_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  have T33 : (A.submatrix in3 in3 - A.submatrix in3 in2 * (a22 A)⁻¹ * A.submatrix in2 in3) *
      A⁻¹.submatrix in3 in3 = 1 := by
    rw [hx23] at F33
    simp only [Matrix.mul_neg, ← Matrix.mul_assoc] at F33
    rw [Matrix.sub_mul, ← F33]
    abel
  have T33' := mul_eq_one_comm.mp T33
  have T13 : (A.submatrix in1 in3 - A.submatrix in1 in2 * (a22 A)⁻¹ * A.submatrix in2 in3) *
      A⁻¹.submatrix in3 in3 = 0 := by
    rw [hx23] at F13
    simp only [Matrix.mul_neg, ← Matrix.mul_assoc] at F13
    rw [Matrix.sub_mul, ← F13]
    abel
  have hfirst : A.submatrix in1 in3 = A.submatrix in1 in2 * (a22 A)⁻¹ * A.submatrix in2 in3 := by
    have := congrArg (fun M : Matrix I K ℂ => M * (A.submatrix in3 in3 -
      A.submatrix in3 in2 * (a22 A)⁻¹ * A.submatrix in2 in3)) T13
    simp only [Matrix.mul_assoc _ (A⁻¹.submatrix in3 in3), T33', Matrix.mul_one,
      Matrix.zero_mul] at this
    exact sub_eq_zero.mp this
  refine ⟨hfirst, ?_⟩
  have hx12 : A⁻¹.submatrix in1 in2 =
      -(A⁻¹.submatrix in1 in1 * A.submatrix in1 in2 * (a22 A)⁻¹) := by
    have := congrArg (fun M : Matrix I J ℂ => M * (a22 A)⁻¹) H12
    simp only [Matrix.add_mul, Matrix.mul_assoc, hp2', Matrix.mul_one, Matrix.zero_mul] at this
    rw [← Matrix.mul_assoc] at this
    exact eq_neg_of_add_eq_zero_right this
  have T11 : A⁻¹.submatrix in1 in1 * (A.submatrix in1 in1 -
      A.submatrix in1 in2 * (a22 A)⁻¹ * A.submatrix in2 in1) = 1 := by
    rw [hx12] at H11
    simp only [Matrix.neg_mul, Matrix.mul_assoc] at H11
    rw [Matrix.mul_sub, ← H11]
    simp only [Matrix.mul_assoc]
    abel
  have T11' := mul_eq_one_comm.mp T11
  have W1 : A.submatrix in1 in2 * (a22 A)⁻¹ * G.submatrix Sum.inl Sum.inr = 0 := by
    rw [hx12] at E13
    have h0 : A⁻¹.submatrix in1 in1 * (A.submatrix in1 in2 * (a22 A)⁻¹ *
        G.submatrix Sum.inl Sum.inr) = 0 := by
      simpa only [Matrix.neg_mul, neg_eq_zero, Matrix.mul_assoc] using E13
    have := congrArg (fun M : Matrix I K ℂ => (A.submatrix in1 in1 -
      A.submatrix in1 in2 * (a22 A)⁻¹ * A.submatrix in2 in1) * M) h0
    rw [← Matrix.mul_assoc, T11', Matrix.one_mul, Matrix.mul_zero] at this
    exact this
  have K12 := congrArg (fun M => M.submatrix Sum.inl Sum.inr) hG2
  have K22 := congrArg (fun M => M.submatrix Sum.inr Sum.inr) hG2
  simp only [g75h_blk2] at K12 K22
  have m11 : (1 + marginal23 A).submatrix Sum.inl Sum.inl = 1 + a22 A := by
    ext x y; simp [marginal23, a22, in2, Matrix.one_apply]
  have m12 : (1 + marginal23 A).submatrix Sum.inl Sum.inr = A.submatrix in2 in3 := by
    ext x y; simp [marginal23, in2, in3, Matrix.one_apply]
  have m21 : (1 + marginal23 A).submatrix Sum.inr Sum.inl = A.submatrix in3 in2 := by
    ext x y; simp [marginal23, in2, in3, Matrix.one_apply]
  have m22 : (1 + marginal23 A).submatrix Sum.inr Sum.inr = 1 + A.submatrix in3 in3 := by
    ext x y; simp [marginal23, in3, Matrix.one_apply]
  have p12 : (1 : Mat (J ⊕ K)).submatrix Sum.inl Sum.inr = 0 := by
    ext x y; simp [Matrix.one_apply]
  have p22 : (1 : Mat (J ⊕ K)).submatrix Sum.inr Sum.inr = 1 := by
    ext x y; simp [Matrix.one_apply]
  rw [m11, m12, p12] at K12
  rw [m21, m22, p22] at K22
  have hG23 : G.submatrix Sum.inl Sum.inr =
      -(q * A.submatrix in2 in3 * G.submatrix Sum.inr Sum.inr) := by
    have := congrArg (fun M : Matrix J K ℂ => q * M) K12
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, hq1, Matrix.one_mul, Matrix.mul_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  have T22 : ((1 + A.submatrix in3 in3) - A.submatrix in3 in2 * q * A.submatrix in2 in3) *
      G.submatrix Sum.inr Sum.inr = 1 := by
    rw [hG23] at K22
    simp only [Matrix.mul_neg, ← Matrix.mul_assoc] at K22
    refine Eq.trans ?_ K22
    rw [Matrix.sub_mul]
    abel
  have T22' := mul_eq_one_comm.mp T22
  have W2 : A.submatrix in1 in2 * (a22 A)⁻¹ * q * A.submatrix in2 in3 = 0 := by
    rw [hG23] at W1
    simp only [Matrix.mul_neg, neg_eq_zero, ← Matrix.mul_assoc] at W1
    have := congrArg (fun M : Matrix I K ℂ => M * ((1 + A.submatrix in3 in3) -
      A.submatrix in3 in2 * q * A.submatrix in2 in3)) W1
    rw [Matrix.mul_assoc _ (G.submatrix Sum.inr Sum.inr), T22', Matrix.mul_one,
      Matrix.zero_mul] at this
    exact this
  have hpq : (a22 A)⁻¹ * q = (a22 A)⁻¹ - q := by
    have h1 : (a22 A)⁻¹ = (a22 A)⁻¹ * ((1 + a22 A) * q) := by rw [hq2, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_one, hp1, Matrix.add_mul,
      Matrix.one_mul] at h1
    rw [eq_sub_iff_add_eq, ← h1]
  have hq' : (a22 A + 1)⁻¹ = q := by rw [add_comm]
  rw [hq']
  have hqq : q = (a22 A)⁻¹ - (a22 A)⁻¹ * q := by rw [hpq]; abel
  show A.submatrix in1 in3 = A.submatrix in1 in2 * q * A.submatrix in2 in3
  rw [hqq, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc _ (a22 A)⁻¹ q, W2, sub_zero,
    hfirst]
