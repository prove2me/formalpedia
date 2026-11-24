-- Prove2me | solution 1 for QuadMatIneq.Basic.theorem_3_2_b
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T01:50:20.261426+00:00
-- url     : https://prove2.me/submissions/6367b882-693e-48b0-af16-fef714fe1043

import Mathlib
import Definitions.Def_QuadMatIneq_Basic_QMI

open Matrix QuadMatIneq.Basic

namespace QMI32bAux

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma mp_of_diag (U : Matrix κ κ ℝ) (d : κ → ℝ) (h1 : Uᵀ * U = 1) :
    IsMoorePenrose (U * diagonal d * Uᵀ) (U * diagonal d⁻¹ * Uᵀ) := by
  have c : ∀ M : Matrix κ κ ℝ, M * Uᵀ * U = M := fun M => by
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have dd : ∀ (M : Matrix κ κ ℝ) (a b : κ → ℝ),
      M * diagonal a * diagonal b = M * diagonal (a * b) := fun M a b => by
    rw [Matrix.mul_assoc, diagonal_mul_diagonal']
    rfl
  have e1 : d * d⁻¹ * d = d := by
    ext i
    simp only [Pi.mul_apply, Pi.inv_apply]
    by_cases h : d i = 0
    · simp [h]
    · rw [mul_inv_cancel₀ h, one_mul]
  have e2 : d * d⁻¹ * d⁻¹ = d⁻¹ := by
    ext i
    simp only [Pi.mul_apply, Pi.inv_apply]
    by_cases h : d i = 0
    · simp [h]
    · rw [mul_inv_cancel₀ h, one_mul]
  have e3 : d⁻¹ * d = d * d⁻¹ := mul_comm _ _
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [← Matrix.mul_assoc, c, dd, transpose_mul, transpose_transpose, diagonal_transpose,
      e3, e1, e2]

lemma mp_exists (A : Matrix κ κ ℝ) (hA : A.IsHermitian) : ∃ X, IsMoorePenrose A X := by
  have hspec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  set U : Matrix κ κ ℝ := (hA.eigenvectorUnitary : Matrix κ κ ℝ) with hU
  have hs : star U = Uᵀ := by rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have h1 : Uᵀ * U = 1 := by rw [← hs]; exact Unitary.coe_star_mul_self _
  rw [hs] at hspec
  rw [hspec]
  exact ⟨_, mp_of_diag U _ h1⟩

lemma qform (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (Z : Matrix κ ι ℝ) :
    qmiForm P Z = P.toBlocks₁₁ + P.toBlocks₁₂ * Z + Zᵀ * P.toBlocks₂₁ +
      Zᵀ * P.toBlocks₂₂ * Z := by
  unfold qmiForm
  conv_lhs => rw [← fromBlocks_toBlocks P]
  rw [transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp only [transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.add_mul, Matrix.mul_assoc]
  abel

lemma quad_expand (P11 : Matrix ι ι ℝ) (B : Matrix κ ι ℝ) (A : Matrix κ κ ℝ)
    (Z : Matrix κ ι ℝ) (x : ι → ℝ) :
    star x ⬝ᵥ ((P11 + Bᵀ * Z + Zᵀ * B + Zᵀ * A * Z) *ᵥ x) =
      x ⬝ᵥ (P11 *ᵥ x) + 2 * ((B *ᵥ x) ⬝ᵥ (Z *ᵥ x)) - (Z *ᵥ x) ⬝ᵥ ((-A) *ᵥ (Z *ᵥ x)) := by
  simp only [star_trivial, add_mulVec, dotProduct_add, ← mulVec_mulVec]
  rw [dotProduct_mulVec x Bᵀ, vecMul_transpose, dotProduct_mulVec x Zᵀ, vecMul_transpose,
    dotProduct_mulVec x Zᵀ, vecMul_transpose, neg_mulVec, dotProduct_neg,
    dotProduct_comm (Z *ᵥ x) (B *ᵥ x)]
  ring

lemma real_bound {c α β t a d q : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h1 : c * t ^ 2 ≤ q) (h0 : 0 ≤ a + 2 * d - q) (ha : |a| ≤ α) (hd : |d| ≤ β * t) :
    t ≤ 1 + (α + 2 * β) / c := by
  have ha' : a ≤ α := (le_abs_self a).trans ha
  have hd' : d ≤ β * t := (le_abs_self d).trans hd
  have key : c * t ^ 2 ≤ α + 2 * β * t := by nlinarith
  by_contra h
  push_neg at h
  have hpos : 0 ≤ (α + 2 * β) / c := by positivity
  have h2 : α + 2 * β < (t - 1) * c := (div_lt_iff₀ hc).1 (by linarith)
  have ht1 : 1 < t := by linarith
  nlinarith [mul_lt_mul_of_pos_left h2 (by linarith : (0 : ℝ) < t),
    mul_nonneg hα (by linarith : (0 : ℝ) ≤ t - 1), mul_pos hc (by linarith : (0 : ℝ) < t)]

lemma abs_dot_le (b y : κ → ℝ) : |b ⬝ᵥ y| ≤ (∑ k, |b k|) * ‖y‖ := by
  unfold dotProduct
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have := norm_le_pi_norm y k
  rwa [Real.norm_eq_abs] at this

end QMI32bAux

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Nonempty ι]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) :
    (∃ C : ℝ, ∀ Z ∈ ZSet P, ∀ i j, |Z i j| ≤ C) ↔ (-P.toBlocks₂₂).PosDef := by
  obtain ⟨hH, hA, hS, hker⟩ := hP
  have hq : ∀ Z, qmiForm P Z = P.toBlocks₁₁ + P.toBlocks₁₂ * Z + Zᵀ * P.toBlocks₂₁ +
      Zᵀ * P.toBlocks₂₂ * Z := fun Z => QMI32bAux.qform P Z
  set A := P.toBlocks₂₂ with hAdef
  set B := P.toBlocks₂₁ with hBdef
  have hBt : P.toBlocks₁₂ = Bᵀ := by
    ext i k
    have := hH.apply (Sum.inl i) (Sum.inr k)
    simp only [star_trivial] at this
    simp only [hBdef, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, transpose_apply, of_apply]
    first | exact this | exact this.symm
  have hAs : Aᵀ = A := by
    ext k l
    have := hH.apply (Sum.inr l) (Sum.inr k)
    simp only [star_trivial] at this
    simp only [hAdef, Matrix.toBlocks₂₂, transpose_apply, of_apply]
    first | exact this | exact this.symm
  simp only [hBt] at hq hker
  constructor
  · rintro ⟨C, hC⟩
    by_contra hnpd
    have hdet : (-A).det = 0 := by
      by_contra hd
      exact hnpd ((hA.posDef_iff_det_ne_zero).2 hd)
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hAv : A *ᵥ v = 0 := by rw [neg_mulVec, neg_eq_zero] at hv; exact hv
    have hBv : Bᵀ *ᵥ v = 0 := hker v hAv
    have hAherm : A.IsHermitian := by simpa using hA.isHermitian.neg
    have hX : IsMoorePenrose A (pinv A) := Classical.epsilon_spec (QMI32bAux.mp_exists A hAherm)
    set X := pinv A with hXdef
    obtain ⟨h1, h2, h3, h4⟩ := hX
    have e1 : Bᵀ * X * A = Bᵀ := by
      have hz : Bᵀ * (1 - X * A) = 0 := by
        ext k j
        have hw : A *ᵥ ((1 - X * A) *ᵥ Pi.single j 1) = 0 := by
          rw [mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h1, sub_self,
            zero_mulVec]
        have := congrFun (hker _ hw) k
        rw [mulVec_mulVec] at this
        simpa [mulVec_single_one] using this
      rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hz
      rw [Matrix.mul_assoc]
      exact hz.symm
    have e2 : X * A * B = B := by
      calc X * A * B = (X * A)ᵀ * B := by rw [h4]
        _ = (Bᵀ * (X * A))ᵀ := by rw [transpose_mul Bᵀ (X * A), transpose_transpose]
        _ = B := by rw [← Matrix.mul_assoc, e1, transpose_transpose]
    have hAXt : A * Xᵀ = X * A := by rw [← h4, transpose_mul, hAs]
    have hAXtA : A * Xᵀ * A = A := by
      have := congrArg transpose h1
      rw [transpose_mul, transpose_mul, hAs] at this
      rw [Matrix.mul_assoc]
      exact this
    have e3 : Bᵀ * Xᵀ * B = Bᵀ * X * B := by
      calc Bᵀ * Xᵀ * B = Bᵀ * X * A * Xᵀ * B := by rw [e1]
        _ = Bᵀ * X * (X * A * B) := by
          rw [Matrix.mul_assoc (Bᵀ * X) A Xᵀ, hAXt]
          simp only [Matrix.mul_assoc]
        _ = Bᵀ * X * B := by rw [e2]
    have e4 : Bᵀ * Xᵀ * A * X * B = Bᵀ * X * B := by
      calc Bᵀ * Xᵀ * A * X * B = Bᵀ * X * A * Xᵀ * A * X * B := by rw [e1]
        _ = Bᵀ * X * (A * Xᵀ * A) * X * B := by simp only [Matrix.mul_assoc]
        _ = Bᵀ * (X * A * X) * B := by rw [hAXtA]; simp only [Matrix.mul_assoc]
        _ = Bᵀ * X * B := by rw [h2]
    have hZ0 : qmiForm P (-(X * B)) = schur P := by
      rw [hq]
      simp only [schur, ← hAdef, ← hBdef, ← hXdef, hBt]
      simp only [transpose_neg, transpose_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
      simp only [← Matrix.mul_assoc, e3, e4]
      abel
    -- a direction along which the solution set is unbounded
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hv0
    simp only [Pi.zero_apply] at hk
    obtain ⟨i0⟩ := ‹Nonempty ι›
    set W : Matrix κ ι ℝ := vecMulVec v (Pi.single i0 (1 : ℝ)) with hWdef
    have hAW : A * W = 0 := by rw [hWdef, mul_vecMulVec, hAv, zero_vecMulVec]
    have hBW : Bᵀ * W = 0 := by rw [hWdef, mul_vecMulVec, hBv, zero_vecMulVec]
    have hWB : Wᵀ * B = 0 := by
      have := congrArg transpose hBW
      rwa [transpose_mul, transpose_transpose, transpose_zero] at this
    have hWA : Wᵀ * A = 0 := by
      have := congrArg transpose hAW
      rwa [transpose_mul, hAs, transpose_zero] at this
    have hAW' : ∀ M : Matrix ι κ ℝ, M * A * W = 0 := fun M => by
      rw [Matrix.mul_assoc, hAW, Matrix.mul_zero]
    have hW : ∀ t : ℝ, qmiForm P (-(X * B) + t • W) = qmiForm P (-(X * B)) := by
      intro t
      rw [hq, hq]
      simp only [transpose_add, transpose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
        Matrix.smul_mul, hBW, hWB, hWA, hAW', smul_zero, add_zero, Matrix.zero_mul]
    have hmem : ∀ t : ℝ, -(X * B) + t • W ∈ ZSet P := by
      intro t
      show (qmiForm P (-(X * B) + t • W)).PosSemidef
      rw [hW, hZ0]
      exact hS
    set z := (-(X * B)) k i0 with hz
    have hent : ∀ t : ℝ, (-(X * B) + t • W) k i0 = z + t * v k := by
      intro t
      simp [hWdef, vecMulVec_apply, hz]
    have := hC _ (hmem ((C + |z| + 1 - z) / v k)) k i0
    rw [hent, div_mul_cancel₀ _ hk] at this
    have hzabs := abs_nonneg z
    have := le_abs_self (z + (C + |z| + 1 - z))
    linarith
  · intro hpd
    obtain ⟨c, hc, hcoer⟩ : ∃ c > 0, ∀ y : κ → ℝ, c * ‖y‖ ^ 2 ≤ y ⬝ᵥ ((-A) *ᵥ y) := by
      by_cases hne : ∃ y : κ → ℝ, y ≠ 0
      · obtain ⟨y0, hy0⟩ := hne
        have hS1 : (Metric.sphere (0 : κ → ℝ) 1).Nonempty := ⟨‖y0‖⁻¹ • y0, by
          rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
            inv_mul_cancel₀ (norm_ne_zero_iff.2 hy0)]⟩
        have hcont : Continuous fun y : κ → ℝ => y ⬝ᵥ ((-A) *ᵥ y) := by
          first
            | fun_prop
            | exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
        obtain ⟨u0, hu0, hmin⟩ :=
          (isCompact_sphere (0 : κ → ℝ) 1).exists_isMinOn hS1 hcont.continuousOn
        have hu0ne : u0 ≠ 0 := by
          intro h
          rw [h, mem_sphere_zero_iff_norm, norm_zero] at hu0
          norm_num at hu0
        refine ⟨u0 ⬝ᵥ ((-A) *ᵥ u0), ?_, ?_⟩
        · have := hpd.dotProduct_mulVec_pos hu0ne
          simpa [star_trivial] using this
        · intro y
          by_cases hy : y = 0
          · simp [hy]
          · have hny : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
            have huS : ‖y‖⁻¹ • y ∈ Metric.sphere (0 : κ → ℝ) 1 := by
              rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hny]
            have hm : u0 ⬝ᵥ ((-A) *ᵥ u0) ≤ (‖y‖⁻¹ • y) ⬝ᵥ ((-A) *ᵥ (‖y‖⁻¹ • y)) :=
              isMinOn_iff.mp hmin _ huS
            have hsc : y ⬝ᵥ ((-A) *ᵥ y) =
                ‖y‖ ^ 2 * ((‖y‖⁻¹ • y) ⬝ᵥ ((-A) *ᵥ (‖y‖⁻¹ • y))) := by
              rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
              field_simp
            rw [hsc, mul_comm]
            exact mul_le_mul_of_nonneg_left hm (sq_nonneg _)
      · push_neg at hne
        refine ⟨1, one_pos, fun y => ?_⟩
        simp [hne y]
    set α : ℝ := ∑ j, |Pi.single j (1 : ℝ) ⬝ᵥ (P.toBlocks₁₁ *ᵥ Pi.single j 1)| with hαdef
    set β : ℝ := ∑ j, ∑ k, |(B *ᵥ Pi.single j (1 : ℝ)) k| with hβdef
    have hα : 0 ≤ α := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hβ : 0 ≤ β := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨1 + (α + 2 * β) / c, fun Z hZ i j => ?_⟩
    have hpsd : (qmiForm P Z).PosSemidef := hZ
    have h0 := hpsd.dotProduct_mulVec_nonneg (Pi.single j (1 : ℝ))
    rw [hq Z, QMI32bAux.quad_expand] at h0
    have ha : |Pi.single j (1 : ℝ) ⬝ᵥ (P.toBlocks₁₁ *ᵥ Pi.single j 1)| ≤ α :=
      Finset.single_le_sum (f := fun j => |Pi.single j (1 : ℝ) ⬝ᵥ (P.toBlocks₁₁ *ᵥ Pi.single j 1)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have hbj : (∑ k, |(B *ᵥ Pi.single j (1 : ℝ)) k|) ≤ β :=
      Finset.single_le_sum (f := fun j => ∑ k, |(B *ᵥ Pi.single j (1 : ℝ)) k|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have hd : |(B *ᵥ Pi.single j (1 : ℝ)) ⬝ᵥ (Z *ᵥ Pi.single j 1)| ≤
        β * ‖Z *ᵥ Pi.single j (1 : ℝ)‖ :=
      (QMI32bAux.abs_dot_le _ _).trans (mul_le_mul_of_nonneg_right hbj (norm_nonneg _))
    have hbound := QMI32bAux.real_bound hc (norm_nonneg _) hα hβ (hcoer _) h0 ha hd
    have hentry : |Z i j| ≤ ‖Z *ᵥ Pi.single j (1 : ℝ)‖ := by
      have := norm_le_pi_norm (Z *ᵥ Pi.single j (1 : ℝ)) i
      rw [mulVec_single_one] at this
      simpa [Real.norm_eq_abs] using this
    linarith
