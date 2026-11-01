-- Prove2me | solution 1 for RobustOpt2009.SDPApproximation.theorem_9_1_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T06:25:49.894046+00:00
-- url     : https://prove2.me/submissions/9f046bee-3774-4685-b7b6-abccb259a6b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RobustOpt2009_SDPApproximation_theorem_7_1_3
import Theorems.Thm_RobustSDP_FullPert_lemma_3_1

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RLMI912Aux

theorem rk1 {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (hM : M.IsHermitian) (hr : M.rank ≤ 1) :
    M.PosSemidef ∨ (-M).PosSemidef := by
  have hcard : Fintype.card {i // hM.eigenvalues i ≠ 0} ≤ 1 := hM.rank_eq_card_non_zero_eigs ▸ hr
  by_cases hall : ∀ i, 0 ≤ hM.eigenvalues i
  · left; exact hM.posSemidef_iff_eigenvalues_nonneg.mpr (fun i => hall i)
  · right
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    have hle : ∀ j, hM.eigenvalues j ≤ 0 := by
      intro j; by_contra hj; push Not at hj
      have h1 : (⟨i, hi.ne⟩ : {k // hM.eigenvalues k ≠ 0}) = ⟨j, hj.ne'⟩ :=
        Fintype.card_le_one_iff.mp hcard _ _
      have h2 := congrArg Subtype.val h1
      simp only at h2; subst h2; linarith
    have hs := hM.spectral_theorem
    rw [hs, Unitary.conjStarAlgAut_apply]
    have hD : (diagonal (-(RCLike.ofReal ∘ hM.eigenvalues : Fin m → ℝ))).PosSemidef := by
      rw [posSemidef_diagonal_iff]
      intro j; simp [hle j]
    have := hD.mul_mul_conjTranspose_same (hM.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)
    convert this using 1
    rw [show diagonal (-(RCLike.ofReal ∘ hM.eigenvalues) : Fin m → ℝ) =
      -diagonal (RCLike.ofReal ∘ hM.eigenvalues) from (diagonal_neg _).symm, Matrix.mul_neg, Matrix.neg_mul]
    simp [Matrix.star_eq_conjTranspose]

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

theorem fbquad {m p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin m) ℝ)
    (C : Matrix (Fin m) (Fin p) ℝ) (D : Matrix (Fin m) (Fin m) ℝ) (w : Fin p → ℝ) (x : Fin m → ℝ) :
    star (Sum.elim w x) ⬝ᵥ (fromBlocks A B C D *ᵥ Sum.elim w x) =
      w ⬝ᵥ (A *ᵥ w) + w ⬝ᵥ (B *ᵥ x) + (x ⬝ᵥ (C *ᵥ w) + x ⬝ᵥ (D *ᵥ x)) := by
  rw [fromBlocks_mulVec]
  simp [dotProduct_add, star_trivial]

theorem trq {a b : ℕ} (x : Fin a → ℝ) (M : Matrix (Fin b) (Fin a) ℝ) (y : Fin b → ℝ) :
    x ⬝ᵥ (Mᵀ *ᵥ y) = (M *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, vecMul_transpose]

theorem symm_part {m p q : ℕ} (L : Matrix (Fin p) (Fin m) ℝ) (R : Matrix (Fin q) (Fin m) ℝ)
    (Z : Matrix (Fin p) (Fin q) ℝ) : (Lᵀ * Z * R + Rᵀ * Zᵀ * L).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_eq_transpose_of_trivial]
  simp [transpose_add, transpose_mul, Matrix.mul_assoc, add_comm]

theorem blk_imp {m p q : ℕ} (hp : 0 < p) (L : Matrix (Fin p) (Fin m) ℝ)
    (R : Matrix (Fin q) (Fin m) ℝ) (V : Matrix (Fin m) (Fin m) ℝ) (hV : V.IsHermitian) (lam : ℝ)
    (hB : (fromBlocks (lam • (1 : Matrix (Fin p) (Fin p) ℝ)) L Lᵀ (V - lam • (Rᵀ * R))).PosSemidef)
    (Z : Matrix (Fin p) (Fin q) ℝ) (hZ : ‖Z‖ ≤ 1) :
    (V - (Lᵀ * Z * R + Rᵀ * Zᵀ * L)).PosSemidef := by
  have hq := hB.dotProduct_mulVec_nonneg
  have hlam : 0 ≤ lam := by
    have := hq (Sum.elim (Pi.single ⟨0, hp⟩ 1) 0)
    rw [fbquad] at this
    simpa using this
  refine PosSemidef.of_dotProduct_mulVec_nonneg (hV.sub (symm_part L R Z)) fun x => ?_
  have h := hq (Sum.elim (-(Z *ᵥ (R *ᵥ x))) x)
  rw [fbquad] at h
  have hc := opsq Z hZ (R *ᵥ x)
  simp only [star_trivial, sub_mulVec, add_mulVec, dotProduct_sub, dotProduct_add] at h ⊢
  simp only [← mulVec_mulVec, trq, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul,
    neg_dotProduct, dotProduct_neg, mulVec_neg] at h ⊢
  have e1 : (L *ᵥ x) ⬝ᵥ (Z *ᵥ (R *ᵥ x)) = (Z *ᵥ (R *ᵥ x)) ⬝ᵥ (L *ᵥ x) := dotProduct_comm _ _
  have e2 : (R *ᵥ x) ⬝ᵥ (Zᵀ *ᵥ (L *ᵥ x)) = (Z *ᵥ (R *ᵥ x)) ⬝ᵥ (L *ᵥ x) := by
    rw [trq]
  nlinarith [mul_le_mul_of_nonneg_left hc hlam]

theorem zero_of_psd {m q : ℕ} (V : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin q) (Fin m) ℝ)
    (h : (fromBlocks V Rᵀ R (0 : Matrix (Fin q) (Fin q) ℝ)).PosSemidef) : R = 0 := by
  ext k i
  have hq := h.dotProduct_mulVec_nonneg
  set b := R k i
  set a := V i i
  have key : ∀ t : ℝ, 0 ≤ a + 2 * t * b := by
    intro t
    have := hq (Sum.elim (Pi.single i 1) (Pi.single k t))
    rw [fbquad] at this
    simp [mulVec_single, dotProduct_single, single_dotProduct] at this
    linarith
  by_contra hb0
  have hb : b ≠ 0 := hb0
  have := key (-(a + 1) / (2 * b))
  have : 2 * (-(a + 1) / (2 * b)) * b = -(a + 1) := by field_simp
  linarith [key (-(a + 1) / (2 * b))]

theorem V_imp_blk {m p q : ℕ} (hq : 0 < q) (L : Matrix (Fin p) (Fin m) ℝ)
    (R : Matrix (Fin q) (Fin m) ℝ) (hR : R ≠ 0) (V : Matrix (Fin m) (Fin m) ℝ) (hV : V.IsHermitian)
    (h : ∀ Z : Matrix (Fin p) (Fin q) ℝ, ‖Z‖ ≤ 1 → (V - (Lᵀ * Z * R + Rᵀ * Zᵀ * L)).PosSemidef) :
    ∃ lam : ℝ,
      (fromBlocks (lam • (1 : Matrix (Fin p) (Fin p) ℝ)) L Lᵀ (V - lam • (Rᵀ * R))).PosSemidef := by
  by_cases hL : L = 0
  · subst hL
    refine ⟨0, ?_⟩
    have hV0 := h 0 (by simp)
    simp only [zero_smul, sub_zero, transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero] at hV0 ⊢
    refine PosSemidef.of_dotProduct_mulVec_nonneg
      (IsHermitian.fromBlocks (by simp [IsHermitian]) (by simp) hV) fun x => ?_
    rw [← Sum.elim_comp_inl_inr x, fbquad]
    simpa using hV0.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
  · have hLt : Lᵀ ≠ 0 := fun h0 => hL (by simpa using congrArg transpose h0)
    have H := (RobustSDP.FullPert.lemma_3_1 hq V hV Lᵀ R 0 hLt).mp (by
      intro Δ hΔ
      refine ⟨by simp, ?_⟩
      have := h (-Δ) (by rwa [norm_neg])
      simp only [Matrix.zero_mul, sub_zero, inv_one, transpose_one, Matrix.mul_one,
        transpose_transpose] at this ⊢
      convert this using 1
      simp [transpose_neg, Matrix.mul_neg, Matrix.neg_mul, sub_eq_add_neg, add_assoc, add_comm])
    obtain ⟨-, τ, hτ⟩ := H
    simp only [transpose_transpose, transpose_zero, Matrix.mul_zero, smul_zero, sub_zero,
      Matrix.zero_mul, Matrix.mul_zero] at hτ
    have hτq := hτ.dotProduct_mulVec_nonneg
    have hτ0 : 0 ≤ τ := by
      have := hτq (Sum.elim 0 (Pi.single ⟨0, hq⟩ 1))
      rw [fbquad] at this
      simpa using this
    have hτpos : 0 < τ := by
      rcases hτ0.lt_or_eq with h1 | h1
      · exact h1
      · exfalso; apply hR
        subst h1
        apply zero_of_psd (V - (0:ℝ) • (Lᵀ * L))
        simpa using hτ
    refine ⟨τ⁻¹, PosSemidef.of_dotProduct_mulVec_nonneg
      (IsHermitian.fromBlocks (by simp [IsHermitian]) (by simp)
        (hV.sub (by simp [IsHermitian, transpose_mul]))) fun x => ?_⟩
    rw [← Sum.elim_comp_inl_inr x, fbquad]
    set w := x ∘ Sum.inl
    set y := x ∘ Sum.inr
    have hP := hτq (Sum.elim y (-(τ⁻¹ • (R *ᵥ y))))
    rw [fbquad] at hP
    have hsq : 0 ≤ (w + τ • (L *ᵥ y)) ⬝ᵥ (w + τ • (L *ᵥ y)) := by
      simpa using dotProduct_star_self_nonneg (w + τ • (L *ᵥ y))
    simp only [star_trivial, sub_mulVec, add_mulVec, dotProduct_sub, dotProduct_add,
      ← mulVec_mulVec, trq, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul,
      neg_dotProduct, dotProduct_neg, mulVec_neg, smul_dotProduct, add_dotProduct,
      mulVec_smul] at hP hsq ⊢
    have e1 : w ⬝ᵥ (L *ᵥ y) = (L *ᵥ y) ⬝ᵥ w := dotProduct_comm _ _
    have e2 : y ⬝ᵥ (Rᵀ *ᵥ (R *ᵥ y)) = (R *ᵥ y) ⬝ᵥ (R *ᵥ y) := trq _ _ _
    have e3 : (R *ᵥ y) ⬝ᵥ (R *ᵥ y) ≥ 0 := by simpa using dotProduct_star_self_nonneg (R *ᵥ y)
    rw [e1] at hsq ⊢
    generalize w ⬝ᵥ w = W at *
    generalize (L *ᵥ y) ⬝ᵥ w = C at *
    generalize (L *ᵥ y) ⬝ᵥ (L *ᵥ y) = AA at *
    generalize (R *ᵥ y) ⬝ᵥ (R *ᵥ y) = B at *
    generalize y ⬝ᵥ (V *ᵥ y) = VV at *
    have hne : τ ≠ 0 := hτpos.ne'
    have : τ⁻¹ * W + C + (C + (VV - τ⁻¹ * B)) = τ⁻¹ * (W + τ * C + τ * (C + τ * AA)) +
        (VV - τ * AA + -(τ⁻¹ * B) + (-(τ⁻¹ * B) + -(τ⁻¹ * (τ * -(τ⁻¹ * B))))) := by
      field_simp; ring
    rw [this]
    exact add_nonneg (mul_nonneg (inv_nonneg.2 hτ0) hsq) hP

end RLMI912Aux

open RLMI912Aux

theorem solution :
    ∃ θ : ℕ → ℝ, θ 2 = Real.pi / 2 ∧ θ 4 = 2 ∧
      (∀ μ : ℕ, 2 < μ → θ μ ≤ Real.pi * Real.sqrt ((μ : ℝ) / 2)) ∧
      ∀ (n m s f : ℕ), 0 < m → 0 < s + f →
      ∀ (p q : Fin f → ℕ), (∀ j, 0 < p j) → (∀ j, 0 < q j) →
      ∀ (A₀ : (Fin n → ℝ) →ᵃ[ℝ] Matrix (Fin m) (Fin m) ℝ)
        (A : Fin s → ((Fin n → ℝ) →ᵃ[ℝ] Matrix (Fin m) (Fin m) ℝ))
        (L : (j : Fin f) → ((Fin n → ℝ) →ᵃ[ℝ] Matrix (Fin (p j)) (Fin m) ℝ))
        (R : (j : Fin f) → Matrix (Fin (q j)) (Fin m) ℝ),
      (∀ y, (A₀ y).IsHermitian) → (∀ i y, (A i y).IsHermitian) →
      (∀ j, R j ≠ 0) → ∀ (ρ : ℝ), 0 < ρ → ∀ y : Fin n → ℝ,
      let RC : ℝ → Prop := fun r =>
        ∀ (z : Fin s → ℝ) (Z : (j : Fin f) → Matrix (Fin (p j)) (Fin (q j)) ℝ),
          (∀ i, |z i| ≤ r) → (∀ j, ‖Z j‖ ≤ r) →
          (A₀ y + (∑ i, z i • A i y) +
            ∑ j, ((L j y)ᵀ * Z j * R j + (R j)ᵀ * (Z j)ᵀ * L j y)).PosSemidef
      let SDP : Prop :=
        ∃ (U : Fin s → Matrix (Fin m) (Fin m) ℝ)
          (V : Fin f → Matrix (Fin m) (Fin m) ℝ) (lam : Fin f → ℝ),
          (∀ i, (U i).IsHermitian) ∧ (∀ j, (V j).IsHermitian) ∧
          (∀ i, (U i - A i y).PosSemidef ∧ (U i + A i y).PosSemidef) ∧
          (∀ j, (fromBlocks (lam j • (1 : Matrix (Fin (p j)) (Fin (p j)) ℝ))
            (L j y) (L j y)ᵀ (V j - lam j • ((R j)ᵀ * R j))).PosSemidef) ∧
          (A₀ y - ρ • ((∑ i, U i) + ∑ j, V j)).PosSemidef
      (SDP → RC ρ) ∧
      (∀ μ : ℕ, IsLeast {k : ℕ | 2 ≤ k ∧ ∀ i y', (A i y').rank ≤ k} μ →
        ¬ SDP → ¬ RC (θ μ * ρ)) ∧
      ((s + f = 1 ∨ (f = 0 ∧ ∀ i y', (A i y').rank ≤ 1)) → (SDP ↔ RC ρ)) := by
  obtain ⟨θ, -, h2, h4, hle, H⟩ := RobustOpt2009.SDPApproximation.theorem_7_1_3
  refine ⟨θ, h2, h4, fun μ hμ => hle μ hμ.le, ?_⟩
  intro n m s f hm hsf p q hp hq A₀ A L R hA₀ hA hR ρ hρ y RC SDP
  have H' := H m s f hm p q hp hq (A₀ y) (fun i => A i y) (fun j => L j y) R (hA₀ y)
    (fun i => hA i y) ρ hρ.le
  simp only at H'
  -- the certificate systems coincide
  have hSb : SDP ↔ ∃ (U : Fin s → Matrix (Fin m) (Fin m) ℝ)
          (V : Fin f → Matrix (Fin m) (Fin m) ℝ),
          (∀ i, (U i).IsHermitian) ∧ (∀ j, (V j).IsHermitian) ∧
          (∀ i, (U i - A i y).PosSemidef ∧ (U i + A i y).PosSemidef) ∧
          (∀ j, ∀ Z : Matrix (Fin (p j)) (Fin (q j)) ℝ, ‖Z‖ ≤ 1 →
            (V j - ((L j y)ᵀ * Z * R j + (R j)ᵀ * Zᵀ * L j y)).PosSemidef) ∧
          (A₀ y - ρ • (∑ i, U i) - ρ • (∑ j, V j)).PosSemidef := by
    constructor
    · rintro ⟨U, V, lam, hU, hV, hUA, hblk, hfin⟩
      refine ⟨U, V, hU, hV, hUA, fun j Z hZ => blk_imp (hp j) _ _ _ (hV j) (lam j) (hblk j) Z hZ, ?_⟩
      rwa [sub_sub, ← smul_add]
    · rintro ⟨U, V, hU, hV, hUA, hVc, hfin⟩
      have hl : ∀ j, ∃ l : ℝ, (fromBlocks (l • (1 : Matrix (Fin (p j)) (Fin (p j)) ℝ))
            (L j y) (L j y)ᵀ (V j - l • ((R j)ᵀ * R j))).PosSemidef :=
        fun j => V_imp_blk (hq j) _ _ (hR j) _ (hV j) (hVc j)
      choose lam hlam using hl
      refine ⟨U, V, lam, hU, hV, hUA, hlam, ?_⟩
      rwa [smul_add, ← sub_sub]
  refine ⟨fun h => H'.1 (hSb.mp h), fun μ hμ hS => H'.2.2 μ hμ.1.1 (fun i => hμ.1.2 i y)
    (fun hb => hS (hSb.mpr hb)), ?_⟩
  rintro (h1 | ⟨hf, hrk⟩)
  · exact hSb.trans (H'.2.1 h1)
  · refine ⟨fun h => H'.1 (hSb.mp h), fun hRC => ?_⟩
    subst hf
    classical
    have hpsd : ∀ i, (A i y).PosSemidef ∨ (-(A i y)).PosSemidef :=
      fun i => rk1 _ (hA i y) (hrk i y)
    let U : Fin s → Matrix (Fin m) (Fin m) ℝ := fun i =>
      if (A i y).PosSemidef then A i y else -(A i y)
    let z : Fin s → ℝ := fun i => if (A i y).PosSemidef then -ρ else ρ
    have hzU : ∀ i, z i • A i y = -(ρ • U i) := by
      intro i; simp only [z, U]; split_ifs <;> simp [neg_smul, smul_neg]
    have hRC' := hRC z (fun j => j.elim0) (fun i => by simp only [z]; split_ifs <;> simp [abs_of_pos hρ])
      (fun j => j.elim0)
    apply hSb.mpr
    refine ⟨U, fun j => j.elim0, fun i => ?_, fun j => j.elim0, fun i => ?_,
      fun j => j.elim0, ?_⟩
    · simp only [U]; split_ifs
      · exact hA i y
      · exact (hA i y).neg
    · simp only [U]; split_ifs with hi
      · refine ⟨by simpa using PosSemidef.zero, ?_⟩
        exact hi.add hi
      · rcases hpsd i with h | h
        · exact absurd h hi
        · refine ⟨by simpa [sub_eq_add_neg] using h.add h, by simpa using PosSemidef.zero⟩
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, smul_zero, sub_zero] at hRC' ⊢
      simp only [hzU, Finset.sum_neg_distrib, ← Finset.smul_sum] at hRC'
      simpa [sub_eq_add_neg] using hRC'
