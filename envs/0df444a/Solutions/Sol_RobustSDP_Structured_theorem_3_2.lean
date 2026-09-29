-- Prove2me | solution 1 for RobustSDP.Structured.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:17:13.484831+00:00
-- url     : https://prove2.me/submissions/6e9a0f9e-a04d-40dc-b279-cd5eab1555a9

import Mathlib
import Definitions.Def_RobustSDP_Structured_Model

open Matrix
open scoped Matrix.Norms.L2Operator


namespace RobustSDP.Structured

lemma psd_mul_comm {ι : Type*} [Fintype ι] [DecidableEq ι] (S Q : Matrix ι ι ℝ)
    (hS : S.PosSemidef) (hQ : Q.PosSemidef) (h : S * Q = Q * S) : (S * Q).PosSemidef := by
  open scoped MatrixOrder in
  have := Commute.mul_nonneg (a := S) (b := Q) hS.nonneg hQ.nonneg h
  exact Matrix.nonneg_iff_posSemidef.mp this

def qfm {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (z : ι → ℝ) : ℝ := z ⬝ᵥ (A *ᵥ z)

lemma dm {a b : Type*} [Fintype a] [Fintype b] (M : Matrix a b ℝ) (x : a → ℝ) (y : b → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = (Mᵀ *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, mulVec_transpose]

lemma elim_dot {a b : Type*} [Fintype a] [Fintype b] (x z : a → ℝ) (y w : b → ℝ) :
    (Sum.elim x y : a ⊕ b → ℝ) ⬝ᵥ Sum.elim z w = x ⬝ᵥ z + y ⬝ᵥ w := by
  simp [dotProduct, Fintype.sum_sum_type]

lemma key_q {n p q : ℕ} (F : Matrix (Fin n) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin p) ℝ) (R : Matrix (Fin q) (Fin n) ℝ) (D : Matrix (Fin q) (Fin p) ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (T : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin p) (Fin q) ℝ)
    (hSs : Sᵀ = S) (ξ : Fin n → ℝ) (η : Fin q → ℝ) :
    qfm (fromBlocks (F - L * S * Lᵀ) (Rᵀ - L * S * Dᵀ + L * G) (R - D * S * Lᵀ + Gᵀ * Lᵀ)
      (T - D * S * Dᵀ + D * G + Gᵀ * Dᵀ)) (Sum.elim ξ η) =
      ξ ⬝ᵥ (F *ᵥ ξ) + 2 * (η ⬝ᵥ (R *ᵥ ξ)) + η ⬝ᵥ (T *ᵥ η)
        - (Lᵀ *ᵥ ξ + Dᵀ *ᵥ η) ⬝ᵥ (S *ᵥ (Lᵀ *ᵥ ξ + Dᵀ *ᵥ η))
        + 2 * ((G *ᵥ η) ⬝ᵥ (Lᵀ *ᵥ ξ + Dᵀ *ᵥ η)) := by
  have hsym : ∀ x y : Fin p → ℝ, x ⬝ᵥ (S *ᵥ y) = y ⬝ᵥ (S *ᵥ x) := by
    intro x y; rw [dm, hSs, dotProduct_comm]
  unfold qfm
  rw [fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, elim_dot, add_mulVec, sub_mulVec,
    ← mulVec_mulVec, dotProduct_add, dotProduct_sub, add_dotProduct, mulVec_add]
  simp only [dm L ξ, dm D η, dm Rᵀ ξ, dm Gᵀ η, transpose_transpose]
  rw [hsym (Dᵀ *ᵥ η) (Lᵀ *ᵥ ξ), dotProduct_comm (R *ᵥ ξ) η,
    dotProduct_comm (Lᵀ *ᵥ ξ) (G *ᵥ η), dotProduct_comm (Dᵀ *ᵥ η) (G *ᵥ η)]
  ring


lemma nsq {a : ℕ} (v : Fin a → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin a))‖ ^ 2 = v ⬝ᵥ v := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]; simp

lemma nmulVec {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) (v : Fin b → ℝ) :
    ‖(WithLp.toLp 2 (M *ᵥ v) : EuclideanSpace ℝ (Fin a))‖ ≤
      ‖M‖ * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin b))‖ :=
  l2_opNorm_mulVec M (WithLp.toLp 2 v)

lemma ntrans {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) : ‖Mᵀ‖ = ‖M‖ := by
  simpa using l2_opNorm_conjTranspose M

lemma one_sub_psd {p q : ℕ} (Δ : Matrix (Fin p) (Fin q) ℝ) (hΔ : ‖Δ‖ ≤ 1) :
    (1 - Δ * Δᵀ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · simp [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_mul]
  · rw [star_trivial, sub_mulVec, one_mulVec, dotProduct_sub, ← mulVec_mulVec, dm Δ x]
    have hn := nmulVec Δᵀ x
    rw [ntrans] at hn
    have h1 := nsq x
    have h2 := nsq (Δᵀ *ᵥ x)
    have h0 := norm_nonneg (WithLp.toLp 2 (Δᵀ *ᵥ x) : EuclideanSpace ℝ (Fin q))
    have h0' := norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin p))
    have : ‖(WithLp.toLp 2 (Δᵀ *ᵥ x) : EuclideanSpace ℝ (Fin q))‖ ≤
        ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin p))‖ := by nlinarith
    nlinarith

lemma bound_q {n p q : ℕ} (F : Matrix (Fin n) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin p) ℝ) (R : Matrix (Fin q) (Fin n) ℝ) (D : Matrix (Fin q) (Fin p) ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (T : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin p) (Fin q) ℝ)
    (hS : S.PosDef) (hT : T.PosDef) (Δ : Matrix (Fin p) (Fin q) ℝ) (hΔ : ‖Δ‖ ≤ 1)
    (h1 : S * Δ = Δ * T) (h2 : G * Δᵀ = -(Δ * Gᵀ))
    (ξ : Fin n → ℝ) (η : Fin q → ℝ) (hη : η = Δᵀ *ᵥ (Lᵀ *ᵥ ξ + Dᵀ *ᵥ η)) :
    qfm (fromBlocks (F - L * S * Lᵀ) (Rᵀ - L * S * Dᵀ + L * G) (R - D * S * Lᵀ + Gᵀ * Lᵀ)
      (T - D * S * Dᵀ + D * G + Gᵀ * Dᵀ)) (Sum.elim ξ η) ≤
      ξ ⬝ᵥ (F *ᵥ ξ) + 2 * (η ⬝ᵥ (R *ᵥ ξ)) := by
  have hSs : Sᵀ = S := hS.1
  have hTs : Tᵀ = T := hT.1
  rw [key_q F L R D S T G hSs ξ η]
  set b := Lᵀ *ᵥ ξ + Dᵀ *ᵥ η with hb
  clear_value b
  subst hη
  -- (a)
  have hP : Δ * T * Δᵀ = S * (Δ * Δᵀ) := by rw [← h1, Matrix.mul_assoc]
  have hcomm : S * (1 - Δ * Δᵀ) = (1 - Δ * Δᵀ) * S := by
    have : Δᵀ * S = T * Δᵀ := by
      rw [← hSs, ← transpose_mul, h1, transpose_mul, hTs]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc Δ,
      this, ← Matrix.mul_assoc Δ T, ← h1, Matrix.mul_assoc]
  have hpsd := psd_mul_comm S _ hS.posSemidef (one_sub_psd Δ hΔ) hcomm
  have ha := hpsd.dotProduct_mulVec_nonneg b
  rw [star_trivial, Matrix.mul_sub, Matrix.mul_one, sub_mulVec, dotProduct_sub, ← hP] at ha
  have hTT : (Δᵀ *ᵥ b) ⬝ᵥ (T *ᵥ (Δᵀ *ᵥ b)) = b ⬝ᵥ ((Δ * T * Δᵀ) *ᵥ b) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dm Δ b]
  -- (b)
  have hG : (G *ᵥ (Δᵀ *ᵥ b)) ⬝ᵥ b = 0 := by
    have e1 : (G *ᵥ (Δᵀ *ᵥ b)) ⬝ᵥ b = b ⬝ᵥ ((G * Δᵀ) *ᵥ b) := by
      rw [dotProduct_comm, mulVec_mulVec]
    have e2 : b ⬝ᵥ ((Δ * Gᵀ) *ᵥ b) = (G *ᵥ (Δᵀ *ᵥ b)) ⬝ᵥ b := by
      rw [← mulVec_mulVec, dm Δ b, dm Gᵀ, transpose_transpose]
    rw [h2, neg_mulVec, dotProduct_neg, e2] at e1
    linarith
  rw [hG]
  linarith


lemma gexp {n p q : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin q) (Fin n) ℝ) (Δ : Matrix (Fin p) (Fin q) ℝ) (K : Matrix (Fin q) (Fin q) ℝ)
    (ξ : Fin n → ℝ) :
    ξ ⬝ᵥ ((F + L * Δ * K * R + Rᵀ * Kᵀ * Δᵀ * Lᵀ) *ᵥ ξ) =
      ξ ⬝ᵥ (F *ᵥ ξ) + 2 * ((Kᵀ *ᵥ (Δᵀ *ᵥ (Lᵀ *ᵥ ξ))) ⬝ᵥ (R *ᵥ ξ)) := by
  simp only [add_mulVec, dotProduct_add, ← mulVec_mulVec]
  rw [dm L ξ, dm Δ, dm K, dm Rᵀ ξ, transpose_transpose,
    dotProduct_comm (R *ᵥ ξ)]
  ring

theorem lemma_3_2_core {n p q : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (L : Matrix (Fin n) (Fin p) ℝ) (R : Matrix (Fin q) (Fin n) ℝ) (D : Matrix (Fin q) (Fin p) ℝ)
    (𝒟 : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ))
    (S : Matrix (Fin p) (Fin p) ℝ) (T : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin p) (Fin q) ℝ)
    (hB : (S, T, G) ∈ scalingSet 𝒟) (hS : S.PosDef) (hT : T.PosDef)
    (hLMI : (fromBlocks (F - L * S * Lᵀ) (Rᵀ - L * S * Dᵀ + L * G) (R - D * S * Lᵀ + Gᵀ * Lᵀ)
      (T - D * S * Dᵀ + D * G + Gᵀ * Dᵀ)).PosDef) :
    ∀ Δ ∈ 𝒟, ‖Δ‖ ≤ 1 →
      (1 - D * Δ).det ≠ 0 ∧
        (F + L * Δ * (1 - D * Δ)⁻¹ * R + Rᵀ * ((1 - D * Δ)⁻¹)ᵀ * Δᵀ * Lᵀ).PosDef := by
  intro Δ hΔD hΔ
  obtain ⟨h1, h2⟩ := hB Δ hΔD
  simp only at h1 h2
  have hpos : ∀ v : Fin n ⊕ Fin q → ℝ, v ≠ 0 →
      0 < qfm (fromBlocks (F - L * S * Lᵀ) (Rᵀ - L * S * Dᵀ + L * G) (R - D * S * Lᵀ + Gᵀ * Lᵀ)
        (T - D * S * Dᵀ + D * G + Gᵀ * Dᵀ)) v := by
    intro v hv
    have := hLMI.dotProduct_mulVec_pos hv
    rwa [star_trivial] at this
  have hbd := bound_q F L R D S T G hS hT Δ hΔ h1 h2
  have h3 : ∀ y, (1 - D * Δ)ᵀ *ᵥ y = y - Δᵀ *ᵥ (Dᵀ *ᵥ y) := by
    intro y
    rw [transpose_sub, transpose_one, transpose_mul, sub_mulVec, one_mulVec, mulVec_mulVec]
  have hdet : (1 - D * Δ).det ≠ 0 := by
    intro h0
    rw [← det_transpose, ← Matrix.exists_mulVec_eq_zero_iff] at h0
    obtain ⟨η, hη0, hη⟩ := h0
    rw [h3, sub_eq_zero] at hη
    have hη' : η = Δᵀ *ᵥ (Lᵀ *ᵥ (0 : Fin n → ℝ) + Dᵀ *ᵥ η) := by
      rw [mulVec_zero, zero_add]; exact hη
    have hle := hbd 0 η hη'
    have hne : (Sum.elim (0 : Fin n → ℝ) η) ≠ 0 := by
      intro he; apply hη0
      have := congrArg (fun v => v ∘ Sum.inr) he
      simpa using this
    have hgt := hpos _ hne
    simp at hle
    linarith
  refine ⟨hdet, ?_⟩
  have hu : IsUnit (1 - D * Δ).det := isUnit_iff_ne_zero.mpr hdet
  have hFt : Fᵀ = F := hF
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun ξ hξ => ?_
  · simp [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_add, transpose_mul, hFt,
      Matrix.mul_assoc]
    abel
  · rw [star_trivial, gexp]
    set η := ((1 - D * Δ)⁻¹)ᵀ *ᵥ (Δᵀ *ᵥ (Lᵀ *ᵥ ξ)) with hηdef
    have h1' : ((1 - D * Δ)⁻¹)ᵀ * (1 - D * Δ)ᵀ = 1 := by
      rw [← transpose_mul, mul_nonsing_inv _ hu, transpose_one]
    have h2' : (1 - D * Δ)ᵀ * ((1 - D * Δ)⁻¹)ᵀ = 1 := by
      rw [← transpose_mul, nonsing_inv_mul _ hu, transpose_one]
    have hη : η = Δᵀ *ᵥ (Lᵀ *ᵥ ξ + Dᵀ *ᵥ η) := by
      have : (1 - D * Δ)ᵀ *ᵥ η = Δᵀ *ᵥ (Lᵀ *ᵥ ξ) := by
        rw [hηdef, mulVec_mulVec, h2', one_mulVec]
      rw [h3] at this
      rw [mulVec_add, ← this]; abel
    have hle := hbd ξ η hη
    have hne : (Sum.elim ξ η) ≠ 0 := by
      intro he; apply hξ
      have := congrArg (fun v => v ∘ Sum.inl) he
      simpa using this
    have hgt := hpos _ hne
    linarith


theorem theorem_3_2_core {m n p q : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (Rs : Fin (m + 1) → Matrix (Fin q) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin p) ℝ) (D : Matrix (Fin q) (Fin p) ℝ)
    (𝒟 : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ)) (ρ : ℝ) (hρ : 0 < ρ) (x : Fin m → ℝ)
    (hx : ∃ (S : Matrix (Fin p) (Fin p) ℝ) (T : Matrix (Fin q) (Fin q) ℝ)
        (G : Matrix (Fin p) (Fin q) ℝ), (S, T, G) ∈ scalingSet 𝒟 ∧ S.PosDef ∧ T.PosDef ∧
          (structuredLMI (affineMap Fs x) (affineMap Rs x) L D S T G ρ).PosDef) :
    x ∈ robustFeasibleSet Fs Rs L D 𝒟 ρ ∧
      ∀ Δ ∈ 𝒟, ‖Δ‖ ≤ ρ → (lfr (affineMap Fs x) (affineMap Rs x) L D Δ).PosDef := by
  obtain ⟨S, T, G, hB, hS, hT, hM⟩ := hx
  set Fx := affineMap Fs x with hFx
  set Rx := affineMap Rs x with hRx
  have hF : Fx.IsSymm := by
    rw [hFx, affineMap, IsSymm, transpose_add, transpose_sum]
    simp only [transpose_smul]
    rw [(hFs 0).eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hFs i.succ).eq]
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hc : 0 < (ρ ^ 2)⁻¹ := by positivity
  have hB' : ((ρ ^ 2)⁻¹ • S, (ρ ^ 2)⁻¹ • T, ρ⁻¹ • G) ∈ scalingSet 𝒟 := by
    intro Δ hΔ
    obtain ⟨h1, h2⟩ := hB Δ hΔ
    simp only at h1 h2 ⊢
    refine ⟨?_, ?_⟩
    · rw [Matrix.smul_mul, Matrix.mul_smul, h1]
    · rw [Matrix.smul_mul, transpose_smul, Matrix.mul_smul, h2, smul_neg]
  have hLMI : (fromBlocks (Fx - (ρ • L) * ((ρ ^ 2)⁻¹ • S) * (ρ • L)ᵀ)
      (Rxᵀ - (ρ • L) * ((ρ ^ 2)⁻¹ • S) * (ρ • D)ᵀ + (ρ • L) * (ρ⁻¹ • G))
      (Rx - (ρ • D) * ((ρ ^ 2)⁻¹ • S) * (ρ • L)ᵀ + (ρ⁻¹ • G)ᵀ * (ρ • L)ᵀ)
      ((ρ ^ 2)⁻¹ • T - (ρ • D) * ((ρ ^ 2)⁻¹ • S) * (ρ • D)ᵀ + (ρ • D) * (ρ⁻¹ • G)
        + (ρ⁻¹ • G)ᵀ * (ρ • D)ᵀ)).PosDef := by
    have e1 : ρ * ((ρ ^ 2)⁻¹ * ρ) = 1 := by field_simp
    have e2 : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ0
    have e3 : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ0
    simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, e1, e2, e3, one_smul]
    exact hM
  have key := lemma_3_2_core Fx hF (ρ • L) Rx (ρ • D) 𝒟 _ _ _ hB' (hS.smul hc) (hT.smul hc) hLMI
  have hmain : ∀ Δ ∈ 𝒟, ‖Δ‖ ≤ ρ → (1 - D * Δ).det ≠ 0 ∧ (lfr Fx Rx L D Δ).PosDef := by
    intro Δ hΔD hΔ
    have hΔ' : ρ⁻¹ • Δ ∈ 𝒟 := 𝒟.smul_mem _ hΔD
    have hn : ‖ρ⁻¹ • Δ‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ]
      rw [inv_mul_le_iff₀ hρ]; linarith
    obtain ⟨hd, hp⟩ := key _ hΔ' hn
    have hDD : (ρ • D) * (ρ⁻¹ • Δ) = D * Δ := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hρ0, one_smul]
    have hLL : (ρ • L) * (ρ⁻¹ • Δ) = L * Δ := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hρ0, one_smul]
    rw [hDD] at hd
    refine ⟨hd, ?_⟩
    rw [hDD, hLL] at hp
    have hT' : (ρ⁻¹ • Δ)ᵀ * (ρ • L)ᵀ = Δᵀ * Lᵀ := by
      rw [← transpose_mul, ← transpose_mul, hLL]
    rw [Matrix.mul_assoc _ (ρ⁻¹ • Δ)ᵀ, hT', ← Matrix.mul_assoc] at hp
    unfold lfr
    have : (1 - Δᵀ * Dᵀ) = (1 - D * Δ)ᵀ := by rw [transpose_sub, transpose_one, transpose_mul]
    rw [this, ← transpose_nonsing_inv]
    exact hp
  refine ⟨fun Δ hΔD hΔ => ⟨(hmain Δ hΔD hΔ).1, (hmain Δ hΔD hΔ).2.posSemidef⟩,
    fun Δ hΔD hΔ => (hmain Δ hΔD hΔ).2⟩

end RobustSDP.Structured

open RobustSDP.Structured


theorem solution {m n p q : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (Rs : Fin (m + 1) → Matrix (Fin q) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin p) ℝ) (D : Matrix (Fin q) (Fin p) ℝ)
    (𝒟 : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ)) (ρ : ℝ) (hρ : 0 < ρ) (x : Fin m → ℝ)
    (hx : ∃ (S : Matrix (Fin p) (Fin p) ℝ) (T : Matrix (Fin q) (Fin q) ℝ)
        (G : Matrix (Fin p) (Fin q) ℝ), (S, T, G) ∈ scalingSet 𝒟 ∧ S.PosDef ∧ T.PosDef ∧
          (structuredLMI (affineMap Fs x) (affineMap Rs x) L D S T G ρ).PosDef) :
    x ∈ robustFeasibleSet Fs Rs L D 𝒟 ρ ∧
      ∀ Δ ∈ 𝒟, ‖Δ‖ ≤ ρ → (lfr (affineMap Fs x) (affineMap Rs x) L D Δ).PosDef := by
  exact theorem_3_2_core Fs hFs Rs L D 𝒟 ρ hρ x hx
