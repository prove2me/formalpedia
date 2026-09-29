-- Prove2me | solution 1 for RobustSDP.Structured.theorem_5_6
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:21:52.42259+00:00
-- url     : https://prove2.me/submissions/156f459b-e450-4464-886f-609975e729f2

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



lemma key56 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] (Fx : Matrix ι ι ℝ) (lam : ℝ)
    (LL : Matrix ι κ ℝ) (RR : Matrix κ ι ℝ) (S G : Matrix κ κ ℝ) (hSs : Sᵀ = S)
    (ξ : ι → ℝ) (η : κ → ℝ) :
    qfm (fromBlocks (Fx - lam • (1 : Matrix ι ι ℝ) - LL * S * LLᵀ) ((1 / 2 : ℝ) • RRᵀ + LL * G)
      ((1 / 2 : ℝ) • RR - G * LLᵀ) S) (Sum.elim ξ η) =
      ξ ⬝ᵥ (Fx *ᵥ ξ) - lam * (ξ ⬝ᵥ ξ) - (LLᵀ *ᵥ ξ) ⬝ᵥ (S *ᵥ (LLᵀ *ᵥ ξ)) + η ⬝ᵥ (RR *ᵥ ξ)
        + ((LLᵀ *ᵥ ξ) ⬝ᵥ (G *ᵥ η) - η ⬝ᵥ (G *ᵥ (LLᵀ *ᵥ ξ))) + η ⬝ᵥ (S *ᵥ η) := by
  unfold qfm
  rw [fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, elim_dot, add_mulVec, sub_mulVec,
    ← mulVec_mulVec, dotProduct_add, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul,
    smul_eq_mul]
  simp only [dm LL ξ, dm RRᵀ ξ, transpose_transpose]
  rw [dotProduct_comm (RR *ᵥ ξ) η]
  ring

lemma bound56 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (Fx : Matrix ι ι ℝ) (lam : ℝ)
    (LL : Matrix ι κ ℝ) (RR : Matrix κ ι ℝ) (S G : Matrix κ κ ℝ) (hS : S.PosSemidef)
    (hGs : Gᵀ = -G) (d : κ → ℝ) (hd : ∀ s, d s ^ 2 ≤ 1)
    (hSd : S * diagonal d = diagonal d * S) (hGd : G * diagonal d = diagonal d * G)
    (ξ : ι → ℝ) :
    qfm (fromBlocks (Fx - lam • (1 : Matrix ι ι ℝ) - LL * S * LLᵀ) ((1 / 2 : ℝ) • RRᵀ + LL * G)
      ((1 / 2 : ℝ) • RR - G * LLᵀ) S) (Sum.elim ξ (diagonal d *ᵥ (LLᵀ *ᵥ ξ))) ≤
      ξ ⬝ᵥ (Fx *ᵥ ξ) - lam * (ξ ⬝ᵥ ξ) + (LLᵀ *ᵥ ξ) ⬝ᵥ (diagonal d *ᵥ (RR *ᵥ ξ)) := by
  have hSs : Sᵀ = S := hS.1
  rw [key56 Fx lam LL RR S G hSs]
  set u := LLᵀ *ᵥ ξ
  set Δ : Matrix κ κ ℝ := diagonal d with hΔ
  have hΔt : Δᵀ = Δ := diagonal_transpose d
  -- G-term
  have hG : u ⬝ᵥ (G *ᵥ (Δ *ᵥ u)) - (Δ *ᵥ u) ⬝ᵥ (G *ᵥ u) = 0 := by
    have e1 : (Δ *ᵥ u) ⬝ᵥ (G *ᵥ u) = u ⬝ᵥ ((Δ * G) *ᵥ u) := by
      rw [← mulVec_mulVec, dotProduct_comm, dm Δ, hΔt, dotProduct_comm]
    have e2 : u ⬝ᵥ ((G * Δ) *ᵥ u) = -(u ⬝ᵥ ((G * Δ) *ᵥ u)) := by
      conv_lhs => rw [dm, transpose_mul, hΔt, hGs, Matrix.mul_neg, ← hGd, neg_mulVec, neg_dotProduct,
        dotProduct_comm]
    rw [e1, ← hGd, mulVec_mulVec]
    linarith
  have hR : (Δ *ᵥ u) ⬝ᵥ (RR *ᵥ ξ) = u ⬝ᵥ (Δ *ᵥ (RR *ᵥ ξ)) := by
    rw [dm Δ u, hΔt]
  -- S-term
  have hQ : (1 - Δ * Δ).PosSemidef := by
    rw [hΔ, diagonal_mul_diagonal, ← diagonal_one, diagonal_sub]
    refine PosSemidef.diagonal fun s => ?_
    have := hd s
    simp only [Pi.sub_apply, Pi.one_apply, Pi.zero_apply]
    nlinarith
  have hcomm : S * (1 - Δ * Δ) = (1 - Δ * Δ) * S := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc, hSd,
      Matrix.mul_assoc, hSd, Matrix.mul_assoc]
  have hpsd := psd_mul_comm S _ hS hQ hcomm
  have ha := hpsd.dotProduct_mulVec_nonneg u
  rw [star_trivial, Matrix.mul_sub, Matrix.mul_one, sub_mulVec, dotProduct_sub] at ha
  have hdl : ∀ x y, (Δ *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Δ *ᵥ y) := by intro x y; rw [dm Δ x, hΔt]
  have hSS : (Δ *ᵥ u) ⬝ᵥ (S *ᵥ (Δ *ᵥ u)) = u ⬝ᵥ ((S * (Δ * Δ)) *ᵥ u) := by
    rw [hdl, mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, ← hSd, Matrix.mul_assoc]
  rw [hR, hSS]
  linarith


lemma bd_comm {m : ℕ} {r : Fin m → ℕ} (Mb : (i : Fin m) → Matrix (Fin (r i)) (Fin (r i)) ℝ)
    (c : Fin m → ℝ) :
    blockDiagonal' Mb * diagonal (fun s : (Σ i, Fin (r i)) => c s.1) =
      diagonal (fun s : (Σ i, Fin (r i)) => c s.1) * blockDiagonal' Mb := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [mul_diagonal, diagonal_mul]
  by_cases h : i = j
  · subst h; simp only [blockDiagonal'_apply_eq]; ring
  · rw [blockDiagonal'_apply_ne _ _ _ h]; simp

lemma lrd {m n : ℕ} {r : Fin m → ℕ} (Ls : (i : Fin m) → Matrix (Fin n) (Fin (r i)) ℝ)
    (Rs : (i : Fin m) → Matrix (Fin (r i)) (Fin n) ℝ) (c : Fin m → ℝ) (ξ : Fin n → ℝ) :
    ((blockRow Ls)ᵀ *ᵥ ξ) ⬝ᵥ (diagonal (fun s : (Σ i, Fin (r i)) => c s.1) *ᵥ (blockCol Rs *ᵥ ξ)) =
      ∑ i, c i * (ξ ⬝ᵥ (Ls i *ᵥ (Rs i *ᵥ ξ))) := by
  simp only [dotProduct, mulVec_diagonal]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mulVec, dotProduct, blockRow, blockCol, transpose_apply, of_apply, Finset.mul_sum,
    Finset.sum_mul]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem theorem_5_6_core {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (r : Fin m → ℕ)
    (Ls : (i : Fin m) → Matrix (Fin n) (Fin (r i)) ℝ)
    (Rs : (i : Fin m) → Matrix (Fin (r i)) (Fin n) ℝ)
    (hFLR : ∀ i : Fin m, Fs i.succ = (2 : ℝ) • (Ls i * Rs i))
    (xfeas : Fin m → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (Sb Gb : (i : Fin m) → Matrix (Fin (r i)) (Fin (r i)) ℝ)
    (hS : (blockDiagonal' Sb).IsSymm) (hG : (blockDiagonal' Gb)ᵀ = -blockDiagonal' Gb)
    (hLMI : (fromBlocks
      (affineMap Fs xfeas - lam • (1 : Matrix (Fin n) (Fin n) ℝ) -
        blockRow Ls * blockDiagonal' Sb * (blockRow Ls)ᵀ)
      ((1 / 2 : ℝ) • (blockCol Rs)ᵀ + blockRow Ls * blockDiagonal' Gb)
      ((1 / 2 : ℝ) • blockCol Rs - blockDiagonal' Gb * (blockRow Ls)ᵀ)
      (blockDiagonal' Sb)).PosDef) :
    ∀ z : Fin m → ℤ,
      (∀ z' : Fin m → ℤ,
        ‖(fun i => (z i : ℝ)) - xfeas‖ ≤ ‖(fun i => (z' i : ℝ)) - xfeas‖) →
      (affineMap Fs (fun i => (z i : ℝ))).PosSemidef := by
  intro z hz
  classical
  -- rounding bound
  have hround : ∀ i, |(z i : ℝ) - xfeas i| ≤ 1 / 2 := by
    have h1 : ‖(fun i => ((round (xfeas i) : ℤ) : ℝ)) - xfeas‖ ≤ 1 / 2 := by
      refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_
      rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm]
      exact abs_sub_round _
    have h2 := le_trans (hz _) h1
    intro i
    have := norm_le_pi_norm ((fun i => (z i : ℝ)) - xfeas) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at this
    linarith
  set c : Fin m → ℝ := fun i => 2 * ((z i : ℝ) - xfeas i) with hc
  set d : (Σ i, Fin (r i)) → ℝ := fun s => c s.1 with hd
  have hd1 : ∀ s, d s ^ 2 ≤ 1 := by
    intro s
    have h := hround s.1
    simp only [hd, hc]
    rw [abs_le] at h
    nlinarith
  set S := blockDiagonal' Sb
  set G := blockDiagonal' Gb
  set LL := blockRow Ls
  set RR := blockCol Rs
  have hSs : Sᵀ = S := hS
  -- S PSD
  have hpos : ∀ v, 0 ≤ qfm (fromBlocks
      (affineMap Fs xfeas - lam • (1 : Matrix (Fin n) (Fin n) ℝ) - LL * S * LLᵀ)
      ((1 / 2 : ℝ) • RRᵀ + LL * G) ((1 / 2 : ℝ) • RR - G * LLᵀ) S) v := by
    intro v
    have := hLMI.posSemidef.dotProduct_mulVec_nonneg v
    rwa [star_trivial] at this
  have hSpsd : S.PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg (by simpa [IsHermitian] using hSs) fun η => ?_
    have := hpos (Sum.elim 0 η)
    rw [key56 _ lam LL RR S G hSs] at this
    simpa using this
  set zR : Fin m → ℝ := fun i => (z i : ℝ) with hzR
  have hsym : ∀ y : Fin m → ℝ, (affineMap Fs y).IsSymm := by
    intro y
    rw [affineMap, IsSymm, transpose_add, transpose_sum]
    simp only [transpose_smul]
    rw [(hFs 0).eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hFs i.succ).eq]
  have hFz : affineMap Fs zR = affineMap Fs xfeas + ∑ i, (zR i - xfeas i) • Fs i.succ := by
    simp only [affineMap, sub_smul, Finset.sum_sub_distrib]; abel
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    (by simpa [IsHermitian] using (hsym zR).eq) fun ξ => ?_
  rw [star_trivial]
  have hq : ξ ⬝ᵥ (affineMap Fs zR *ᵥ ξ) = ξ ⬝ᵥ (affineMap Fs xfeas *ᵥ ξ) +
      ∑ i, c i * (ξ ⬝ᵥ (Ls i *ᵥ (Rs i *ᵥ ξ))) := by
    rw [hFz, add_mulVec, sum_mulVec, dotProduct_add, dotProduct_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFLR i, smul_mulVec, smul_mulVec, dotProduct_smul, dotProduct_smul, ← mulVec_mulVec]
    simp only [hc, smul_eq_mul, hzR]
    ring
  have hb := bound56 (affineMap Fs xfeas) lam LL RR S G hSpsd hG d hd1
    (bd_comm Sb c) (bd_comm Gb c) ξ
  rw [lrd Ls Rs c ξ] at hb
  have h0 := hpos (Sum.elim ξ (diagonal d *ᵥ (LLᵀ *ᵥ ξ)))
  have hξ : 0 ≤ ξ ⬝ᵥ ξ := Finset.sum_nonneg fun i _ => mul_self_nonneg (ξ i)
  rw [hq]
  nlinarith [mul_nonneg hlam hξ]

end RobustSDP.Structured

open RobustSDP.Structured


theorem solution {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (r : Fin m → ℕ)
    (Ls : (i : Fin m) → Matrix (Fin n) (Fin (r i)) ℝ)
    (Rs : (i : Fin m) → Matrix (Fin (r i)) (Fin n) ℝ)
    (hFLR : ∀ i : Fin m, Fs i.succ = (2 : ℝ) • (Ls i * Rs i))
    (hrank : ∀ i : Fin m, (Fs i.succ).rank = r i)
    (xfeas : Fin m → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (Sb Gb : (i : Fin m) → Matrix (Fin (r i)) (Fin (r i)) ℝ)
    (hS : (blockDiagonal' Sb).IsSymm) (hG : (blockDiagonal' Gb)ᵀ = -blockDiagonal' Gb)
    (hLMI : (fromBlocks
      (affineMap Fs xfeas - lam • (1 : Matrix (Fin n) (Fin n) ℝ) -
        blockRow Ls * blockDiagonal' Sb * (blockRow Ls)ᵀ)
      ((1 / 2 : ℝ) • (blockCol Rs)ᵀ + blockRow Ls * blockDiagonal' Gb)
      ((1 / 2 : ℝ) • blockCol Rs - blockDiagonal' Gb * (blockRow Ls)ᵀ)
      (blockDiagonal' Sb)).PosDef) :
    ∀ z : Fin m → ℤ,
      (∀ z' : Fin m → ℤ,
        ‖(fun i => (z i : ℝ)) - xfeas‖ ≤ ‖(fun i => (z' i : ℝ)) - xfeas‖) →
      (affineMap Fs (fun i => (z i : ℝ))).PosSemidef := by
  exact theorem_5_6_core Fs hFs r Ls Rs hFLR xfeas lam hlam Sb Gb hS hG hLMI
