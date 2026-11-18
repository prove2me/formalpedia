-- Prove2me | solution 2 for RandomDimReduction.Channel.RTP_embedded_twirl
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T19:55:29.254687+00:00
-- url     : https://prove2.me/submissions/b95eecf9-4f58-4c5c-b8bc-0bae41c27519

import Theorems.Thm_RandomDimReduction_Channel_schur_coordinates_exist
import Theorems.Thm_RandomDimReduction_Channel_theorem_5_3
import Theorems.Thm_RandomDimReduction_Channel_lemma_5_4
import Theorems.Thm_RandomDimReduction_Channel_lemma_5_5
import Theorems.Thm_RandomDimReduction_Channel_lemma_5_6
import Theorems.Thm_RandomDimReduction_Channel_lemma_2_2
import Theorems.Thm_RandomDimReduction_Channel_lemma_B_1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

def rawBlock {L : Type} {a b : L → Type}
    (D : Matrix (Sigma a) (Sigma b) ℂ) (l m : L) : Matrix (a l) (b m) ℂ :=
  fun i j => D ⟨l,i⟩ ⟨m,j⟩

lemma rawBlock_mul_right {L : Type} [Fintype L] [DecidableEq L]
    {a b c : L → Type} [∀ l, Fintype (b l)]
    (D : Matrix (Sigma a) (Sigma b) ℂ) (R : ∀ l, Matrix (b l) (c l) ℂ) (l m : L) :
    rawBlock (D * Matrix.blockDiagonal' R) l m = rawBlock D l m * R m := by
  ext i j
  simp only [rawBlock, Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single m]
  · simp [Matrix.blockDiagonal'_apply_eq]
  · intro t _ htm
    simp [Matrix.blockDiagonal'_apply_ne _ _ _ htm]
  · simp

lemma rawBlock_mul_left {L : Type} [Fintype L] [DecidableEq L]
    {a b c : L → Type} [∀ l, Fintype (b l)]
    (R : ∀ l, Matrix (a l) (b l) ℂ) (D : Matrix (Sigma b) (Sigma c) ℂ) (l m : L) :
    rawBlock (Matrix.blockDiagonal' R * D) l m = R l * rawBlock D l m := by
  ext i j
  simp only [rawBlock, Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single l]
  · simp [Matrix.blockDiagonal'_apply_eq]
  · intro t _ htl
    simp [Matrix.blockDiagonal'_apply_ne _ _ _ htl.symm]
  · simp

end RandomDimReduction.Channel


namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma schur_conjugate_injective {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    (U : Matrix b a ℂ) (hU : Uᴴ * U = 1) :
    Function.Injective (fun X : Op a => U * X * Uᴴ) := by
  have hc (X : Op a) : Uᴴ * (U * X * Uᴴ) * U = X := by
    calc
      _ = (Uᴴ * U) * X * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hU, Matrix.one_mul, Matrix.mul_one]
  intro X Y he
  have h := congrArg (fun Z : Op b => Uᴴ * Z * U) he
  rw [hc X, hc Y] at h
  exact h

lemma reductionBlocks_embedded (n k d : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkd : k ≤ d)
    (κ : SpechtModel n) (Sd : SchurTransform κ d) (Sk : SchurTransform κ k)
    (W : Matrix (Fin d) (Fin k) ℂ) (hW : Wᴴ * W = 1) (X₀ : Op (Word n k)) :
    reductionBlocks (k := k) Sd (tensor n W * X₀ * (tensor n W)ᴴ) = twirlBlocks Sk X₀ := by
  obtain ⟨eta, heta, hiso⟩ := lemma_5_5 n k d hn hk hkd κ Sd Sk W hW
  let T := tensor n W
  let D : Matrix (SchurIndex n d) (SchurIndex n k) ℂ := Sd.U * T * Sk.Uᴴ
  let Z := Sk.U * X₀ * Sk.Uᴴ
  have hD : D = Matrix.blockDiagonal' (fun lam =>
      Matrix.kronecker (1 : Op (Fin (spechtDim lam))) (eta lam)) := heta
  have hfull : Sd.U * (T * X₀ * Tᴴ) * Sd.Uᴴ = D * Z * Dᴴ := by
    symm
    calc
      _ = Sd.U * T * (Sk.Uᴴ * Sk.U) * X₀ * (Sk.Uᴴ * Sk.U) * Tᴴ * Sd.Uᴴ := by
        dsimp [D, Z]
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = _ := by rw [Sk.right_unitary]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hb (lam : Shape n) :
      schurBlock Sd (T * X₀ * Tᴴ) lam lam =
        Matrix.kronecker (1 : Op (Fin (spechtDim lam))) (eta lam) *
          schurBlock Sk X₀ lam lam *
            (Matrix.kronecker (1 : Op (Fin (spechtDim lam))) (eta lam))ᴴ := by
    change rawBlock (Sd.U * (T * X₀ * Tᴴ) * Sd.Uᴴ) lam lam = _
    rw [hfull, hD, Matrix.blockDiagonal'_conjTranspose,
      rawBlock_mul_right, rawBlock_mul_left]
    rfl
  have htrace (lam : Shape n) :
      WildeQIT.partialTraceRight (schurBlock Sd (T * X₀ * Tᴴ) lam lam) =
        WildeQIT.partialTraceRight (schurBlock Sk X₀ lam lam) := by
    rw [hb]
    simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
    have h := lemma_B_1 (schurBlock Sk X₀ lam lam) (eta lam) (eta lam)
    simpa only [Matrix.kronecker, hiso lam, Matrix.one_kronecker_one, Matrix.one_mul] using h
  change Matrix.blockDiagonal' _ = Matrix.blockDiagonal' _
  congr 1
  funext lam
  rw [htrace]

end RandomDimReduction.Channel

open RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (n k d : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkd : k ≤ d)
    (W : Matrix (Fin d) (Fin k) ℂ) (hW : Wᴴ * W = 1) (X₀ : Op (Word n k)) :
    RTP n k d (tensor n W * X₀ * (tensor n W)ᴴ) = twirl n k X₀ := by
  obtain ⟨κ,hS⟩ := RandomDimReduction.Channel.schur_coordinates_exist n hn
  let Sd := Classical.choice (hS d (hk.trans hkd))
  let Sk := Classical.choice (hS k hk)
  let X := tensor n W * X₀ * (tensor n W)ᴴ
  have hQ := (lemma_2_2 n k d hn hk hkd W hW X₀).1
  have hhigh := (lemma_5_6 n k d hn hk hkd).2.2
  have hR := (theorem_5_3 n k d hn hk hkd κ Sd Sk).2 X
  rw [← hhigh, show kernelProjector n k d * X = 0 from hQ,
    Matrix.trace_zero, zero_div, zero_smul, zero_add] at hR
  apply schur_conjugate_injective Sk.U Sk.right_unitary
  change Sk.U * RTP n k d X * Sk.Uᴴ = Sk.U * twirl n k X₀ * Sk.Uᴴ
  rw [hR, lemma_5_4 n k hn hk κ Sk X₀]
  exact reductionBlocks_embedded n k d hn hk hkd κ Sd Sk W hW X₀
