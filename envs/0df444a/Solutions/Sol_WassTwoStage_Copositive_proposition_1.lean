-- Prove2me | solution 1 for WassTwoStage.Copositive.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:40:52.329448+00:00
-- url     : https://prove2.me/submissions/0610b339-c230-46f0-a1c8-4129607de0f8

import Mathlib
import Definitions.Def_WassTwoStage_Copositive_ConicPrograms

set_option autoImplicit false
open Matrix WassTwoStage.Copositive

noncomputable def copGen {ιK ιMJ ιNJ : Type} [Fintype ιK] [Fintype ιMJ] [Fintype ιNJ] [DecidableEq ιK]
    [DecidableEq ιMJ] [DecidableEq ιNJ]
    (Q : Matrix ιNJ ιK ℝ) (W : Matrix ιMJ ιNJ ℝ) (T : Matrix ιMJ ιK ℝ) (h : ιMJ → ℝ)
    (δ lam s : ℝ) (ψ φ : ιNJ → ℝ) (ξh : ιK → ℝ) :
    Matrix (ιK ⊕ (ιMJ ⊕ Unit)) (ιK ⊕ (ιMJ ⊕ Unit)) ℝ :=
  Matrix.fromBlocks
    (lam • (1 : Matrix ιK ιK ℝ) + Qᵀ * diagonal φ * Q)
    (Matrix.fromCols (-(1 / 2 : ℝ) • Tᵀ - Qᵀ * diagonal φ * Wᵀ)
      (replicateCol Unit (-lam • ξh - (1 / 2 : ℝ) • (Qᵀ *ᵥ ψ))))
    (Matrix.fromRows (-(1 / 2 : ℝ) • T - W * diagonal φ * Q)
      (replicateRow Unit (-lam • ξh - (1 / 2 : ℝ) • (Qᵀ *ᵥ ψ))))
    (Matrix.fromBlocks (W * diagonal φ * Wᵀ + δ • (1 : Matrix ιMJ ιMJ ℝ))
      (replicateCol Unit ((1 / 2 : ℝ) • (W *ᵥ ψ - h)))
      (replicateRow Unit ((1 / 2 : ℝ) • (W *ᵥ ψ - h)))
      (Matrix.of fun _ _ => s))

theorem quadForm {ιK ιMJ ιNJ : Type} [Fintype ιK] [Fintype ιMJ] [Fintype ιNJ] [DecidableEq ιK]
    [DecidableEq ιMJ] [DecidableEq ιNJ]
    (Q : Matrix ιNJ ιK ℝ) (W : Matrix ιMJ ιNJ ℝ) (T : Matrix ιMJ ιK ℝ) (h : ιMJ → ℝ)
    (δ lam s : ℝ) (ψ φ : ιNJ → ℝ) (ξh : ιK → ℝ)
    (a : ιK → ℝ) (b : ιMJ → ℝ) (c : ℝ) :
    (Sum.elim a (Sum.elim b (fun _ : Unit => c)) : ιK ⊕ (ιMJ ⊕ Unit) → ℝ) ⬝ᵥ
      (copGen Q W T h δ lam s ψ φ ξh *ᵥ
        (Sum.elim a (Sum.elim b (fun _ : Unit => c)) : ιK ⊕ (ιMJ ⊕ Unit) → ℝ))
    = lam * (a ⬝ᵥ a) + ∑ j, φ j * ((Q *ᵥ a) j - (Wᵀ *ᵥ b) j) ^ 2 + δ * (b ⬝ᵥ b)
      - (T *ᵥ a) ⬝ᵥ b
      + 2 * c * (-lam * (ξh ⬝ᵥ a) - (1/2) * (ψ ⬝ᵥ (Q *ᵥ a)) + (1/2) * ((Wᵀ *ᵥ b) ⬝ᵥ ψ)
          - (1/2) * (b ⬝ᵥ h)) + s * c ^ 2 := by
  have hcol : ∀ {ι : Type} [Fintype ι] (v : ι → ℝ), replicateCol Unit v *ᵥ (fun _ : Unit => c) = c • v := by
    intro ι _ v; ext i; simp [Matrix.mulVec, dotProduct, replicateCol, mul_comm]
  have hD : (Matrix.of fun (_ _ : Unit) => s) *ᵥ (fun _ : Unit => c) = fun _ => s * c := by
    ext i; simp [Matrix.mulVec, dotProduct]
  unfold copGen
  simp only [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.fromCols_mulVec_sumElim, Matrix.fromRows_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.neg_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hcol, hD,
    replicateRow_mulVec_eq_const, sumElim_dotProduct_sumElim, Matrix.mulVec_replicateCol_eq_const]
  rw [← Sum.elim_add_add, sumElim_dotProduct_sumElim]
  have hU : ∀ (x y : Unit → ℝ), x ⬝ᵥ y = x () * y () := by intro x y; simp [dotProduct]
  simp only [hU, Function.const_apply, Pi.add_apply]
  have A1 : ∀ y : ιNJ → ℝ, a ⬝ᵥ (Qᵀ *ᵥ y) = (Q *ᵥ a) ⬝ᵥ y := by
    intro y; rw [dotProduct_mulVec, Matrix.vecMul_transpose]
  have A2 : ∀ y : ιNJ → ℝ, b ⬝ᵥ (W *ᵥ y) = (Wᵀ *ᵥ b) ⬝ᵥ y := by
    intro y; rw [dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have A3 : a ⬝ᵥ (Tᵀ *ᵥ b) = (T *ᵥ a) ⬝ᵥ b := by
    rw [dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  have Dg : ∀ x y : ιNJ → ℝ, x ⬝ᵥ (diagonal φ *ᵥ y) = ∑ j, x j * φ j * y j := by
    intro x y; simp [dotProduct, Matrix.mulVec_diagonal, mul_assoc]
  have hS : ∑ j, φ j * ((Q *ᵥ a) j - (Wᵀ *ᵥ b) j) ^ 2
      = ∑ j, (Q *ᵥ a) j * φ j * (Q *ᵥ a) j - 2 * ∑ j, (Q *ᵥ a) j * φ j * (Wᵀ *ᵥ b) j
        + ∑ j, (Wᵀ *ᵥ b) j * φ j * (Wᵀ *ᵥ b) j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intros; ring
  have hS2 : ∑ j, (Wᵀ *ᵥ b) j * φ j * (Q *ᵥ a) j = ∑ j, (Q *ᵥ a) j * φ j * (Wᵀ *ᵥ b) j := by
    apply Finset.sum_congr rfl; intros; ring
  simp only [dotProduct_add, add_dotProduct, dotProduct_sub, sub_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, A1, A2, A3, Dg, Matrix.mulVec_neg]
  have e1 : (Qᵀ *ᵥ ψ) ⬝ᵥ a = (Q *ᵥ a) ⬝ᵥ ψ := by rw [dotProduct_comm, A1]
  have e2 : (W *ᵥ ψ) ⬝ᵥ b = (Wᵀ *ᵥ b) ⬝ᵥ ψ := by rw [dotProduct_comm, A2]
  rw [e1, e2, dotProduct_comm a ξh, dotProduct_comm h b, dotProduct_comm b (T *ᵥ a),
    dotProduct_comm ψ (Q *ᵥ a), hS, hS2]
  ring

theorem colmul {p q' : Type} [Fintype p] [Fintype q'] {m : ℕ} (M : Matrix p q' ℝ) (A : Matrix q' (Fin m) ℝ) (l : Fin m) :
    M *ᵥ (fun k => A k l) = fun j => (M * A) j l := by
  ext j; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem perI_core {ιK ιMJ ιNJ : Type} [Fintype ιK] [Fintype ιMJ] [Fintype ιNJ] [DecidableEq ιK]
    [DecidableEq ιMJ] [DecidableEq ιNJ] {m : ℕ}
    (Q : Matrix ιNJ ιK ℝ) (W : Matrix ιMJ ιNJ ℝ) (T : Matrix ιMJ ιK ℝ) (h : ιMJ → ℝ) (q : ιNJ → ℝ)
    (δ lam s : ℝ) (ψ φ : ιNJ → ℝ) (ξ : ιK → ℝ)
    (A : Matrix ιK (Fin m) ℝ) (Bm : Matrix ιMJ (Fin m) ℝ) (c : Fin m → ℝ)
    (hA : ∀ k l, 0 ≤ A k l) (hBm : ∀ j l, 0 ≤ Bm j l) (hc : ∀ l, 0 ≤ c l)
    (hZ : MurtyKabadi.Reduction.Copositive (copGen Q W T h δ lam s ψ φ ξ))
    (hc1 : ∑ l, c l * c l = 1)
    (hlin : Q *ᵥ (A *ᵥ c) + q = Wᵀ *ᵥ (Bm *ᵥ c))
    (hdiag : ∀ j, ∑ l, ((Q * A) j l - (Wᵀ * Bm) j l) ^ 2 = q j ^ 2) :
    trace (T * (A * Bmᵀ)) + h ⬝ᵥ (Bm *ᵥ c) - δ * trace (Bm * Bmᵀ)
      - lam * (trace (A * Aᵀ) - 2 * (ξ ⬝ᵥ (A *ᵥ c)) + ξ ⬝ᵥ ξ)
      ≤ s + q ⬝ᵥ ψ - lam * (ξ ⬝ᵥ ξ) + ∑ j, φ j * q j ^ 2 := by
  have hcol : ∀ l, 0 ≤ lam * ((fun k => A k l) ⬝ᵥ (fun k => A k l))
      + ∑ j, φ j * ((Q * A) j l - (Wᵀ * Bm) j l) ^ 2 + δ * ((fun j => Bm j l) ⬝ᵥ (fun j => Bm j l))
      - ((T * A) · l) ⬝ᵥ (fun j => Bm j l)
      + 2 * c l * (-lam * (ξ ⬝ᵥ (fun k => A k l)) - (1/2) * (ψ ⬝ᵥ (fun j => (Q * A) j l))
          + (1/2) * ((fun j => (Wᵀ * Bm) j l) ⬝ᵥ ψ) - (1/2) * ((fun j => Bm j l) ⬝ᵥ h))
      + s * c l ^ 2 := by
    intro l
    have := hZ (Sum.elim (fun k => A k l) (Sum.elim (fun j => Bm j l) (fun _ : Unit => c l)))
      (by
        intro x
        rcases x with k | j | u
        · exact hA k l
        · exact hBm j l
        · exact hc l)
    rw [MurtyKabadi.Reduction.Q, quadForm, colmul, colmul, colmul] at this
    exact this
  -- column quantities
  set F1 : Fin m → ℝ := fun l => ∑ k, A k l * A k l with hF1
  set F2 : Fin m → ℝ := fun l => ∑ j, φ j * ((Q * A) j l - (Wᵀ * Bm) j l) ^ 2 with hF2
  set F3 : Fin m → ℝ := fun l => ∑ j, Bm j l * Bm j l with hF3
  set F4 : Fin m → ℝ := fun l => ∑ j, (T * A) j l * Bm j l with hF4
  set F5 : Fin m → ℝ := fun l => c l * ∑ k, ξ k * A k l with hF5
  set F6 : Fin m → ℝ := fun l => c l * ∑ j, ψ j * (Q * A) j l with hF6
  set F7 : Fin m → ℝ := fun l => c l * ∑ j, (Wᵀ * Bm) j l * ψ j with hF7
  set F8 : Fin m → ℝ := fun l => c l * ∑ j, Bm j l * h j with hF8
  set F9 : Fin m → ℝ := fun l => c l * c l with hF9
  have hsum : 0 ≤ ∑ l, (lam * F1 l + F2 l + δ * F3 l - F4 l - 2 * lam * F5 l - F6 l + F7 l - F8 l
      + s * F9 l) := by
    apply Finset.sum_nonneg
    intro l _
    have := hcol l
    simp only [hF1, hF2, hF3, hF4, hF5, hF6, hF7, hF8, hF9]
    unfold dotProduct at this
    refine le_of_le_of_eq this ?_
    ring
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have e1 : ∑ l, F1 l = trace (A * Aᵀ) := by
    simp only [hF1, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
  have e2 : ∑ l, F2 l = ∑ j, φ j * q j ^ 2 := by
    simp only [hF2]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum, hdiag]
  have e3 : ∑ l, F3 l = trace (Bm * Bmᵀ) := by
    simp only [hF3, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
  have e4 : ∑ l, F4 l = trace (T * (A * Bmᵀ)) := by
    rw [← Matrix.mul_assoc]
    simp only [hF4, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
  have e5 : ∑ l, F5 l = ξ ⬝ᵥ (A *ᵥ c) := by
    simp only [hF5, dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    ring
  have e6 : ∑ l, F6 l = ψ ⬝ᵥ (Q *ᵥ (A *ᵥ c)) := by
    rw [Matrix.mulVec_mulVec]
    simp only [hF6, dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    ring
  have e7 : ∑ l, F7 l = ψ ⬝ᵥ (Wᵀ *ᵥ (Bm *ᵥ c)) := by
    rw [Matrix.mulVec_mulVec]
    simp only [hF7, dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    ring
  have e8 : ∑ l, F8 l = h ⬝ᵥ (Bm *ᵥ c) := by
    simp only [hF8, dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    ring
  have e9 : ∑ l, F9 l = 1 := hc1
  have e67 : ψ ⬝ᵥ (Wᵀ *ᵥ (Bm *ᵥ c)) = ψ ⬝ᵥ (Q *ᵥ (A *ᵥ c)) + ψ ⬝ᵥ q := by
    rw [← hlin, dotProduct_add]
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e67] at hsum
  have eq' : q ⬝ᵥ ψ = ψ ⬝ᵥ q := dotProduct_comm _ _
  rw [eq']
  nlinarith [hsum]

theorem gramEq {p r : Type} [Fintype p] [Fintype r] {m : ℕ} (X : Matrix p (Fin m) ℝ)
    (Z : Matrix r (Fin m) ℝ) (x : p → ℝ) (z : r → ℝ) :
    x ⬝ᵥ ((X * Zᵀ) *ᵥ z) = (Xᵀ *ᵥ x) ⬝ᵥ (Zᵀ *ᵥ z) := by
  rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.mulVec_transpose]

theorem perI {ιK ιMJ ιNJ : Type} [Fintype ιK] [Fintype ιMJ] [Fintype ιNJ] [DecidableEq ιK]
    [DecidableEq ιMJ] [DecidableEq ιNJ]
    (Q : Matrix ιNJ ιK ℝ) (W : Matrix ιMJ ιNJ ℝ) (T : Matrix ιMJ ιK ℝ) (h : ιMJ → ℝ) (q : ιNJ → ℝ)
    (δ lam s : ℝ) (ψ φ : ιNJ → ℝ) (ξ : ιK → ℝ)
    (Ω : Matrix ιK ιK ℝ) (Y : Matrix ιK ιMJ ℝ) (μ : ιK → ℝ) (Γ : Matrix ιMJ ιMJ ℝ) (γ : ιMJ → ℝ)
    (hZ : MurtyKabadi.Reduction.Copositive (copGen Q W T h δ lam s ψ φ ξ))
    (hCP : CompletelyPositive (cpMatrix Ω Y μ Γ γ))
    (hlin : Q *ᵥ μ + q = Wᵀ *ᵥ γ)
    (hdiag : ∀ j, Q j ⬝ᵥ (Ω *ᵥ Q j) - 2 * (Q j ⬝ᵥ (Y *ᵥ Wᵀ j)) + Wᵀ j ⬝ᵥ (Γ *ᵥ Wᵀ j) = q j ^ 2) :
    trace (T * Y) + h ⬝ᵥ γ - δ * trace Γ - lam * (trace Ω - 2 * (ξ ⬝ᵥ μ) + ξ ⬝ᵥ ξ)
      ≤ s + q ⬝ᵥ ψ - lam * (ξ ⬝ᵥ ξ) + ∑ j, φ j * q j ^ 2 := by
  obtain ⟨m, B, hB0, hB⟩ := hCP
  set A : Matrix ιK (Fin m) ℝ := fun k l => B (Sum.inl k) l with hA
  set Bm : Matrix ιMJ (Fin m) ℝ := fun j l => B (Sum.inr (Sum.inl j)) l with hBm
  set c : Fin m → ℝ := fun l => B (Sum.inr (Sum.inr ())) l with hc
  have hΩ : Ω = A * Aᵀ := by
    ext k k'
    exact congrFun (congrFun hB (Sum.inl k)) (Sum.inl k')
  have hY : Y = A * Bmᵀ := by
    ext k j
    exact congrFun (congrFun hB (Sum.inl k)) (Sum.inr (Sum.inl j))
  have hΓ : Γ = Bm * Bmᵀ := by
    ext j j'
    exact congrFun (congrFun hB (Sum.inr (Sum.inl j))) (Sum.inr (Sum.inl j'))
  have hμ : μ = A *ᵥ c := by
    ext k
    exact congrFun (congrFun hB (Sum.inl k)) (Sum.inr (Sum.inr ()))
  have hγ : γ = Bm *ᵥ c := by
    ext j
    exact congrFun (congrFun hB (Sum.inr (Sum.inl j))) (Sum.inr (Sum.inr ()))
  have hc1 : ∑ l, c l * c l = 1 :=
    (congrFun (congrFun hB (Sum.inr (Sum.inr ()))) (Sum.inr (Sum.inr ()))).symm
  have hnnA : ∀ k l, 0 ≤ A k l := fun k l => hB0 _ _
  have hnnB : ∀ j l, 0 ≤ Bm j l := fun j l => hB0 _ _
  have hnnc : ∀ l, 0 ≤ c l := fun l => hB0 _ _
  have hdiag' : ∀ j, ∑ l, ((Q * A) j l - (Wᵀ * Bm) j l) ^ 2 = q j ^ 2 := by
    intro j
    have hu : Aᵀ *ᵥ Q j = fun l => (Q * A) j l := by
      ext l; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm]
    have hw : Bmᵀ *ᵥ Wᵀ j = fun l => (Wᵀ * Bm) j l := by
      ext l; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm]
    have := hdiag j
    rw [hΩ, hY, hΓ, gramEq, gramEq, gramEq, hu, hw] at this
    rw [← this]
    simp only [dotProduct, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intros; ring
  clear hB
  subst hΩ hY hΓ hμ hγ
  apply perI_core Q W T h q δ lam s ψ φ ξ A Bm c hnnA hnnB hnnc hZ hc1 hlin hdiag'

theorem solution {K J M N₁ N₂ I : ℕ} (d : Data K J M N₁ N₂ I) (x : Fin N₁ → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    d.lowerValue δ x ≤ d.upperValue δ x := by
  unfold Data.lowerValue Data.upperValue
  refine iSup_le fun γ => iSup_le fun μ => iSup_le fun Γ => iSup_le fun Ω => iSup_le fun Y =>
    iSup_le fun hfeas => ?_
  refine le_iInf fun lam => le_iInf fun s => le_iInf fun ψ => le_iInf fun φ => le_iInf fun hcop => ?_
  rw [EReal.coe_le_coe_iff]
  obtain ⟨hnn, hlin, hdiag, hbud, hcp⟩ := hfeas
  obtain ⟨hlam, hcopi⟩ := hcop
  have hnorm : ∀ i, ‖d.ξhat i‖ ^ 2 = WithLp.ofLp (d.ξhat i) ⬝ᵥ WithLp.ofLp (d.ξhat i) := by
    intro i
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, sq]
  have hi : ∀ i, trace (d.bT x * Y i) + d.bh x ⬝ᵥ γ i - δ * trace (Γ i)
      - lam * (trace (Ω i) - 2 * (WithLp.ofLp (d.ξhat i) ⬝ᵥ μ i)
        + WithLp.ofLp (d.ξhat i) ⬝ᵥ WithLp.ofLp (d.ξhat i))
      ≤ s i + d.bq ⬝ᵥ ψ i - lam * ‖d.ξhat i‖ ^ 2 + ∑ j, φ i j * d.bq j ^ 2 := by
    intro i
    rw [hnorm]
    exact perI d.bQ d.bW (d.bT x) (d.bh x) d.bq δ lam (s i) (ψ i) (φ i) (WithLp.ofLp (d.ξhat i))
      (Ω i) (Y i) (μ i) (Γ i) (γ i) (hcopi i) (hcp i) (hlin i) (hdiag i)
  unfold Data.cpObjective Data.copObjective
  have hinv : 0 ≤ 1 / (I : ℝ) := by positivity
  have hsum : ∑ i, (trace (d.bT x * Y i) + d.bh x ⬝ᵥ γ i - δ * trace (Γ i)) ≤
      ∑ i, (s i + d.bq ⬝ᵥ ψ i - lam * ‖d.ξhat i‖ ^ 2 + ∑ j, φ i j * d.bq j ^ 2)
        + lam * ∑ i, (trace (Ω i) - 2 * (WithLp.ofLp (d.ξhat i) ⬝ᵥ μ i)
          + WithLp.ofLp (d.ξhat i) ⬝ᵥ WithLp.ofLp (d.ξhat i)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have := hi i
    linarith
  have h2 := mul_le_mul_of_nonneg_left hsum hinv
  have h3 := mul_le_mul_of_nonneg_left hbud hlam
  nlinarith [h2, h3]
