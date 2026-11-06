-- Prove2me | solution 1 for PrimalDualLDR.Multistage.theorem_3_primal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:12:26.765506+00:00
-- url     : https://prove2.me/submissions/5a494bda-5167-4346-bdb3-b234b76aeefa

import Mathlib
import Definitions.Def_PrimalDualLDR_Multistage_Basic
import Definitions.Def_PrimalDualLDR_Multistage_Setting
import Definitions.Def_PrimalDualLDR_Multistage_Problems
import Theorems.Thm_LinearOptimization_farkas_inequality_form

open MeasureTheory Matrix

namespace PDLDRT3Primal

open PrimalDualLDR.Multistage PrimalDualLDR.Multistage.Setting

/-- Under the standing assumptions, an a.s. nonnegative linear function is nonnegative on `Ξ`. -/
theorem nonneg_on_Xi (σ : Setting) (hσ : σ.Standing) {m : ℕ} (Q : Matrix (Fin m) (Fin σ.k) ℝ)
    (hQ : ∀ᵐ ξ ∂σ.P, ∀ i, 0 ≤ Q.mulVec ξ i) : ∀ ξ ∈ σ.Xi, ∀ i, 0 ≤ Q.mulVec ξ i := by
  obtain ⟨-, ⟨-, -, hball⟩, -⟩ := hσ
  intro ξ₀ hξ₀ i
  by_contra hneg
  push Not at hneg
  have hcont : Continuous fun ξ : Fin σ.k → ℝ => Q.mulVec ξ i := by
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hopen : IsOpen {ξ : Fin σ.k → ℝ | Q.mulVec ξ i < 0} := isOpen_lt hcont continuous_const
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen ξ₀ hneg
  have hpos := hball ξ₀ hξ₀ ε hε
  have hnull : σ.P {ξ | ¬ ∀ i, 0 ≤ Q.mulVec ξ i} = 0 := ae_iff.mp hQ
  have : σ.P (Metric.ball ξ₀ ε) = 0 := by
    apply measure_mono_null _ hnull
    intro ξ hξ
    have := hsub hξ
    simp only [Set.mem_setOf_eq] at this ⊢
    intro h
    exact absurd (h i) (not_le.mpr this)
  exact (ne_of_gt hpos) this

/-- Affine Farkas on `Ξ`, row by row. -/
theorem farkas_rows (σ : Setting) (hσ : σ.Standing) {m : ℕ} (Q : Matrix (Fin m) (Fin σ.k) ℝ)
    (hQ : ∀ ξ ∈ σ.Xi, ∀ i, 0 ≤ Q.mulVec ξ i) :
    ∃ Λ : Matrix (Fin m) (Fin σ.l) ℝ, Λ * σ.W = Q ∧ (∀ i, 0 ≤ Λ.mulVec σ.h i) ∧
      ∀ i j, 0 ≤ Λ i j := by
  obtain ⟨-, -, hne, -⟩ := hσ
  have hmemXi : ∀ x : Fin σ.k → ℝ, (-σ.W).mulVec x ≤ -σ.h ↔ x ∈ σ.Xi := by
    intro x
    simp only [Setting.Xi, PrimalDualLDR.FixedRecourse.polyhedron, Set.mem_setOf_eq,
      Pi.le_def, Matrix.neg_mulVec, Pi.neg_apply, neg_le_neg_iff]
  have hfeas : ∃ x : Fin σ.k → ℝ, (-σ.W).mulVec x ≤ -σ.h := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, (hmemXi x).mpr hx⟩
  have hrow : ∀ i : Fin m, ∃ p : Fin σ.l → ℝ, 0 ≤ p ∧ (-σ.W)ᵀ.mulVec p = -(Q i) ∧
      p ⬝ᵥ (-σ.h) ≤ 0 := by
    intro i
    apply (LinearOptimization.farkas_inequality_form (-σ.W) (-σ.h) (-(Q i)) 0 hfeas).mp
    intro x hx
    have := hQ x ((hmemXi x).mp hx) i
    simp only [Matrix.mulVec] at this
    simpa [neg_dotProduct] using this
  choose p hp0 hpW hph using hrow
  refine ⟨Matrix.of fun i j => p i j, ?_, ?_, ?_⟩
  · ext i j
    have := congrFun (hpW i) j
    simp only [Matrix.transpose_neg, Matrix.neg_mulVec, Pi.neg_apply, neg_inj] at this
    rw [← this]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
  · intro i
    have := hph i
    simp only [dotProduct_neg, neg_nonpos] at this
    simpa [Matrix.mulVec, dotProduct, mul_comm] using this
  · intro i j
    exact hp0 i j

/-- The robust-counterpart equivalence used for `𝓜𝒮𝒫^u`. -/
theorem ae_nonneg_iff (σ : Setting) (hσ : σ.Standing) {m : ℕ} (Q : Matrix (Fin m) (Fin σ.k) ℝ) :
    (∀ᵐ ξ ∂σ.P, ∀ i, 0 ≤ Q.mulVec ξ i) ↔
      ∃ Λ : Matrix (Fin m) (Fin σ.l) ℝ, Λ * σ.W = Q ∧ (∀ i, 0 ≤ Λ.mulVec σ.h i) ∧
        ∀ i j, 0 ≤ Λ i j := by
  constructor
  · intro h
    exact farkas_rows σ hσ Q (nonneg_on_Xi σ hσ Q h)
  · rintro ⟨Λ, hΛW, hΛh, hΛ⟩
    have hsupp := hσ.2.1.2.1
    have hXi : ∀ᵐ ξ ∂σ.P, ξ ∈ σ.Xi := by
      rw [ae_iff]
      exact hsupp
    filter_upwards [hXi] with ξ hξ i
    rw [← hΛW, ← Matrix.mulVec_mulVec]
    have hξ' : ∀ j, σ.h j ≤ σ.W.mulVec ξ j := hξ
    calc (0 : ℝ) ≤ Λ.mulVec σ.h i := hΛh i
      _ ≤ Λ.mulVec (σ.W.mulVec ξ) i := by
        simp only [Matrix.mulVec, dotProduct]
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hξ' j) (hΛ i j)

end PDLDRT3Primal

open PDLDRT3Primal in
theorem solution (σ : PrimalDualLDR.Multistage.Setting) (hσ : σ.Standing) :
    σ.valMSPu = σ.valLP42 := by
  -- the residual matrix `B_t P_t − Σ_s A_ts X_s P_s M_t P_t`
  let Q : σ.XFam → (t : Fin σ.T) → Matrix (Fin (σ.m t)) (Fin σ.k) ℝ := fun X t =>
    σ.B t * σ.Pt t - ∑ s, σ.A t s * X s * σ.Pt s * σ.Mt t * σ.Pt t
  apply le_antisymm
  · -- every point of (4.2) gives a point of 𝓜𝒮𝒫^u
    unfold PrimalDualLDR.Multistage.Setting.valMSPu PrimalDualLDR.Multistage.Setting.valLP42
    apply le_iInf₂
    rintro ⟨X, Λ⟩ hp
    let S : σ.SFam := fun t => σ.B t - ∑ s, σ.A t s * X s * σ.Pt s * σ.Mt t
    have hSP : ∀ t, S t * σ.Pt t = Q X t := by
      intro t
      simp only [S, Q]
      rw [Matrix.sub_mul, Matrix.sum_mul]
    have hmem : (X, S) ∈ σ.feasMSPu := by
      intro t
      obtain ⟨hEq, hh, hΛ⟩ := hp t
      have hQ : Q X t = Λ t * σ.W := by
        simp only [Q]
        rw [← hEq]; abel
      have hae := (ae_nonneg_iff σ hσ (Q X t)).mpr ⟨Λ t, hQ.symm, hh, hΛ⟩
      filter_upwards [hae] with ξ hξ
      refine ⟨?_, ?_⟩
      · simp only [hSP, Q, Matrix.sub_mulVec]
        abel
      · simpa [hSP] using hξ
    exact iInf₂_le (f := fun (p : σ.XFam × σ.SFam) (_ : p ∈ σ.feasMSPu) =>
      ((σ.linObj p.1 : ℝ) : EReal)) (X, S) hmem
  · unfold PrimalDualLDR.Multistage.Setting.valMSPu PrimalDualLDR.Multistage.Setting.valLP42
    apply le_iInf₂
    rintro ⟨X, S⟩ hp
    have hlam : ∀ t, ∃ Λ : Matrix (Fin (σ.m t)) (Fin σ.l) ℝ, Λ * σ.W = Q X t ∧
        (∀ i, 0 ≤ Λ.mulVec σ.h i) ∧ ∀ i j, 0 ≤ Λ i j := by
      intro t
      apply (ae_nonneg_iff σ hσ (Q X t)).mp
      filter_upwards [hp t] with ξ hξ
      obtain ⟨hEq, hnn⟩ := hξ
      intro i
      have : (Q X t).mulVec ξ = (S t * σ.Pt t).mulVec ξ := by
        simp only [Q, Matrix.sub_mulVec]
        rw [← hEq]; abel
      rw [this]; exact hnn i
    choose Λ hΛW hΛh hΛ using hlam
    have hmem : (X, Λ) ∈ σ.feasLP42 := by
      intro t
      refine ⟨?_, hΛh t, hΛ t⟩
      simp only
      rw [hΛW t]
      simp only [Q]; abel
    exact iInf₂_le (f := fun (p : σ.XFam × ((t : Fin σ.T) → Matrix (Fin (σ.m t)) (Fin σ.l) ℝ))
      (_ : p ∈ σ.feasLP42) => ((σ.linObj p.1 : ℝ) : EReal)) (X, Λ) hmem
