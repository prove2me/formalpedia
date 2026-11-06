-- Prove2me | solution 1 for PrimalDualLDR.RandomRecourse.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:15:05.000216+00:00
-- url     : https://prove2.me/submissions/8717c011-7fe8-45f8-b459-199789cef50d

import Mathlib
import Definitions.Def_PrimalDualLDR_RandomRecourse_Setting
import Theorems.Thm_ConvexOptimization_s_procedure

open MeasureTheory Matrix

namespace PDLDRProp6Aux

open PrimalDualLDR.RandomRecourse

lemma qcont {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) :
    Continuous fun ξ : Fin k → ℝ => ξ ⬝ᵥ (S *ᵥ ξ) := by
  simp only [dotProduct, mulVec]
  fun_prop

lemma isHerm_of_symm {k : ℕ} {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.IsSymm) : S.IsHermitian := by
  show Sᴴ = S
  rw [conjTranspose_eq_transpose_of_trivial]
  exact hS

lemma psd_of_forall {k : ℕ} {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.IsSymm)
    (h : ∀ x, 0 ≤ x ⬝ᵥ (S *ᵥ x)) : S.PosSemidef :=
  PosSemidef.of_dotProduct_mulVec_nonneg (isHerm_of_symm hS) (fun x => by
    simpa only [star_trivial] using h x)

lemma symm_swap {k : ℕ} {W : Matrix (Fin k) (Fin k) ℝ} (hW : W.IsSymm) (u v : Fin k → ℝ) :
    u ⬝ᵥ (W *ᵥ v) = v ⬝ᵥ (W *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, hW.eq]

/-- Step 1: almost-sure nonnegativity of a quadratic form holds on the whole support `Ξ`. -/
lemma on_Xi (σ : Setting) (hσ : σ.Standing) (S : Matrix (Fin σ.k) (Fin σ.k) ℝ)
    (h : ∀ᵐ ξ ∂σ.P, 0 ≤ ξ ⬝ᵥ (S *ᵥ ξ)) : ∀ ξ ∈ σ.Xi, 0 ≤ ξ ⬝ᵥ (S *ᵥ ξ) := by
  intro ξ0 hξ0
  by_contra hneg
  push_neg at hneg
  have hopen : IsOpen {ξ : Fin σ.k → ℝ | ξ ⬝ᵥ (S *ᵥ ξ) < 0} :=
    isOpen_lt (qcont S) continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen ξ0 hneg
  have hpos := hσ.2.2.1.2.2 ξ0 hξ0 ε hε
  have hzero : σ.P {ξ | ¬ 0 ≤ ξ ⬝ᵥ (S *ᵥ ξ)} = 0 := ae_iff.mp h
  have hle : σ.P (Metric.ball ξ0 ε) ≤ σ.P {ξ | ¬ 0 ≤ ξ ⬝ᵥ (S *ᵥ ξ)} := by
    apply measure_mono
    intro ξ hξ
    have := hball hξ
    simp only [Set.mem_setOf_eq] at this ⊢
    linarith
  rw [hzero] at hle
  exact absurd (le_zero_iff.mp hle) (ne_of_gt hpos)

/-- Step 2: for `l = 1`, nonnegativity on `Ξ` gives the homogeneous implication
`ξᵀWξ ≥ 0 ⇒ ξᵀSξ ≥ 0` on all of `ℝ^k`. -/
lemma homog (σ : Setting) (hσ : σ.Standing) (hl : σ.l = 1) (S : Matrix (Fin σ.k) (Fin σ.k) ℝ)
    (hS : ∀ ξ ∈ σ.Xi, 0 ≤ ξ ⬝ᵥ (S *ᵥ ξ)) (ℓ0 : Fin σ.l) :
    ∀ x, 0 ≤ x ⬝ᵥ (σ.W ℓ0 *ᵥ x) → 0 ≤ x ⬝ᵥ (S *ᵥ x) := by
  have hall : ∀ ℓ : Fin σ.l, ℓ = ℓ0 := fun ℓ => Fin.ext (by have := ℓ.isLt; have := ℓ0.isLt; omega)
  intro x hx
  set i0 : Fin σ.k := ⟨0, σ.hk⟩ with hi0
  have he1 : ∀ y : Fin σ.k → ℝ, σ.e1 ⬝ᵥ y = y i0 := by
    intro y
    simp [Setting.e1, i0]
  have hmem : ∀ y : Fin σ.k → ℝ, y i0 = 1 → 0 ≤ y ⬝ᵥ (σ.W ℓ0 *ᵥ y) → y ∈ σ.Xi := by
    intro y hy1 hy2
    refine ⟨by rw [he1]; exact hy1, fun ℓ => ?_⟩
    rw [hall ℓ]; exact hy2
  by_cases hx0 : x i0 = 0
  · by_cases hxz : x = 0
    · simp [hxz]
    exfalso
    obtain ⟨ξ0, hξ0⟩ := hσ.2.2.2.1
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hσ.2.2.2.2.1
    have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hxz
    have hWs := symm_swap (hσ.2.1 ℓ0)
    have ha : 0 ≤ ξ0 ⬝ᵥ (σ.W ℓ0 *ᵥ ξ0) := hξ0.2 ℓ0
    have hξ01 : ξ0 i0 = 1 := by rw [← he1 ξ0]; exact hξ0.1
    set t : ℝ := (R + ‖ξ0‖ + 1) / ‖x‖ with ht
    have htx : t * ‖x‖ = R + ‖ξ0‖ + 1 := by rw [ht]; field_simp
    have hRn : 0 ≤ R := le_trans (norm_nonneg _) (hR ξ0 hξ0)
    have htpos : 0 < t := by rw [ht]; positivity
    have key : ∀ s : ℝ, |s| = t → 0 ≤ s * (ξ0 ⬝ᵥ (σ.W ℓ0 *ᵥ x)) → False := by
      intro s hs hsb
      have hexp : (ξ0 + s • x) ⬝ᵥ (σ.W ℓ0 *ᵥ (ξ0 + s • x)) =
          ξ0 ⬝ᵥ (σ.W ℓ0 *ᵥ ξ0) + 2 * (s * (ξ0 ⬝ᵥ (σ.W ℓ0 *ᵥ x))) +
            (s * s) * (x ⬝ᵥ (σ.W ℓ0 *ᵥ x)) := by
        have h2 := hWs x ξ0
        simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
          smul_dotProduct, smul_eq_mul] at *
        rw [h2]; ring
      have hy : ξ0 + s • x ∈ σ.Xi := by
        apply hmem
        · simp [hξ01, hx0]
        · rw [hexp]
          have := mul_nonneg (mul_self_nonneg s) hx
          linarith
      have hn := hR _ hy
      have h1 : ‖s • x‖ = R + ‖ξ0‖ + 1 := by rw [norm_smul, Real.norm_eq_abs, hs, htx]
      have h2 : ‖s • x‖ ≤ ‖ξ0 + s • x‖ + ‖ξ0‖ := by
        have := norm_sub_le (ξ0 + s • x) ξ0
        simpa using this
      linarith
    by_cases hb : 0 ≤ ξ0 ⬝ᵥ (σ.W ℓ0 *ᵥ x)
    · exact key t (abs_of_pos htpos) (mul_nonneg htpos.le hb)
    · push_neg at hb
      exact key (-t) (by rw [abs_neg, abs_of_pos htpos])
        (by nlinarith)
  · set c := x i0 with hc
    have hcinv : (c⁻¹ • x) i0 = 1 := by simp [← hc, inv_mul_cancel₀ hx0]
    have hq : ∀ M : Matrix (Fin σ.k) (Fin σ.k) ℝ,
        (c⁻¹ • x) ⬝ᵥ (M *ᵥ (c⁻¹ • x)) = (c⁻¹ * c⁻¹) * (x ⬝ᵥ (M *ᵥ x)) := by
      intro M
      simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
    have hpos : 0 < c⁻¹ * c⁻¹ := mul_self_pos.mpr (inv_ne_zero hx0)
    have hy : c⁻¹ • x ∈ σ.Xi := by
      apply hmem _ hcinv
      rw [hq]; exact mul_nonneg hpos.le hx
    have := hS _ hy
    rw [hq] at this
    exact (mul_nonneg_iff_of_pos_left hpos).mp this

end PDLDRProp6Aux

open PDLDRProp6Aux in
theorem solution (σ : PrimalDualLDR.RandomRecourse.Setting) (hσ : σ.Standing)
    (S : Matrix (Fin σ.k) (Fin σ.k) ℝ) (hS : S.IsSymm) :
    ((∃ lam : Fin σ.l → ℝ, (∀ ℓ, 0 ≤ lam ℓ) ∧ (S - ∑ ℓ : Fin σ.l, lam ℓ • σ.W ℓ).PosSemidef) →
        ∀ᵐ ξ ∂σ.P, 0 ≤ ξ ⬝ᵥ (S *ᵥ ξ)) ∧
      (σ.l = 1 → (∀ᵐ ξ ∂σ.P, 0 ≤ ξ ⬝ᵥ (S *ᵥ ξ)) →
        ∃ lam : Fin σ.l → ℝ, (∀ ℓ, 0 ≤ lam ℓ) ∧ (S - ∑ ℓ : Fin σ.l, lam ℓ • σ.W ℓ).PosSemidef) := by
  constructor
  · rintro ⟨lam, hlam, hpsd⟩
    have hXi : ∀ᵐ ξ ∂σ.P, ξ ∈ σ.Xi := by
      rw [ae_iff]
      simpa [Set.compl_def] using hσ.2.2.1.2.1
    filter_upwards [hXi] with ξ hξ
    have h1 := hpsd.dotProduct_mulVec_nonneg ξ
    simp only [star_trivial] at h1
    have hexp : ξ ⬝ᵥ ((S - ∑ ℓ : Fin σ.l, lam ℓ • σ.W ℓ) *ᵥ ξ) =
        ξ ⬝ᵥ (S *ᵥ ξ) - ∑ ℓ : Fin σ.l, lam ℓ * (ξ ⬝ᵥ (σ.W ℓ *ᵥ ξ)) := by
      rw [sub_mulVec, dotProduct_sub, sum_mulVec, dotProduct_sum]
      simp only [smul_mulVec, dotProduct_smul, smul_eq_mul]
    have h2 : 0 ≤ ∑ ℓ : Fin σ.l, lam ℓ * (ξ ⬝ᵥ (σ.W ℓ *ᵥ ξ)) :=
      Finset.sum_nonneg (fun ℓ _ => mul_nonneg (hlam ℓ) (hξ.2 ℓ))
    linarith
  · intro hl hae
    have ℓ0 : Fin σ.l := ⟨0, by omega⟩
    have hall : ∀ ℓ : Fin σ.l, ℓ = ℓ0 := fun ℓ => Fin.ext (by have := ℓ.isLt; have := ℓ0.isLt; omega)
    have hsum : ∀ c : ℝ, ∑ ℓ : Fin σ.l, (fun _ => c) ℓ • σ.W ℓ = c • σ.W ℓ0 := by
      intro c
      rw [Finset.sum_eq_single ℓ0 (fun b _ hb => absurd (hall b) hb) (by simp)]
    have hhom := homog σ hσ hl S (on_Xi σ hσ S hae) ℓ0
    have hW := hσ.2.1 ℓ0
    by_cases hsl : ∃ xb : Fin σ.k → ℝ, 0 < xb ⬝ᵥ (σ.W ℓ0 *ᵥ xb)
    · obtain ⟨xb, hxb⟩ := hsl
      have hq : ∀ (M : Matrix (Fin σ.k) (Fin σ.k) ℝ) (x : Fin σ.k → ℝ),
          ConvexOptimization.quadForm (-M) 0 0 x = -(x ⬝ᵥ (M *ᵥ x)) := by
        intro M x
        simp [ConvexOptimization.quadForm, neg_mulVec, dotProduct_neg]
      have hsp := (ConvexOptimization.s_procedure (-σ.W ℓ0) (-S) hW.neg hS.neg 0 0 0 0 xb
        (by rw [hq]; linarith)).mp (by
          intro x hx
          rw [hq] at hx ⊢
          have := hhom x (by linarith)
          linarith)
      obtain ⟨lam, hlam, hpsd⟩ := hsp
      refine ⟨fun _ => lam, fun _ => hlam, ?_⟩
      rw [hsum]
      have hsub := hpsd.submatrix (Sum.inl : Fin σ.k → Fin σ.k ⊕ Unit)
      convert hsub using 1
      ext i j
      simp only [submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, ConvexOptimization.symQuadBlock,
        fromBlocks_apply₁₁, Matrix.neg_apply, smul_eq_mul]
      change S i j - lam * σ.W ℓ0 i j = lam * (-σ.W ℓ0 i j) - (-S i j)
      ring
    · push_neg at hsl
      have hnegW : (-σ.W ℓ0).PosSemidef :=
        psd_of_forall hW.neg (fun x => by
          have := hsl x
          simp only [neg_mulVec, dotProduct_neg]
          linarith)
      have hker : ∀ ξ ∈ σ.Xi, ξ ∈ LinearMap.ker (σ.W ℓ0).mulVecLin := by
        intro ξ hξ
        have h0 : star ξ ⬝ᵥ ((-σ.W ℓ0) *ᵥ ξ) = 0 := by
          have := hξ.2 ℓ0
          have := hsl ξ
          simp only [star_trivial, neg_mulVec, dotProduct_neg]
          linarith
        have := (hnegW.dotProduct_mulVec_zero_iff ξ).mp h0
        rw [LinearMap.mem_ker, mulVecLin_apply]
        rw [neg_mulVec] at this
        exact neg_eq_zero.mp this
      have htop : Submodule.span ℝ σ.Xi ≤ LinearMap.ker (σ.W ℓ0).mulVecLin :=
        Submodule.span_le.mpr hker
      rw [hσ.2.2.2.2.2] at htop
      have hz : ∀ v : Fin σ.k → ℝ, σ.W ℓ0 *ᵥ v = 0 := by
        intro v
        have := htop (Submodule.mem_top (x := v))
        rwa [LinearMap.mem_ker, mulVecLin_apply] at this
      refine ⟨fun _ => 0, fun _ => le_refl 0, ?_⟩
      rw [hsum, zero_smul, sub_zero]
      exact psd_of_forall hS (fun x => hhom x (by rw [hz]; simp))
