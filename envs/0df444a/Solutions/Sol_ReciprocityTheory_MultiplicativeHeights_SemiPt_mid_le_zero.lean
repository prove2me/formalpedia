-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.mid_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:52:21.536418+00:00
-- url     : https://prove2.me/submissions/63abf630-a764-4e0b-97b5-901f169cb0f6

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegM
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegN
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_colMat_mulVec
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_form_colMat
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_gramC_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_gramC_posDef
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_hGram_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_hermForm_swap
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_quad_diag
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_quad_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_spanIdx_ne_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_sum_log_norm_emb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution (hN : IntegralIndexStatement) (hA : AbsDetStatement) {K : Type} [Field K]
    [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ) (g : Fin r → K)
    (hfix : ∀ a : Fin r, m ≤ (a : ℕ) → (a : ℕ) + m < r → S.c (g a) = g a)
    (Gm : Submodule (𝓞 K) (Fin r → K)) (hGm : Gm.FG)
    (hsupp : ∀ x ∈ Gm, ∀ a : Fin r, ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) → x a = 0)
    (hint : IsIntegralOn (midForm S m g hfix) Gm)
    (haniso : ∀ t : Fin r → K, (∀ i : Fin r, (i : ℕ) < m ∨ r ≤ (i : ℕ) + m → t i = 0) →
      ∑ i, S.c (t i) * g i * t i = 0 → t = 0)
    (δ : (K →+* ℂ) → Fin r → ℝ) (hδ : ∀ σ a, 0 < δ σ a)
    (hδmid : ∀ σ (a : Fin r), m ≤ (a : ℕ) → (a : ℕ) + m < r → δ σ a = ‖σ (g a)‖)
    (C : Submodule (𝓞 K) (Fin r → K)) (hC : C ≤ Gm) (k : ℕ) (c : Fin k → Fin r → K)
    (hc : IsKBasisIn C c) : latDeg (diagMet δ) C c ≤ 0 := by
  set Sm := midForm S m g hfix with hSm
  have hCfg : C.FG := Submodule.FG.of_le hGm hC
  have hCint : IsIntegralOn Sm C := fun x hx y hy => hint x (hC hx) y (hC hy)

  have hSmh : ∀ z : Fin r → K, (∀ a : Fin r, ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) → z a = 0) →
      Sm.h z z = ∑ a, S.c (z a) * g a * z a := by
    intro z hz
    simp only [HermForm.h, hSm, midForm, midG, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h
    · rfl
    · rw [hz a (by omega)]
      simp
  have hdet : (hGram Sm c).det ≠ 0 := by
    intro h0
    obtain ⟨t, ht0, ht⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    set z := colMat c *ᵥ t with hz
    have hzsupp : ∀ a : Fin r, ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) → z a = 0 := by
      intro a ha
      rw [hz, colMat_mulVec, Finset.sum_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Pi.smul_apply, hsupp _ (hC (hc.1 j)) a ha, smul_zero]
    have h1 : Sm.h z z = 0 := by
      rw [hz, ← form_colMat, ht]
      simp
    rw [hSmh z hzsupp] at h1
    have h2 := haniso z hzsupp h1
    rw [hz, colMat_mulVec] at h2
    exact ht0 (funext (Fintype.linearIndependent_iff.1 hc.2.1 t h2))
  have hidx := hN K r k Sm C c hCfg hc hCint hdet
  have hDpd : ∀ σ, (diagMet δ σ).PosDef := fun σ =>
    Matrix.posDef_diagonal_iff.2 fun a => by exact_mod_cast hδ σ a

  have hσ : ∀ σ : K →+* ℂ, ‖σ (hGram Sm c).det‖ ≤ (gramC (diagMet δ σ) σ c).det.re := by
    intro σ
    set E := embMat σ c with hE
    have hEc : ((colMat c).map S.c)ᵀ.map σ = Eᴴ := by
      ext a b
      simp [hE, embMat, colMat, Matrix.conjTranspose_apply, S.c_emb]
    have hC' : (hGram Sm c).map σ = Eᴴ * (midG r m g).map σ * E := by
      rw [hGram_eq, Matrix.map_mul, Matrix.map_mul]
      simp only [hSm, midForm]
      rw [hEc]
      rfl
    have hGσ : (midG r m g).map σ =
        diagonal fun a : Fin r => σ (if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then g a else 0) := by
      simp only [midG]
      rw [Matrix.diagonal_map (map_zero σ)]
    have hherm : ((hGram Sm c).map σ).IsHermitian := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply, hGram, Matrix.of_apply]
      rw [← hermForm_swap Sm (c j) (c i), Sm.c_emb]
      rfl
    have hineq : ∀ v : Fin k → ℂ, ‖star v ⬝ᵥ (((hGram Sm c).map σ) *ᵥ v)‖ ≤
        (star v ⬝ᵥ ((gramC (diagMet δ σ) σ c) *ᵥ v)).re := by
      intro v
      rw [hC', gramC_eq, quad_eq, quad_eq, hGσ]
      simp only [diagMet]
      rw [quad_diag, quad_diag]
      calc ‖∑ a : Fin r, σ (if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then g a else 0) *
              ((‖(E *ᵥ v) a‖ ^ 2 : ℝ) : ℂ)‖
          ≤ ∑ a : Fin r, ‖σ (if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then g a else 0) *
              ((‖(E *ᵥ v) a‖ ^ 2 : ℝ) : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ a : Fin r, δ σ a * ‖(E *ᵥ v) a‖ ^ 2 := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            gcongr
            split_ifs with h
            · rw [hδmid σ a h.1 h.2]
            · simp only [map_zero, norm_zero]
              exact (hδ σ a).le
        _ = (∑ a : Fin r, ((δ σ a : ℝ) : ℂ) * ((‖(E *ᵥ v) a‖ ^ 2 : ℝ) : ℂ)).re := by
            rw [Complex.re_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Complex.ofReal_mul, Complex.ofReal_re]
    have h5 := hA k (gramC (diagMet δ σ) σ c) ((hGram Sm c).map σ)
      (gramC_posDef S _ (hDpd σ) σ c hc.2.1) hherm hineq
    rwa [show ((hGram Sm c).map σ).det = σ (hGram Sm c).det from (RingHom.map_det σ _).symm] at h5
  have hN0 : 0 < |((Algebra.norm ℚ (hGram Sm c).det : ℚ) : ℝ)| := by
    apply abs_pos.2
    exact_mod_cast (Algebra.norm_ne_zero_iff).2 hdet
  have hsum : Real.log |((Algebra.norm ℚ (hGram Sm c).det : ℚ) : ℝ)| ≤
      ∑ σ : K →+* ℂ, Real.log (gramC (diagMet δ σ) σ c).det.re := by
    rw [← sum_log_norm_emb]
    refine Finset.sum_le_sum fun σ _ => Real.log_le_log ?_ (hσ σ)
    apply norm_pos_iff.2
    intro h0
    exact hdet (σ.injective (by rw [h0, map_zero]))
  have hone : 1 ≤ (spanIdx C c : ℝ) :=
    Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 (spanIdx_ne_zero C c hCfg hc))
  have hidx' : 2 * Real.log (spanIdx C c : ℝ) ≤ Real.log |((Algebra.norm ℚ (hGram Sm c).det : ℚ) : ℝ)| := by
    have := Real.log_le_log (by positivity) hidx
    rwa [Real.log_pow] at this
  unfold latDeg
  unfold spanIdx at hidx'
  linarith
end ReciprocityTheory.MultiplicativeHeights.SemiPt
