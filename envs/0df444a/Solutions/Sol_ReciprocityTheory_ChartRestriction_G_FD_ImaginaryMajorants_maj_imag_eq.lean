-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.ImaginaryMajorants.maj_imag_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:05:22.017802+00:00
-- url     : https://prove2.me/submissions/06fe5101-19f0-4686-ba3d-bf818a9e6b08

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoostLowerBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ImaginaryMajorants
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_ImaginaryMajorants_jp_col
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoostLowerBounds_plane_facts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_col_flow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_flowMat_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermC_jp_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_mulVec_lin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantConjugateTransfer_maj_transfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RankOneBoostIsometries_boost_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RankOneBoostIsometries_boost_isom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RankOneBoostIsometries_boost_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_smul_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.ImaginaryMajorants
open MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries BoostLowerBounds
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.ImaginaryMajorants
theorem _root_.solution {z : Frame X.Ψ r} (hz : z ∈ X.dom) (ξ : Fin r → E) (b : X.Ψ → ℝ)
    (hy : X.flow ξ (fun τ => I * (b τ : ℂ)) z ∈ X.dom) (τ : X.Ψ)
    (hee : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (he0 : Data.emb τ.1 ξ ≠ 0)
    (hq : 0 < 1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)) (w : Fin r → ℂ) :
    X.maj (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ w = X.maj z τ (Matrix.mulVec
      (boost X τ (Data.emb τ.1 ξ) (X.jp z τ (Data.emb τ.1 ξ)) (X.maj z τ (Data.emb τ.1 ξ))
        (Real.sqrt (1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)))⁻¹) w) := by
  set e := Data.emb τ.1 ξ with he_def
  obtain ⟨hm, hff, hef, hfe⟩ := plane_facts X τ hz hee he0
  set f := X.jp z τ e with hf_def
  set m := X.maj z τ e with hm_def
  set q := 1 + X.c τ * b τ * m with hq_def
  set σ := Real.sqrt q with hσ_def
  have hσ : 0 < σ := Real.sqrt_pos.mpr hq
  have hσ2 : σ ^ 2 = q := Real.sq_sqrt hq.le
  set T := X.flowMat ξ τ (I * (b τ : ℂ))
  have hT : ∀ v, Matrix.mulVec T v = v + (((X.c τ * b τ : ℝ) : ℂ) * hermC τ.1 X.Gm v e) • e := by
    intro v
    rw [Data.flowMat_mulVec]
    congr 2
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hcb : X.c τ * b τ = (σ ^ 2 - 1) / m := by
    rw [hσ2, hq_def]; field_simp; ring
  set B := boost X τ e f m σ
  set B' := boost X τ e f m σ⁻¹
  set P := X.ppos z τ e with hP_def
  set γ : Fin X.p0 → ℂ := fun j => ∑ b, hermC τ.1 X.Gm e (X.colP z τ b) * (X.gramPos z τ)⁻¹ b j
  have hPsum : P = ∑ j, γ j • X.colP z τ j := rfl
  have hPef : P = (1 / 2 : ℂ) • (e + f) := by
    funext k
    simp only [hf_def, Data.jp, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, ← hP_def]
    ring
  have hPe : hermC τ.1 X.Gm P e = (m / 2 : ℝ) := by
    rw [hPef, hC_smul_left, hC_add_left, hee, hfe]; push_cast; ring
  have hPf : hermC τ.1 X.Gm P f = (m / 2 : ℝ) := by
    rw [hPef, hC_smul_left, hC_add_left, hef, hff]; push_cast; ring
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hσC : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hcol : ∀ d, Matrix.mulVec T (X.colP z τ d) = X.colP (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ d := by
    intro d
    rw [show X.colP (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ d = col (mat (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ) (Fin.castLE X.p0_le d) from rfl, Data.col_flow]
    rfl
  have hzf : ∀ d, hermC τ.1 X.Gm (X.colP z τ d) f = hermC τ.1 X.Gm (X.colP z τ d) e := by
    intro d; rw [hf_def, ← X.hermC_jp_left hz, jp_col X hz τ d]

  have hi : ∀ d, Matrix.mulVec T (X.colP z τ d) = Matrix.mulVec B (X.colP z τ d) +
      (((σ - 1) : ℂ) * (2 * hermC τ.1 X.Gm (X.colP z τ d) e / m)) • Matrix.mulVec B P := by
    intro d
    rw [hT, boost_mulVec, boost_mulVec, hzf, hPe, hPf, hPef, hcb]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
    ring
  have hii : ∀ d, Matrix.mulVec B (X.colP z τ d) = Matrix.mulVec T (X.colP z τ d) -
      (((1 - σ⁻¹) : ℂ) * (2 * hermC τ.1 X.Gm (X.colP z τ d) e / m)) • Matrix.mulVec T P := by
    intro d
    rw [hT, hT, boost_mulVec, hzf, hPe, hPef, hcb]
    funext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
    ring
  have H2 : ∀ a, ∃ L : Fin X.p0 → ℂ, X.colP (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ a = ∑ c, L c • Matrix.mulVec B (X.colP z τ c) := by
    intro a
    refine ⟨fun j => (if j = a then 1 else 0) +
      ((σ - 1) : ℂ) * (2 * hermC τ.1 X.Gm (X.colP z τ a) e / m) * γ j, ?_⟩
    rw [← hcol, hi, hPsum, Data.mulVec_lin]
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, mul_smul, ← Finset.smul_sum]
  have H1 : ∀ c, ∃ K : Fin X.p0 → ℂ, Matrix.mulVec B (X.colP z τ c) = ∑ a, K a • X.colP (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ a := by
    intro c
    refine ⟨fun j => (if j = c then 1 else 0) -
      ((1 - σ⁻¹) : ℂ) * (2 * hermC τ.1 X.Gm (X.colP z τ c) e / m) * γ j, ?_⟩
    rw [hii, hPsum, Data.mulVec_lin]
    simp only [hcol, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_smul, ← Finset.smul_sum]
  have hmt := maj_transfer X hz hy τ B B' (boost_comp X τ hm hee hff hef hfe hσ)
    (boost_isom X τ hm hee hff hef hfe hσ) H1 H2 w
  exact hmt
end ReciprocityTheory.ChartRestriction.G.FD.ImaginaryMajorants
