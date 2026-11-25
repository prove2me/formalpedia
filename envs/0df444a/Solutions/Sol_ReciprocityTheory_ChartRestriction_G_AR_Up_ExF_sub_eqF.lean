-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.sub_eqF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:25:11.989225+00:00
-- url     : https://prove2.me/submissions/6f044a55-e02b-4879-add5-83a8fdea78b7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_rhF_eq_log
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_mem_OmF_iff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ComplexConjugate ComplexOrder ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private theorem det_one_sub_mul_conjTranspose_mem_Icc {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) (h : (1 - Z * Zᴴ).PosSemidef) :
    0 ≤ (1 - Z * Zᴴ).det.re ∧ (1 - Z * Zᴴ).det.re ≤ 1 ∧ ‖(1 - Z * Zᴴ).det‖ = (1 - Z * Zᴴ).det.re := by
  have hH : (1 - Z * Zᴴ).IsHermitian := h.isHermitian
  have hev : ∀ i, 0 ≤ hH.eigenvalues i ∧ hH.eigenvalues i ≤ 1 := by
    intro i
    refine ⟨h.eigenvalues_nonneg i, ?_⟩
    rw [hH.eigenvalues_eq i]
    set v := (hH.eigenvectorBasis i).ofLp with hvdef
    have hv : star v ⬝ᵥ v = 1 := by
      have h1 : ‖hH.eigenvectorBasis i‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h1
      simp only [dotProduct, Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
      rw [hvdef]
      have h2 := congrArg (fun t : ℝ => (t : ℂ)) h1
      push_cast at h2
      exact h2
    have hq : 0 ≤ star v ⬝ᵥ (Z * Zᴴ) *ᵥ v := (posSemidef_self_mul_conjTranspose Z).dotProduct_mulVec_nonneg v
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hv, map_sub, RCLike.one_re]
    have := (RCLike.nonneg_iff.1 hq).1
    linarith
  have hd : (1 - Z * Zᴴ).det = ((∏ i, hH.eigenvalues i : ℝ) : ℂ) := by
    rw [hH.det_eq_prod_eigenvalues]
    push_cast
    rfl
  have h0 : 0 ≤ ∏ i, hH.eigenvalues i := Finset.prod_nonneg fun i _ => (hev i).1
  rw [hd, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg h0]
  exact ⟨h0, Finset.prod_le_one (fun i _ => (hev i).1) fun i _ => (hev i).2, rfl⟩
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ComplexConjugate ComplexOrder ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
theorem _root_.solution (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (a : ℝ) :
    {z : V (nd X) | z ∈ OmF X x0 ∧ eF X x0 z ≤ a} =
      {z | (∀ τ, (Am X z τ).PosSemidef) ∧
        Real.exp (Real.log (1 + ‖z‖ ^ 2) - a) ≤ ∏ τ, (Am X z τ).det.re} := by
  ext z
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz, hle⟩
    have hpd := (mem_OmF_iff X x0 ho z).1 hz
    refine ⟨fun τ => (hpd τ).posSemidef, ?_⟩
    have hpos : ∀ τ, 0 < (Am X z τ).det.re := fun τ => by
      have h := Complex.lt_def.1 (hpd τ).det_pos
      simp only [Complex.zero_re] at h
      exact h.1
    unfold eF at hle
    rw [rhF_eq_log X x0 ho hz] at hle
    have hP : 0 < ∏ τ, (Am X z τ).det.re := Finset.prod_pos fun τ _ => hpos τ
    rw [← Real.exp_log hP]
    exact Real.exp_le_exp.2 (by linarith)
  · rintro ⟨hpsd, hle⟩
    have hP : 0 < ∏ τ, (Am X z τ).det.re := lt_of_lt_of_le (Real.exp_pos _) hle
    have hpos : ∀ τ, 0 < (Am X z τ).det.re := by
      intro τ
      obtain ⟨h0, -, -⟩ : 0 ≤ (Am X z τ).det.re ∧ (Am X z τ).det.re ≤ 1 ∧
          ‖(Am X z τ).det‖ = (Am X z τ).det.re := det_one_sub_mul_conjTranspose_mem_Icc (Zt X z τ) (hpsd τ)
      rcases h0.eq_or_lt with h0 | h0
      · exact absurd hP (by rw [Finset.prod_eq_zero (Finset.mem_univ τ) h0.symm]; exact lt_irrefl 0)
      · exact h0
    have hz : z ∈ OmF X x0 := (mem_OmF_iff X x0 ho z).2 fun τ => ((hpsd τ).posDef_iff_isUnit).2
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 fun h => by
        have := hpos τ
        rw [h, Complex.zero_re] at this
        exact lt_irrefl 0 this))
    refine ⟨hz, ?_⟩
    unfold eF
    rw [rhF_eq_log X x0 ho hz]
    have := Real.log_le_log (Real.exp_pos _) hle
    rw [Real.log_exp] at this
    linarith
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
