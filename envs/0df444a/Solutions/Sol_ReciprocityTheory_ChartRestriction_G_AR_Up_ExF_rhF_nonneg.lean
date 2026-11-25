-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.rhF_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:34:54.237817+00:00
-- url     : https://prove2.me/submissions/d7ab189b-ee20-47d5-9e19-d46ebd5ae82f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_mem_OmF_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_rhF_eq_sum
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
theorem _root_.solution (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) : 0 ≤ rhF X x0 z := by
  rw [rhF_eq_sum X x0 ho z, neg_nonneg]
  refine Finset.sum_nonpos fun τ _ => Real.log_nonpos (norm_nonneg _) ?_
  obtain ⟨h0, h1, h2⟩ : 0 ≤ (Am X z τ).det.re ∧ (Am X z τ).det.re ≤ 1 ∧ ‖(Am X z τ).det‖ = (Am X z τ).det.re :=
    det_one_sub_mul_conjTranspose_mem_Icc (Zt X z τ) ((mem_OmF_iff X x0 ho z).1 hz τ).posSemidef
  rw [h2]
  exact h1
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
