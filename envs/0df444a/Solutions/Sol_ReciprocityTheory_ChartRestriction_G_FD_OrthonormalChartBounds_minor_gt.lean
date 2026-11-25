-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.minor_gt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:31:11.258119+00:00
-- url     : https://prove2.me/submissions/1e1eaadc-cd20-495f-a3eb-2e171f7064b0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosDefOfBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_bound_castLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_psgn_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_signType_cancel_identity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_pos_re_of_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_Gp_nn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_Gp_np
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_Gp_pn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_Gp_pp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_gram_xZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_posDef_of_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
theorem _root_.solution {x : Frame X.Ψ r} (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1) (τ : X.Ψ)
    (k : ℕ) (hk : k ≤ r - X.p0) (i : Fin (r + 1)) (hik : (i : ℕ) = X.p0 + k) :
    0 < psgn X.p0 i * (dmin X.Gm (X.xZ x Z) τ i).re := by
  classical
  obtain ⟨i, hi⟩ := i
  simp only at hik
  subst hik
  rw [show ((⟨X.p0 + k, hi⟩ : Fin (r + 1)) : ℕ) = X.p0 + k from rfl, psgn_add]
  set A : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ :=
    Matrix.of fun m b => Z τ m (Fin.castLE (le_refl X.p0) b) with hA
  set B : Matrix (Fin k) (Fin X.p0) ℂ := Matrix.of fun m c => Z τ (Fin.castLE hk m) c with hB
  have hs0 : 0 ≤ X.zN Z := by
    unfold Data.zN
    apply Real.iSup_nonneg
    intro τ'
    unfold Data.opN
    apply Real.sSup_nonneg
    rintro t ⟨v, -, rfl⟩
    positivity
  have hpd := posDef_of_bound A B hZ (bound_castLE X (le_refl X.p0) Z τ) hs0
  haveI : Invertible (1 : Matrix (Fin k) (Fin k) ℂ) := invertibleOne
  haveI : Invertible (-1 : Matrix (Fin k) (Fin k) ℂ) := invertibleNeg 1
  have heq : dmin X.Gm (X.xZ x Z) τ ⟨X.p0 + k, hi⟩ =
      (-1 : ℂ) ^ k * (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).det := by
    unfold dmin lminor
    rw [gram_xZ X ho Z τ, ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
    have hc1 : ∀ a : Fin X.p0, (Fin.castLE (Nat.le_of_lt_succ hi) (finSumFinEquiv (Sum.inl a)) : Fin r) =
        Fin.castLE X.p0_le a := fun a => Fin.ext (by simp)
    have hc2 : ∀ m : Fin k, (Fin.castLE (Nat.le_of_lt_succ hi) (finSumFinEquiv (Sum.inr m)) : Fin r) =
        nI X (Fin.castLE hk m) := fun m => Fin.ext (by simp [nI])
    have hblk : ((Gp X Z τ).submatrix (Fin.castLE (Nat.le_of_lt_succ hi)) (Fin.castLE (Nat.le_of_lt_succ hi))).submatrix
        finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks (1 - Aᵀ * A.map (starRingEnd ℂ)) (-Bᵀ) (-(B.map (starRingEnd ℂ))) (-1) := by
      ext (a | m) (b | m')
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc1, Gp_pp, Matrix.fromBlocks_apply₁₁]
        simp [hA, Matrix.one_apply, Matrix.mul_apply]
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc1, hc2, Gp_pn, Matrix.fromBlocks_apply₁₂]
        simp [hB]
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc1, hc2, Gp_np, Matrix.fromBlocks_apply₂₁]
        simp [hB]
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc2, Gp_nn, Matrix.fromBlocks_apply₂₂]
        simp [Matrix.one_apply, Fin.castLE_inj]
    rw [hblk, Matrix.det_fromBlocks₂₂, invOf_neg, invOf_one, Matrix.det_neg, Matrix.det_one, Fintype.card_fin,
      mul_one]
    congr 2
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg, sub_neg_eq_add]
  rw [heq]
  exact signType_cancel_identity k _ (pos_re_of_posDef hpd)
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
