-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.minor_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:31:15.949084+00:00
-- url     : https://prove2.me/submissions/320d3e5e-351f-4110-ab83-68f959ed2bce

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosDefOfBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_bound_castLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_pos_re_of_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_Gp_pp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_gram_xZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_posDef_of_bound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_psgn_eq_one


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
    (i : Fin (r + 1)) (hip : (i : ℕ) ≤ X.p0) : 0 < psgn X.p0 i * (dmin X.Gm (X.xZ x Z) τ i).re := by
  classical
  rw [psgn_eq_one hip, one_mul]
  set A : Matrix (Fin (r - X.p0)) (Fin (i : ℕ)) ℂ :=
    Matrix.of fun m b => Z τ m (Fin.castLE hip b) with hA
  set B : Matrix (Fin 0) (Fin (i : ℕ)) ℂ := 0 with hB
  have hs0 : 0 ≤ X.zN Z := by
    unfold Data.zN
    apply Real.iSup_nonneg
    intro τ'
    unfold Data.opN
    apply Real.sSup_nonneg
    rintro t ⟨v, -, rfl⟩
    positivity
  have hpd := posDef_of_bound A B hZ (bound_castLE X hip Z τ) hs0
  have heq : dmin X.Gm (X.xZ x Z) τ i = (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).det := by
    unfold dmin lminor
    rw [gram_xZ X ho Z τ]
    congr 1
    ext a b
    have hca : (Fin.castLE (Nat.le_of_lt_succ i.isLt) a : Fin r) = Fin.castLE X.p0_le (Fin.castLE hip a) :=
      Fin.ext rfl
    have hcb : (Fin.castLE (Nat.le_of_lt_succ i.isLt) b : Fin r) = Fin.castLE X.p0_le (Fin.castLE hip b) :=
      Fin.ext rfl
    rw [Matrix.submatrix_apply, hca, hcb, Gp_pp]
    simp [hA, hB, Matrix.one_apply, Matrix.mul_apply, Fin.castLE_inj]
  rw [heq]
  exact pos_re_of_posDef hpd
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
