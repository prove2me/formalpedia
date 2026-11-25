-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries.boost_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:13:03.553786+00:00
-- url     : https://prove2.me/submissions/d0d35afe-09ce-4539-90f8-ea1176f706f2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatrixMajorants
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RankOneBoostIsometries
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RankOneBoostIsometries_rk_mulVec

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
open ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries
open MajorantConjugateTransfer FlowMatrixMajorants
variable {r : ℕ} (X : Data E r) (τ : X.Ψ)
namespace ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries
theorem _root_.solution (e f : Fin r → ℂ) (m σ : ℝ) (v : Fin r → ℂ) :
    Matrix.mulVec (boost X τ e f m σ) v =
      v + ((((σ - 1) / m : ℝ) : ℂ) * hermC τ.1 X.Gm v f) • e +
        ((((σ⁻¹ - 1) / m : ℝ) : ℂ) * hermC τ.1 X.Gm v e) • f := by
  simp only [boost, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, rk_mulVec,
    smul_smul]
end ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries
