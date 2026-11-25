-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries.boost_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:26:38.042319+00:00
-- url     : https://prove2.me/submissions/0e852c13-52e3-42d7-af01-717c85923f21

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatrixMajorants
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RankOneBoostIsometries
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RankOneBoostIsometries_boost_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right


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
variable {e f : Fin r → ℂ} {m : ℝ} (hm : 0 < m) (hee : hermC τ.1 X.Gm e e = 0)
  (hff : hermC τ.1 X.Gm f f = 0) (hef : hermC τ.1 X.Gm e f = m) (hfe : hermC τ.1 X.Gm f e = m)
include hm hee hff hef hfe
namespace ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries
theorem _root_.solution {σ : ℝ} (hσ : 0 < σ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (Matrix.mulVec (boost X τ e f m σ) u) (Matrix.mulVec (boost X τ e f m σ) v) =
      hermC τ.1 X.Gm u v := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  rw [boost_mulVec, boost_mulVec]
  simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC_add_left, ReciprocityTheory.ChartRestriction.G.FD.hermC_add_right, ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left,
    ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_right, hee, hff, hef, hfe, map_mul, Complex.conj_ofReal]
  rw [← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ.1 X.Gm_herm v e, ← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ.1 X.Gm_herm v f]
  push_cast
  field_simp
  ring
end ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries
