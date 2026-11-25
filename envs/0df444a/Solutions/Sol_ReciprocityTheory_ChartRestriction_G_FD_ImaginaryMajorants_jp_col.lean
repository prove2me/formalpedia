-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.ImaginaryMajorants.jp_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:56:50.746545+00:00
-- url     : https://prove2.me/submissions/2f5ec82f-ea7c-4d43-9e31-bd130906d92e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoostLowerBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ImaginaryMajorants
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_det_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_eq_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_zero_left


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
theorem _root_.solution {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (d : Fin X.p0) :
    X.jp z τ (X.colP z τ d) = X.colP z τ d := by
  have hP : X.ppos z τ (X.colP z τ d) = X.colP z τ d := by
    have h := X.ppos_eq_of z τ (X.gramPos_det_ne hz τ) (X.colP z τ d)
      (fun a => if a = d then 1 else 0) (fun b => by
        rw [show (∑ a, (if a = d then (1 : ℂ) else 0) • col (mat z τ) (Fin.castLE X.p0_le a)) =
          X.colP z τ d by simp [Data.colP]]
        rw [sub_self, hermC_zero_left])
    rw [h]
    simp [Data.colP]
  simp only [Data.jp, hP]
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.ImaginaryMajorants
