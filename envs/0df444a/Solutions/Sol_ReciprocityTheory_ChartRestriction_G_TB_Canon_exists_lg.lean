-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.Canon.exists_lg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:54:52.018455+00:00
-- url     : https://prove2.me/submissions/d854b234-b0af-4347-b18f-ce595c1bfd47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_constantCoeff_logS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_log
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_expS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.Canon
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d n l : ℕ}
variable [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.Canon
theorem _root_.solution {m : ℕ} (f : PS k m d) (hf : constantCoeff f = 1) : ∃ g : PS k m d, FB.expS k g = f ∧
    ∀ {n} (a : Fin m → Q k d n), constantCoeff (sb a g) = 0 ∧ FB.expS k (sb a g) = sb a f :=
  ⟨_, WickVanishing.exp_log hf, fun a => ⟨by rw [sb_apply]; exact constantCoeff_ev (czQ a) (WickVanishing.constantCoeff_logS hf), by
    rw [sb_apply, sb_apply, ← WickVanishing.gt_ev_expS _ (fun j => (a j).2) _ (WickVanishing.constantCoeff_logS hf)]
    exact congrArg _ (WickVanishing.exp_log hf)⟩⟩
end ReciprocityTheory.ChartRestriction.G.TB.Canon
