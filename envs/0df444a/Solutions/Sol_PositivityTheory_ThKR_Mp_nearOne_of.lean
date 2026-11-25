-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.nearOne_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:59:06.346482+00:00
-- url     : https://prove2.me/submissions/2c10f4f8-b352-4096-a454-d53cea4f85b4

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticGroupT2Space
import Theorems.Thm_PositivityTheory_ThKR_Mp_MpE_eventually_det_pos_G
import Theorems.Thm_PositivityTheory_ThKR_Mp_MpE_tendsto_sec
import Theorems.Thm_PositivityTheory_ThKR_Mp_MpE_exists_sch_ne
import Theorems.Thm_PositivityTheory_ThKR_Mp_continuous_om
import Theorems.Thm_PositivityTheory_ThKR_Mp_continuous_pr
import Theorems.Thm_PositivityTheory_ThKR_Mp_om_sch


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real ContDiff
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open MpE
namespace PositivityTheory.ThKR.Mp
theorem _root_.solution (hS : SecEx l) (hK : Ker l) (hD : SecDer l) : NearOne l := by
  obtain ⟨ε, -, hker, hεom⟩ := hK
  obtain ⟨f, hf⟩ := exists_sch_ne (l := l)
  have hv : 0 < ‖schwartzToL2 l f‖ := norm_pos_iff.2 hf
  have hom : ∀ᶠ g in 𝓝 (1 : G l), ‖om g (schwartzToL2 l f) - schwartzToL2 l f‖ < ‖schwartzToL2 l f‖ := by
    have h := (continuous_om (schwartzToL2 l f)).tendsto (1 : G l)
    rw [map_one] at h
    exact (tendsto_iff_norm_sub_tendsto_zero.1 h).eventually (gt_mem_nhds hv)
  have hsec : ∀ᶠ g in 𝓝 (1 : G l), ‖schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f‖ < ‖schwartzToL2 l f‖ := by
    have h := continuous_pr.tendsto (1 : G l)
    rw [map_one] at h
    exact (tendsto_iff_norm_sub_tendsto_zero.1 ((tendsto_sec hD f).comp h)).eventually (gt_mem_nhds hv)
  filter_upwards [eventually_det_pos_G, hom, hsec] with g h1 h2 h3
  obtain ⟨g', c, hg', hU, hc⟩ := hS (pr g) h1.ne'
  rw [hc h1, one_smul] at hU
  have hk : pr (g * g'⁻¹) = 1 := by rw [map_mul, map_inv, hg', mul_inv_cancel]
  rcases (hker _).1 hk with h | h
  · rw [mul_inv_eq_one.1 h, hU, hg']
  · exfalso
    have hg : g = ε * g' := mul_inv_eq_iff_eq_mul.1 h
    have e1 : om g = om ε * om g' := by rw [hg, map_mul]
    have e : om g (schwartzToL2 l f) = -schwartzToL2 l (sec (pr g).1 f) := by
      rw [e1]
      show om ε (om g' (schwartzToL2 l f)) = _
      rw [hεom, om_sch, hU]
    rw [e] at h2
    have h4 : ‖schwartzToL2 l f + schwartzToL2 l f‖ ≤
        ‖schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f‖ + ‖-schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f‖ := by
      have := norm_add_le (schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f) (-schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f)
      have e2 : schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f + (-schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f) =
          -(schwartzToL2 l f + schwartzToL2 l f) := by abel
      rwa [e2, norm_neg] at this
    have h5 : ‖schwartzToL2 l f + schwartzToL2 l f‖ = 2 * ‖schwartzToL2 l f‖ := by
      rw [← two_smul ℂ (schwartzToL2 l f), norm_smul]
      norm_num
    linarith
end PositivityTheory.ThKR.Mp
