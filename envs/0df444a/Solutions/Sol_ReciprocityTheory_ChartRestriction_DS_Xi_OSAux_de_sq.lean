-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.de_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:27:33.686265+00:00
-- url     : https://prove2.me/submissions/7f6fb3d5-d648-40c9-a533-031aab1bfa89

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_Lsq_ge_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_rhoSq_ge
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_bco_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) :
    de x l ^ 2 = (Lsq x l * rhoSq x l + (-(∑ i, ‖x.2.2.1 i‖ ^ 2) / 2 - (bS x l).re) ^ 2) +
      (x.2.2.2 - (bS x l).im) ^ 2 := by
  have hL := Lsq_ge_one x l
  have hR : 1 ≤ ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq x l := le_trans hL (rhoSq_ge x l l)
  have hpos : 0 ≤ ReciprocityTheory.ChartRestriction.DS.Xi.Lsq x l * ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq x l + ‖ReciprocityTheory.ChartRestriction.DS.Xi.bco x l‖ ^ 2 :=
    add_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  have hre : (ReciprocityTheory.ChartRestriction.DS.Xi.bco x l).re = -(∑ i, ‖x.2.2.1 i‖ ^ 2) / 2 - (bS x l).re := by
    rw [bco_eq]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him : (ReciprocityTheory.ChartRestriction.DS.Xi.bco x l).im = x.2.2.2 - (bS x l).im := by
    rw [bco_eq]
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.de
  rw [Real.sq_sqrt hpos, Complex.sq_norm, Complex.normSq_apply, hre, him]
  ring
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
