-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.addition_linear_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:32:38.568344+00:00
-- url     : https://prove2.me/submissions/3bdbe1d5-c671-4d9a-b120-fcb18492ce25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_pt
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_add__bceb3bffa58a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_scale_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution : AddLinFstSt := by
  intro k _ _ d f hf n hn
  let b : Fin 3 → Pt k 2 d := ![pt k d 0, pt k d 0, pt k d 1]
  have hb0 : ∀ j i, constantCoeff (b j i) = 0 := fun j i => by
    fin_cases j <;> simp [b, pt]
  have hA : ev b (ev (n := 3) ![pt k d 0 + pt k d 1, pt k d 2] f)
      = ev (![fun i => (2 : k) ^ 1 • (X ((0 : Fin 2), i) : PS k 2 d),
        fun i => (2 : k) ^ 0 • (X ((1 : Fin 2), i) : PS k 2 d)] : Fin 2 → Pt k 2 d) f := by
    rw [ev_ev _ _ (fun j i => by fin_cases j <;> simp [pt]) hb0]
    congr 1
    funext j i
    fin_cases j <;> simp [b, pt, ev_add' b hb0, ev_X b hb0, two_smul]
  have hB : ∀ c : Fin 3, c ≠ 2 → ev b (ev (n := 3) ![pt k d c, pt k d 2] f) = f := by
    intro c hc
    calc ev b (ev (n := 3) ![pt k d c, pt k d 2] f) = ev (fun j => pt k d j) f := by
          rw [ev_ev _ _ (fun j i => by fin_cases j <;> simp [pt]) hb0]
          congr 1
          funext j i
          fin_cases c <;> fin_cases j <;> simp_all [b, pt, ev_X b hb0]
      _ = f := ev_pt f
  have h1 := congrArg (ev b) hf
  rw [ev_add' b hb0, hA, hB 0 (by decide), hB 1 (by decide)] at h1
  refine scale_two f 1 0 ?_ n ?_
  · rw [two_smul]
    exact h1
  · simpa using hn
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
