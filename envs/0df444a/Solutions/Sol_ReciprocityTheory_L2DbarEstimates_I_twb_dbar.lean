-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.twb_dbar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:26:33.835009+00:00
-- url     : https://prove2.me/submissions/1e42d183-eb5d-4333-bbb4-b33caf1b166d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwBound
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_cexp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_db_eq_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_cexp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_ck
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_cexp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_const_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (F0 F : M → ℂ)
    (Ph : M → ℝ) (hF0 : Smooth n z F0) (hF : Holo n z F) (hPh : SmoothR n z Ph) (x : M)
    (ξ : Fin n → ℂ) :
    dbarDot n z (fun y => (F0 y - F y) * Complex.exp (Ph y)) x ξ =
      Complex.exp (Ph x) * (dbarDot n z F0 x ξ +
        (F0 x - F x) * dbarDot n z (fun y => (Ph y : ℂ)) x ξ) := by
  have hF0' : Ck n z 1 F0 := Smooth.ck n z 1 F0 hF0
  have hF' : Ck n z 1 F := Smooth.ck n z 1 F (Holo.smooth n z F hF)
  have hPh' : Ck n z 1 (fun y => (Ph y : ℂ)) := Smooth.ck n z 1 _ hPh
  have hsub : Ck n z 1 (fun y => F0 y - F y) := Ck.sub n z 1 F0 F hF0' hF'
  have hexp : Ck n z 1 (fun y => Complex.exp (Ph y : ℂ)) := Ck.cexp n z 1 _ hPh'
  have hdsub : ∀ j, db n z j (fun y => F0 y - F y) x = db n z j F0 x := by
    intro j
    have e1 : (fun y => F0 y - F y) = fun y => F0 y + (-1 : ℂ) * F y := by funext y; ring
    rw [e1, db_add n z _ _ hF0' (Ck.mul n z 1 _ _ (Ck.const n z 1 (-1)) hF') j x,
      db_const_mul n z (-1) F hF' j x, Holo.db_eq_zero n z F hF j x]
    ring
  have hterm : ∀ j, db n z j (fun y => (F0 y - F y) * Complex.exp (Ph y : ℂ)) x =
      Complex.exp (Ph x) * (db n z j F0 x + (F0 x - F x) * db n z j (fun y => (Ph y : ℂ)) x) := by
    intro j
    rw [db_mul n z (fun y => F0 y - F y) (fun y => Complex.exp (Ph y : ℂ)) hsub hexp j x, hdsub j,
      db_cexp n z _ hPh' j x]
    ring
  simp only [dbarDot, hterm, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring
end ReciprocityTheory.L2DbarEstimates.I
