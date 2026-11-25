-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cut_norm_d_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:54.572863+00:00
-- url     : https://prove2.me/submissions/eedb8adb-4314-4a80-b3ab-2a2d26b2736b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
private lemma norm_wd_ofReal_eq_norm_wdb_ofReal (n : ℕ) (j : Fin n) (h : V n → ℝ) (y : V n) :
    ‖wd n j (fun y => (h y : ℂ)) y‖ = ‖wdb n j (fun y => (h y : ℂ)) y‖ := by
  have key : ∀ v : V n, (starRingEnd ℂ) (fderiv ℝ (fun y => (h y : ℂ)) y v) =
      fderiv ℝ (fun y => (h y : ℂ)) y v := by
    intro v
    have hf : (fun y => (h y : ℂ)) = Complex.conjCLE ∘ (fun y => (h y : ℂ)) := by
      funext w
      simp
    conv_rhs => rw [hf]
    rw [ContinuousLinearEquiv.comp_fderiv]
    simp
  unfold wd wdb
  rw [← Complex.norm_conj]
  congr 1
  simp only [map_div₀, map_sub, map_add, map_mul, key, Complex.conj_I, map_ofNat]
  ring
end
end ReciprocityTheory.L2DbarEstimates.F
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (η : M → ℝ) (x : M) :
    ‖d n z j (fun y => (η y : ℂ)) x‖ = ‖db n z j (fun y => (η y : ℂ)) x‖ := by
  unfold d db
  split_ifs with hc
  · exact norm_wd_ofReal_eq_norm_wdb_ofReal n j (η ∘ (Classical.choose hc).symm) (z x)
  · rfl
end ReciprocityTheory.L2DbarEstimates.F
