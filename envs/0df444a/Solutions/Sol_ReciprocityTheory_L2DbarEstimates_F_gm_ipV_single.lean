-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.gm_ipV_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:35:25.422276+00:00
-- url     : https://prove2.me/submissions/e400000e-525f-473e-83a8-d4755fcb9ac7

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_GmSingleIsTestForm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (z : M → V n) (ph : M → ℝ) (F0 φ : M → ℂ) (j : Fin n) :
    ipV n z (dbarF n z F0) (gmSingle ph φ j) ph = conj (∫ x, db n z j F0 x * φ x ∂vol n z) := by
  simp only [ipV, dbarF, gmSingle, EuclideanSpace.inner_single_right]
  rw [← integral_conj]
  congr 1
  funext x
  have hE : (Real.exp (ph x) : ℂ) * (Real.exp (-ph x) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  first
    | (simp only [PiLp.toLp_apply, map_mul]
       linear_combination (conj (db n z j F0 x) * conj (φ x)) * hE)
    | (simp only [map_mul]
       linear_combination (conj (db n z j F0 x) * conj (φ x)) * hE)
end ReciprocityTheory.L2DbarEstimates.F
