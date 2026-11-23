-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_inUJ_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:27.703802+00:00
-- url     : https://prove2.me/submissions/044afa3d-bb6a-48a1-be22-9db7a39d6262

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
local notation "JJ" => Formalism.REAL.Jm
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {a b : Matrix (Fin n) (Fin n) ℂ} (ha : Formalism.REAL.inUJ ε a)
    (hb : Formalism.REAL.inUJ ε b) : Formalism.REAL.inUJ ε (a * b) := by
  unfold Formalism.REAL.inUJ at ha hb ⊢
  calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha, hb]
end ReciprocityTheory.ChartRestriction.DS
