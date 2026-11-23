-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_Ji_inUJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:07.387839+00:00
-- url     : https://prove2.me/submissions/3a3733a7-4539-4565-8a25-4763754e6a64

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_JJ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_mul_Ji
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
namespace ReciprocityTheory.ChartRestriction.DS
section Mat
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {k : WithTop ℕ∞}
end Mat
section Ret
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
local notation "JJ" => Formalism.REAL.Jm
private lemma Jm_conjTranspose_eq_Jm (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]
end Ret
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
local notation "JJ" => Formalism.REAL.Jm
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.inUJ ε (slmJi ε g) := by
  have h1 : g * (Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε)) = 1 := by
    have := slm_mul_Ji hg
    unfold slmJi at this
    simpa only [Matrix.mul_assoc] using this
  unfold Formalism.REAL.inUJ slmJi
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose_eq_Jm, Matrix.mul_assoc,
    slm_JJ, h1, Matrix.mul_one]
end ReciprocityTheory.ChartRestriction.DS
