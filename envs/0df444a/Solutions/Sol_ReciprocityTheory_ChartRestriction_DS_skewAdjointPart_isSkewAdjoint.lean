-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.skewAdjointPart_isSkewAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:25:30.623704+00:00
-- url     : https://prove2.me/submissions/01332617-cc4d-4723-abf3-093501dae439

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_JJ
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
private lemma Jm_mul_Jm_self_eq_one (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  simpa using slm_JJ ε 1
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
theorem _root_.solution (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.inG ε (slmP ε Y) := by
  have hs : (star (1 / 2 : ℂ)) = 1 / 2 := by simp
  unfold Formalism.REAL.inG slmP
  rw [Matrix.conjTranspose_smul, hs, Matrix.conjTranspose_sub]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose_eq_Jm, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, slm_JJ, Jm_mul_Jm_self_eq_one, Matrix.mul_one]
  rw [← smul_add]
  simp
end ReciprocityTheory.ChartRestriction.DS
