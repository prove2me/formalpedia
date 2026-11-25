-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_cay_inUJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:25:41.831612+00:00
-- url     : https://prove2.me/submissions/66992b00-eef4-4cfb-8ba3-ffc0b42e7ed6

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
theorem _root_.solution {X : Matrix (Fin n) (Fin n) ℂ} (hX : Formalism.REAL.inG ε X) (hd : (1 - X).det ≠ 0) :
    Formalism.REAL.inUJ ε ((1 + X) * (1 - X)⁻¹) := by
  have hu : IsUnit (1 - X).det := isUnit_iff_ne_zero.mpr hd
  have hC1 : (1 - X) * (1 - X)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hC2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, ((1 - X)⁻¹)ᴴ * ((1 - X)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hC1, Matrix.conjTranspose_one, Matrix.one_mul]
  have hm : (1 + X)ᴴ * Formalism.REAL.Jm ε * (1 + X) = (1 - X)ᴴ * Formalism.REAL.Jm ε * (1 - X) := by
    unfold Formalism.REAL.inG at hX
    have hX' : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.sub_mul,
      Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hX']
    abel
  unfold Formalism.REAL.inUJ
  calc ((1 + X) * (1 - X)⁻¹)ᴴ * Formalism.REAL.Jm ε * ((1 + X) * (1 - X)⁻¹)
      = ((1 - X)⁻¹)ᴴ * ((1 + X)ᴴ * Formalism.REAL.Jm ε * (1 + X)) * (1 - X)⁻¹ := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = ((1 - X)⁻¹)ᴴ * ((1 - X)ᴴ * Formalism.REAL.Jm ε * (1 - X)) * (1 - X)⁻¹ := by rw [hm]
    _ = Formalism.REAL.Jm ε := by simp only [Matrix.mul_assoc, hC1, hC2, Matrix.mul_one]
end ReciprocityTheory.ChartRestriction.DS
