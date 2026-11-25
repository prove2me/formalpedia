-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_Y_inG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:25:36.746422+00:00
-- url     : https://prove2.me/submissions/eb7772ab-cbad-49f5-bbfa-b3f6c17baba7

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
theorem _root_.solution {h : Matrix (Fin n) (Fin n) ℂ} (hh : Formalism.REAL.inUJ ε h) (hd : (h + 1).det ≠ 0) :
    Formalism.REAL.inG ε ((h - 1) * (h + 1)⁻¹) := by
  have hu : IsUnit (h + 1).det := isUnit_iff_ne_zero.mpr hd
  have hA1 : (h + 1) * (h + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hA2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, ((h + 1)⁻¹)ᴴ * ((h + 1)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hA1, Matrix.conjTranspose_one, Matrix.one_mul]
  have hm : (h - 1)ᴴ * Formalism.REAL.Jm ε * (h + 1) + (h + 1)ᴴ * Formalism.REAL.Jm ε * (h - 1) = 0 := by
    unfold Formalism.REAL.inUJ at hh
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.sub_mul,
      Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hh]
    abel
  unfold Formalism.REAL.inG
  generalize h + 1 = A at hA1 hA2 hm ⊢
  generalize h - 1 = B at hm ⊢
  calc (B * A⁻¹)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (B * A⁻¹)
      = (A⁻¹)ᴴ * (Bᴴ * Formalism.REAL.Jm ε * A + Aᴴ * Formalism.REAL.Jm ε * B) * A⁻¹ := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hA1, hA2, Matrix.mul_one]
    _ = 0 := by rw [hm, Matrix.mul_zero, Matrix.zero_mul]
end ReciprocityTheory.ChartRestriction.DS
