-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ct_Hf_uc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:16:58.488479+00:00
-- url     : https://prove2.me/submissions/f3a59bcc-3c65-4cf5-8fae-339fceb6eb4f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
private theorem Hf_add_right_euclidean (a b c : EuclideanSpace ℂ ι) : Hf a (b + c) = Hf a b + Hf a c := by
  simp [Hf, mul_add, Finset.sum_add_distrib]
private theorem Hf_finset_sum_right {κ : Type} (s : Finset κ) (v : EuclideanSpace ℂ ι)
    (f : κ → EuclideanSpace ℂ ι) : Hf v (∑ k ∈ s, f k) = ∑ k ∈ s, Hf v (f k) :=
  map_sum (AddMonoidHom.mk' (fun w => Hf v w) (Hf_add_right_euclidean v)) f s
private theorem Hf_real_smul_right (v w : EuclideanSpace ℂ ι) (r : ℝ) :
    Hf v (r • w) = (r : ℂ) * Hf v w := by
  simp only [Hf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp <;> ring
end
end ReciprocityTheory.ChartRestriction.G.I2
namespace ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
variable {K : Submodule ℝ (EuclideanSpace ℂ ι)} (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
include hK
end
end ReciprocityTheory.ChartRestriction.G.I2
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
variable {K : Submodule ℝ (EuclideanSpace ℂ ι)} (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
include hK
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (v a : EuclideanSpace ℂ ι) :
    Hf v (Col.uc K a) = ∑ k, ((Col.z K k a).im : ℂ) * Col.z K k v := by
  simp only [Col.uc]
  rw [Hf_finset_sum_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Hf_real_smul_right]
  rfl
end ReciprocityTheory.ChartRestriction.G.I2
