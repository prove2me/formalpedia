-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hintMH_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:57:15.680074+00:00
-- url     : https://prove2.me/submissions/e609f93e-a386-402a-bc7b-f7b83f3e7ed0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ComponentFormProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintIntOfBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintLogFinprod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {R : Type*} [CommSemiring R] {D n : ℕ} (k : R)
    {q : MvPolynomial (Fin (D + 1) × Fin n) R} (hq : HintMH q) :
    HintMH (MvPolynomial.C k * q) := by
  obtain ⟨α, h0, hα⟩ := hq
  refine ⟨α, h0, fun s hs b => hα s ?_ b⟩
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hs
  exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hs)
end ReciprocityTheory.ChartRestriction.G.T0
