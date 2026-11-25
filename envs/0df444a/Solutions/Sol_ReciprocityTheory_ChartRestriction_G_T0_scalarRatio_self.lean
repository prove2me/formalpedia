-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.scalarRatio_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:30:48.31575+00:00
-- url     : https://prove2.me/submissions/3651b8ff-0d38-4d1e-8ad0-e4baa23ecc38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsDualDerivations
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_AlgStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentScaledForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f : V}
    (hf : f ≠ 0) : ratio (Ω := Ω) f f = 1 := by
  unfold ratio
  split_ifs with h
  · have hc : f = h.choose • f := h.choose_spec
    have h0 : (h.choose - 1) • f = 0 := by
      rw [sub_smul, one_smul, ← hc, sub_self]
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hf
  · exact absurd ⟨1, (one_smul Ω f).symm⟩ h
end ReciprocityTheory.ChartRestriction.G.T0
