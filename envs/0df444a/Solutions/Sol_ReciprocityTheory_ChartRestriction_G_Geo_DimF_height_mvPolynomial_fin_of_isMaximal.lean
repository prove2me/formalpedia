-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_mvPolynomial_fin_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:01:08.701418+00:00
-- url     : https://prove2.me/submissions/a8493ecf-9ffb-4309-ae76-d1eac6fb001a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_height_polynomial_of_isMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.DimF
open Ideal
namespace ReciprocityTheory.ChartRestriction.G.Geo.DimF
theorem _root_.solution {k : Type*} [Field k] :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k)), M.IsMaximal → M.height = n
  | 0, M, hM => by
    have h := Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
    have h' : M.height ≤ 0 := by
      have : ((M.height : ℕ∞) : WithBot ℕ∞) ≤ ((0 : ℕ∞) : WithBot ℕ∞) := by simpa using h
      exact WithBot.coe_le_coe.mp this
    simpa using h'
  | n + 1, M, hM => by
    let e := (MvPolynomial.finSuccEquiv k n).toRingEquiv
    have hM' : (M.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    rw [← e.height_map M, height_polynomial_of_isMaximal
      (solution n) _ hM']
    simp
end ReciprocityTheory.ChartRestriction.G.Geo.DimF
