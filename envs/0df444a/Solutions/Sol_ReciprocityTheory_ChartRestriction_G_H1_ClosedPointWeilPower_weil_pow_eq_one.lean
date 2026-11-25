-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower.weil_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:26:46.017929+00:00
-- url     : https://prove2.me/submissions/882215ef-9e04-44fa-80d1-98a6c133db24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ClosedPointWeilPower
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_ClosedPointWeilPower_weil_one_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower
theorem _root_.solution (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (x y : T ⟶ P.A) (hx : x ^ k = 1) (hy : y ^ k = 1) (c : Γ(T.left, ⊤)ˣ)
    (hc : WeilIs P.A P.L k x y c) : c ^ k = 1 := by
  have hpow : ∀ n : ℕ, WeilIs P.A P.L k (x ^ n) y (c ^ n) := by
    intro n
    induction n with
    | zero => simpa using weil_one_left hW P k y hy
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (hW S P k T).2.1 _ _ _ _ _ ih hc
  have h1 := hpow k
  rw [hx] at h1
  exact ((hW S P k T).1 1 y (one_pow k) hy).unique h1 (weil_one_left hW P k y hy)
end ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower
