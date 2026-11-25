-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.transference_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:52:01.855971+00:00
-- url     : https://prove2.me/submissions/59250c06-5ec8-4fae-82da-7d0f7141c0ff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtE_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Module Submodule
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {n : ℕ} (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ x ∈ Submodule.span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖) :
    ∃ y : Fin n → EuclideanSpace ℝ (Fin n), LinearIndependent ℝ y ∧
      (∀ i j, ∃ m : ℤ, inner ℝ (y i) (b j) = m) ∧ ∀ i, ‖y i‖ ≤ (n : ℝ) ^ 2 / lam :=
  gtE_main n b lam hlam hmin
end ReciprocityTheory.ChartRestriction.G.T0
