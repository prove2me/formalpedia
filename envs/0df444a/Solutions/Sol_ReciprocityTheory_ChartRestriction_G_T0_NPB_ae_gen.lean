-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.NPB.ae_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:06:32.255515+00:00
-- url     : https://prove2.me/submissions/9411044e-3f55-41ac-8f3b-afa65315635b

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_countable_mvPoly
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ae_blockSphere_eval_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.NPB
open MvPolynomial MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.NPB
theorem _root_.solution (sg : K →+* ℂ) [Countable K] :
    ∀ᵐ z ∂(blockSphereProb D (N + 1)), ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K),
      IsMultiHomogeneous a p → p ≠ 0 → eval₂ sg (blockPoint z) p ≠ 0 := by
  have := countable_mvPoly (σ := Fin D × Fin (N + 1)) (R := K)
  rw [ae_all_iff]; intro a
  rw [ae_all_iff]; intro p
  by_cases hp : IsMultiHomogeneous a p ∧ p ≠ 0
  · have hm : IsMultiHomogeneous a (MvPolynomial.map sg p) :=
      fun s hs => hp.1 s (support_map_subset _ _ hs)
    have hm0 : MvPolynomial.map sg p ≠ 0 := fun h0 =>
      hp.2 (map_injective sg sg.injective (by rw [h0, map_zero]))
    filter_upwards [ae_blockSphere_eval_ne_zero D (N + 1) a _ hm0 hm] with z hz _ _
    rwa [eval_map] at hz
  · exact Filter.Eventually.of_forall fun z h1 h2 => absurd ⟨h1, h2⟩ hp
end ReciprocityTheory.ChartRestriction.G.T0.NPB
