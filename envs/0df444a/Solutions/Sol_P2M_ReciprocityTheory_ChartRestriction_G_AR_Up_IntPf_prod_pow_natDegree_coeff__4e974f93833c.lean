-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_IntPf_prod_pow_natDegree_coeff__4e974f93833c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:57:16.934465+00:00
-- url     : https://prove2.me/submissions/0835d9eb-fca6-47e0-a417-7993b6758322

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
import Theorems.Thm_Bl_FirstLemmaA_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
noncomputable section
open Polynomial
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
theorem _root_.solution {B : Type*} [CommRing B] {ι : Type*} (s : Finset ι)
    (v : ι → B[X]) (d : ι → ℕ) (hv : ∀ i, (v i).natDegree ≤ 1) :
    (∏ i ∈ s, v i ^ d i).natDegree ≤ ∑ i ∈ s, d i ∧
      (∏ i ∈ s, v i ^ d i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (v i).coeff 1 ^ d i := by
  first | exact Bl.FirstLemmaA.goal1 .. | (apply Bl.FirstLemmaA.goal1 <;> assumption) | (intros; apply Bl.FirstLemmaA.goal1 <;> assumption) | (apply @Bl.FirstLemmaA.goal1 <;> assumption) | (intros; apply @Bl.FirstLemmaA.goal1 <;> assumption) | (apply @Bl.FirstLemmaA.goal1 <;> first | assumption | infer_instance)
end ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
