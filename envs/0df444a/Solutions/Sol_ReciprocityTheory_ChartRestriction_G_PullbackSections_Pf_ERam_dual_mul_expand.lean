-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.dual_mul_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:27:25.496882+00:00
-- url     : https://prove2.me/submissions/845b3640-133e-4160-a6e7-f3d287688bf7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_IdemDataBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamData
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_dual_expand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_trace_dual_mul


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
open NumberField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
theorem _root_.solution (a : 𝓞 E) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (a : E) * TB.trDual (integralBasis E) i =
      ∑ j, (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E j) i : ℤ) : ℚ) • TB.trDual (integralBasis E) j := by
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dual_expand (integralBasis E) ((a : E) * TB.trDual (integralBasis E) i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hb : ∀ l, integralBasis E l = ((RingOfIntegers.basis E l : 𝓞 E) : E) :=
    fun l => NumberField.integralBasis_apply E l
  have e1 : (a : E) * TB.trDual (integralBasis E) i * integralBasis E j =
      TB.trDual (integralBasis E) i * ((a * RingOfIntegers.basis E j : 𝓞 E) : E) := by
    rw [hb]
    push_cast
    ring
  rw [e1, ← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E j)]
  push_cast
  simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_zsmul, ← hb,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.trace_dual_mul]
  simp
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
