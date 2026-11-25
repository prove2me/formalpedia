-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.LocAt.unitAt_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:28:11.481521+00:00
-- url     : https://prove2.me/submissions/f441ede0-d991-469a-8c4c-950a395f9742

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DiscLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UnitAtIntAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LocAt_unitAt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LocAt_unitAt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
open ReciprocityTheory.ChartRestriction.G.T0.LocAt
variable {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
variable {p : Ideal R} [hP : p.IsPrime]
include hP
omit [IsDomain R] [IsFractionRing R F]
namespace ReciprocityTheory.ChartRestriction.G.T0.LocAt
theorem _root_.solution {κ : Type*} (s : Finset κ) (f : κ → F) (hf : ∀ i ∈ s, UnitAt p (f i)) :
    UnitAt p (∏ i ∈ s, f i) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.prod_empty]
    exact unitAt_one
  · intro i s hi ih hf
    rw [Finset.prod_insert hi]
    exact unitAt_mul (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
end ReciprocityTheory.ChartRestriction.G.T0.LocAt
