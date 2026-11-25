-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.fixJStab_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:30:19.288208+00:00
-- url     : https://prove2.me/submissions/a3e39106-de3e-48d4-8f29-d11482a72e83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModChebOm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModSepInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobCong
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_IsIntegralOfRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFixJ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_mem_fixJStab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] [Algebra.IsAlgebraic E Ω]
    {P : Polynomial ℤ} : IsOpen (fixJStab E Ω P : Set (Ω ≃ₐ[E] Ω)) := by
  let K : IntermediateField E Ω := IntermediateField.adjoin E ((fixJRoots (Ω := Ω) P : Finset Ω) : Set Ω)
  haveI : FiniteDimensional E K := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := E) x).isIntegral)
  refine Subgroup.isOpen_mono (H₁ := K.fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen K)
  intro g hg
  rw [mem_fixJStab]
  intro r hr
  exact hg ⟨r, IntermediateField.subset_adjoin E _ hr⟩
end ReciprocityTheory.ChartRestriction.L1
