-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.p_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:38:39.666685+00:00
-- url     : https://prove2.me/submissions/8a09ef02-7d9e-4e7c-b25e-0c60649e965a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_zetaC_isPrimitiveRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {p : ℕ} (hp : p.Prime) : ∃ r ∈ Rm p, (p : ℂ) = (1 - zetaC p) * r := by
  haveI := Fact.mk hp
  have hζ := zetaC_isPrimitiveRoot hp.ne_zero
  have hmem : ∀ μ ∈ primitiveRoots p ℂ, μ ∈ Rm p := by
    intro μ hμ
    rw [mem_primitiveRoots hp.pos] at hμ
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    exact pow_mem (Subring.subset_closure (Set.mem_singleton _)) _
  have hprod : (p : ℂ) = ∏ μ ∈ primitiveRoots p ℂ, (1 - μ) := by
    have h1 := Polynomial.eval_one_cyclotomic_prime (R := ℂ) (p := p)
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h1
    simpa using h1.symm
  refine ⟨∏ μ ∈ (primitiveRoots p ℂ).erase (zetaC p), (1 - μ),
    prod_mem fun μ hμ => sub_mem (one_mem _) (hmem μ (Finset.mem_of_mem_erase hμ)), ?_⟩
  rw [hprod, Finset.mul_prod_erase _ _ ((mem_primitiveRoots hp.pos).2 hζ)]
end ReciprocityTheory.ChartRestriction.L1
