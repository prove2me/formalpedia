-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.one_sub_zeta_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:38:34.061981+00:00
-- url     : https://prove2.me/submissions/5fb2ac07-4f37-41cb-910b-ea21f0d364ed

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
theorem _root_.solution {p : ℕ} (hp : p.Prime) : ∃ r ∈ Rm p, (1 - zetaC p) ^ p = (p : ℂ) * r := by
  have hζ := zetaC_isPrimitiveRoot hp.ne_zero
  have hz : zetaC p ∈ Rm p := Subring.subset_closure (Set.mem_singleton _)
  set z : Rm p := ⟨zetaC p, hz⟩ with hzdef
  have hzc : (z : ℂ) = zetaC p := rfl
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (1 : Rm p) (-z)
  have hr' : (1 - zetaC p) ^ p = 1 + (-zetaC p) ^ p + p * (-(zetaC p * (r : ℂ))) := by
    have h1 := congrArg (fun x : Rm p => (x : ℂ)) hr
    push_cast at h1
    rw [hzc] at h1
    rw [sub_eq_add_neg, h1]
    ring
  have hm : -(zetaC p * (r : ℂ)) ∈ Rm p := neg_mem (mul_mem hz r.2)
  rcases hp.eq_two_or_odd' with rfl | hodd
  · refine ⟨1 + -(zetaC 2 * (r : ℂ)), add_mem (one_mem _) hm, ?_⟩
    rw [hr', neg_sq, hζ.pow_eq_one]
    push_cast
    ring
  · refine ⟨-(zetaC p * (r : ℂ)), hm, ?_⟩
    rw [hr', hodd.neg_pow, hζ.pow_eq_one]
    ring
end ReciprocityTheory.ChartRestriction.L1
