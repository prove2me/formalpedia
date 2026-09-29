-- Prove2me | solution 1 for Rep.card_smul_eq_zero_of_tateH0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/23e8be2c-a892-505a-a16a-b2c7a9c34e46

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_card_smul_eq_zero_of_tateH0

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep P2MW.S_Rep_card_smul_eq_zero_of_tateH0.Rep"

namespace Rep
p2m_export "Rep" "of norm ρ tateH0"
namespace tateSolutionAux
p2m_open "Rep"

variable {k G : Type*} [CommRing k] [Group G] [Fintype G] {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)

lemma norm_apply_of_mem_invariants (a : A) (ha : a ∈ A.ρ.invariants) :
    A.ρ.norm a = (Fintype.card G : k) • a := by
  rw [Nat.cast_smul_eq_nsmul, ← Finset.card_univ, ← Finset.sum_const]
  simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun g _ => (Representation.mem_invariants _ _).1 ha g

end Rep.tateSolutionAux

open Rep.tateSolutionAux in
theorem solution {k G : Type*} [CommRing k] [Group G] [Fintype G] (A : Rep k G)
    (x : A.tateH0) : (Fintype.card G : k) • x = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine ⟨Representation.Coinvariants.mk A.ρ a, Subtype.ext ?_⟩
  rw [Representation.normBar_mk, Representation.coe_normToInvariants_apply, Submodule.coe_smul]
  exact norm_apply_of_mem_invariants (a : A) a.2

end S_Rep_card_smul_eq_zero_of_tateH0
end P2MW
export P2MW.S_Rep_card_smul_eq_zero_of_tateH0 (solution)
