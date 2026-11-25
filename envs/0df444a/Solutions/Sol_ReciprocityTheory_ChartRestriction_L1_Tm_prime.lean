-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.Tm_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:35:52.411011+00:00
-- url     : https://prove2.me/submissions/7b9c9797-0bbc-4792-8abe-eb1956423c25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Cg_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Cg_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Cg_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_mem_Tm


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
theorem _root_.solution {p : ℕ} (hp : p.Prime) :
    Tm p = insert (p, 0, 1) ((Finset.range p).image fun b => (1, b, p)) := by
  ext ⟨a, b, e⟩
  rw [mem_Tm hp.pos, Finset.mem_insert, Finset.mem_image]
  simp only [Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨hae, hbe⟩
    have ha : a ∣ p := ⟨e, hae.symm⟩
    rcases hp.eq_one_or_self_of_dvd a ha with rfl | rfl
    · right
      exact ⟨b, by omega, rfl, rfl, by omega⟩
    · left
      have he : e = 1 := Nat.eq_of_mul_eq_mul_left hp.pos (hae.trans (mul_one a).symm)
      subst he
      exact ⟨rfl, by omega, rfl⟩
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨c, hc, rfl, rfl, rfl⟩)
    · exact ⟨mul_one _, Nat.zero_lt_one⟩
    · exact ⟨one_mul _, hc⟩
end ReciprocityTheory.ChartRestriction.L1
