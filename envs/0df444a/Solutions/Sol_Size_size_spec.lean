-- Prove2me | solution 1 for Size.size_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:09:10.528602+00:00
-- url     : https://prove2.me/submissions/a76b9566-ea8a-4944-9eb5-32674d606c46

import Definitions.Def_Bdd_Collect
import Definitions.Def_Bdd_Size
import Theorems.Thm_Collect_collect_nodup
import Theorems.Thm_Collect_collect_spec
import Theorems.Thm_Collect_collect_spec_reverse
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Size
namespace Size
theorem _root_.solution {O : OBdd n m} : size O = OBdd.size O := by
  simp only [size, OBdd.size, Function.comp_apply]
  simp_rw [Fintype.card, Finset.univ]
  have : (Collect.collect O).length = (Multiset.ofList (Collect.collect O)).card := by rfl
  rw [this]
  refine Eq.symm (Finset.card_eq_of_bijective (fun i hi ↦ ⟨(Collect.collect O).get ⟨i, hi⟩, by simp; exact Collect.collect_spec_reverse (List.getElem_mem hi)⟩) ?_ ?_ ?_)
  · rintro ⟨j, hj⟩ h
    simp only [Subtype.mk.injEq, Multiset.coe_card]
    exact List.mem_iff_getElem.mp (Collect.collect_spec hj)
  · rintro i hi
    simp only [List.get_eq_getElem]
    apply Fintype.complete
  · intro i j hi hj heq
    simp only [List.get_eq_getElem, Subtype.mk.injEq] at heq
    exact (List.Nodup.getElem_inj_iff Collect.collect_nodup).mp heq
end Size
