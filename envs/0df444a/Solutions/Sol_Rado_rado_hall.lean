-- Prove2me | solution 1 for Rado.rado_hall
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:29:58.351741+00:00
-- url     : https://prove2.me/submissions/6d396cec-4341-4b3e-bb16-084d1635cccb

import Mathlib
import Theorems.Thm_Rado_rado_defect

set_option autoImplicit false

open Rado

theorem solution {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
    [DecidableEq ι] (A : ι → Set V) (hA : ∀ i, (A i).Finite)
    (h : ∀ S : Finset ι, S.card ≤ Module.finrank k (Submodule.span k (⋃ i ∈ S, A i))) :
    ∃ v : ι → V, (∀ i, v i ∈ A i) ∧ LinearIndependent k v := by
  obtain ⟨J, v, S, hv, hind, hcard⟩ := rado_defect (k := k) A hA
  have hS := h S
  have hc : Sᶜ.card + S.card = Fintype.card ι := by
    rw [Finset.card_compl]; have := Finset.card_le_univ S; omega
  have hJ : J = Finset.univ := Finset.eq_univ_of_card J (by
    have := Finset.card_le_univ J; omega)
  subst hJ
  refine ⟨v, fun i => hv i (Finset.mem_univ i), ?_⟩
  rw [Finset.coe_univ] at hind
  exact linearIndepOn_univ_iff.1 hind

#print axioms solution
