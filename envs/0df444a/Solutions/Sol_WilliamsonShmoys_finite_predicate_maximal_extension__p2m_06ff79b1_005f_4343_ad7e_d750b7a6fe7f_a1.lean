-- Prove2me | solution 1 for WilliamsonShmoys.finite_predicate_maximal_extension__p2m_06ff79b1_005f_4343_ad7e_d750b7a6fe7f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:21:20.956927+00:00
-- url     : https://prove2.me/submissions/62b3e234-0768-45c2-99e1-f848d08d6c1b

import Mathlib
import Theorems.Thm_finite_nonempty_subset_has_maximal__p2m_f12881bc_f698_449c_9421_69b4df3ce3de_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (L : SimpleGraph V) (hL : P L) :
    ∃ M : SimpleGraph V, L.edgeSet ⊆ M.edgeSet ∧ P M ∧
      ∀ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet → P N → N = M := by
  let r : SimpleGraph V → SimpleGraph V → Prop := fun A B => A.edgeSet ⊆ B.edgeSet
  let S : Set (SimpleGraph V) := fun G => L.edgeSet ⊆ G.edgeSet ∧ P G
  have hS : S.Nonempty := ⟨L, Set.Subset.rfl, hL⟩
  have hrefl : ∀ A : SimpleGraph V, r A A := by
    intro A
    exact Set.Subset.rfl
  have htrans : ∀ {A B C : SimpleGraph V}, r A B → r B C → r A C := by
    intro A B C hAB hBC
    exact Set.Subset.trans hAB hBC
  have hanti : ∀ {A B : SimpleGraph V}, r A B → r B A → A = B := by
    intro A B hAB hBA
    ext v w
    constructor
    · intro hvw
      have hmem : s(v, w) ∈ A.edgeSet := by simpa using hvw
      have hmem' : s(v, w) ∈ B.edgeSet := hAB hmem
      simpa using hmem'
    · intro hvw
      have hmem : s(v, w) ∈ B.edgeSet := by simpa using hvw
      have hmem' : s(v, w) ∈ A.edgeSet := hBA hmem
      simpa using hmem'
  obtain ⟨M, hMS, hmax⟩ :=
    finite_nonempty_subset_has_maximal__p2m_f12881bc_f698_449c_9421_69b4df3ce3de_a1
      r hrefl htrans hanti S hS
  have hLM : L.edgeSet ⊆ M.edgeSet := hMS.1
  have hPM : P M := hMS.2
  refine ⟨M, hLM, hPM, ?_⟩
  intro N hMN hPN
  have hNS : S N := ⟨hLM.trans hMN, hPN⟩
  have hNM : r N M := hmax N hNS hMN
  exact hanti hNM hMN