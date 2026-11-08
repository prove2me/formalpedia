-- Prove2me | solution 1 for SepCostShare.line8_well_defined
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:28:33.496294+00:00
-- url     : https://prove2.me/submissions/c58b3e46-483d-4178-9510-43e938fe0594

import Mathlib
import Definitions.Def_SepCostShare_MatroidGame
import Definitions.Def_SepCostShare_Deviation
import Definitions.Def_SepCostShare_Algorithm

open SepCostShare in
theorem solution {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E]
    [DecidableEq E] (G : MatroidGame N E) (hG : G.Subadditive) (B : N → Finset E)
    (hB : G.IsProfile B) (e : E) (h2 : G.cond2 B e) :
    ∃ i ∈ G.users e B, G.deltaBar B i e < G.c e {i} + G.d i e := by
  have hsub : ∀ S : Finset N, S.Nonempty → G.c e S ≤ ∑ i ∈ S, G.c e {i} := by
    intro S hS
    refine Finset.Nonempty.cons_induction
      (motive := fun S _ => G.c e S ≤ ∑ i ∈ S, G.c e {i}) ?_ ?_ hS
    · intro a
      rw [Finset.sum_singleton]
    · intro a s ha hs ih
      rw [Finset.cons_eq_insert, Finset.sum_insert ha]
      have hss : s ⊂ Finset.univ :=
        Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ s, fun h => ha (h ▸ Finset.mem_univ a)⟩
      linarith [hG.2 e s hss a]
  by_contra hne
  push_neg at hne
  obtain ⟨hne', hlt⟩ := h2
  have hle : ∑ i ∈ G.users e B, G.c e {i} ≤ ∑ i ∈ G.users e B, (G.deltaBar B i e - G.d i e) :=
    Finset.sum_le_sum (fun i hi => by linarith [hne i hi])
  linarith [hsub _ hne']
