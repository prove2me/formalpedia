-- Prove2me | solution 1 for OrdinalMSP.Forbidden.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T12:58:23.788384+00:00
-- url     : https://prove2.me/submissions/276d001d-f1c2-435c-b9fd-d111fdbe03af

import Mathlib
import Definitions.Def_OrdinalMSP_Forbidden_Setting

open OrdinalMSP.Forbidden

theorem mem_opt_iff' {R : Type*} [Fintype R] [DecidableEq R] [LinearOrder R]
    (M : Matroid R) (Q : Finset R) (r : R) :
    r ∈ opt M Q ↔ r ∈ Q ∧ r ∉ M.closure {q | q ∈ Q ∧ r < q} := by
  classical
  unfold opt
  rw [Finset.mem_filter]

theorem solution {R : Type*} [Fintype R] [DecidableEq R] [LinearOrder R]
    (M : Matroid R) (hE : M.E = Set.univ) (Q : Finset R) :
    opt M Finset.univ ∩ Q ⊆ opt M Q := by
  intro r hr
  rw [Finset.mem_inter] at hr
  obtain ⟨h1, h2⟩ := hr
  rw [mem_opt_iff'] at h1 ⊢
  refine ⟨h2, fun hc => h1.2 ?_⟩
  refine M.closure_subset_closure ?_ hc
  intro q hq
  exact ⟨Finset.mem_univ _, hq.2⟩
