-- Prove2me | solution 1 for ResourceScheduling.Poly.q2_algorithm_optimal
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T18:10:35.635619+00:00
-- url     : https://prove2.me/submissions/f3428600-401e-47bd-9278-d03d319d8b79

import Mathlib
import Definitions.Def_ResourceScheduling_Poly_Model
import Definitions.Def_ResourceScheduling_Poly_Q2Properties
import Definitions.Def_ResourceScheduling_Poly_Q2Algorithm
import Theorems.Thm_ResourceScheduling_Poly_q2_algorithm_best_abc
import Theorems.Thm_ResourceScheduling_Poly_q2_exists_abc_le

open ResourceScheduling.Poly

/-- Theorem 5 (Błażewicz–Lenstra–Rinnooy Kan 1983), correctness of the algorithm:
the algorithm's schedule is feasible, and by the exchange argument every feasible schedule
is dominated by a feasible (a)–(c) schedule, among which the algorithm is best. -/
theorem solution (I : Instance) (hm : I.m = 2) (hl : I.l = 1)
    (hprec : I.NoPrecedence) (hq : I.q (I.M₂ hm) ≤ I.q (I.M₁ hm)) (hfit : I.EveryJobFits)
    (ord : Fin I.n ≃ Fin I.n) (hord : Antitone fun p => I.r (I.R₁ hl) (ord p)) :
    (q2Algorithm I hm hl ord).Feasible ∧
      ∀ σ : Schedule I, σ.Feasible → (q2Algorithm I hm hl ord).makespan ≤ σ.makespan := by
  obtain ⟨hfeas, -, hbest⟩ := q2_algorithm_best_abc I hm hl hprec hq hfit ord hord
  refine ⟨hfeas, fun σ hσ => ?_⟩
  obtain ⟨σ', hσ'f, hσ'abc, hle⟩ := q2_exists_abc_le I hm hl hprec hq σ hσ
  exact (hbest σ' hσ'f hσ'abc).trans hle
