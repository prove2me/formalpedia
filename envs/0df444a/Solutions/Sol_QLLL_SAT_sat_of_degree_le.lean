-- Prove2me | solution 1 for QLLL.SAT.sat_of_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:57:17.589616+00:00
-- url     : https://prove2.me/submissions/e4f73d90-e1f1-49b2-afa8-8284b24fd299

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Classical_KSAT
import Theorems.Thm_QLLL_SAT_exists_forall_clause_eval
import Mathlib
import Std.Sat.CNF

section

open QLLL
open QLLL.SAT
open Finset Std.Sat
variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
variable {V : ℕ}

theorem solution {V : ℕ} (f : CNF (Fin V)) (k D : ℕ) (hk : 1 ≤ k) (hD1 : 1 ≤ D)
    (hvars : ∀ i : Fin f.clauses.size, (clauseVars (f.clauses[i.1]'i.2)).card = k)
    (hdeg : ∀ v : Fin V, (univ.filter fun i : Fin f.clauses.size =>
        v ∈ clauseVars (f.clauses[i.1]'i.2)).card ≤ D)
    (hDk : (D : ℝ) * (Real.exp 1 * k) ≤ 2 ^ k) :
    ∃ a, CNF.Sat a f := by
  obtain ⟨a, ha⟩ := exists_forall_clause_eval
    (fun i : Fin f.clauses.size => f.clauses[i.1]'i.2) k D hk hD1 hvars hdeg hDk
  refine ⟨a, ?_⟩
  simp only [CNF.Sat, CNF.eval, Array.all_eq_true_iff_forall_mem]
  intro c hc
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hc
  exact ha ⟨i, hi⟩

end
