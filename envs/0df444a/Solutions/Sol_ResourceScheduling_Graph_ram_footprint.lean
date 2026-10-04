-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_footprint
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:23:34.151189+00:00
-- url     : https://prove2.me/submissions/12694b08-edec-442d-aa0e-7d841faf9039

import Definitions.Def_ResourceScheduling_Graph_RAMCode

set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

private theorem iter {V : Type} (f : RAMState V → RAMState V) (v : V)
    (h : ∀ s, (f s).val v = s.val v) (n : ℕ) (s : RAMState V) :
    ((f^[n]) s).val v = s.val v := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, h]

theorem solution {V : Type} [DecidableEq V] (p : RAMCode V) (v : V)
    (h : p.writes v = false) (s : RAMState V) : (p.eval s).val v = s.val v := by
  induction p generalizing s with
  | seq p q ihp ihq =>
    simp only [RAMCode.writes, Bool.or_eq_false_iff] at h
    exact (ihq h.2 (p.eval s)).trans (ihp h.1 s)
  | branch j p q ihp ihq =>
    simp only [RAMCode.writes, Bool.or_eq_false_iff] at h
    simp only [RAMCode.eval]; split <;> first | exact ihp h.1 s | exact ihq h.2 s
  | loop j p ih =>
    simp only [RAMCode.writes, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    apply iter
    intro s'
    simpa [RAMState.set, h.1] using ih h.2 (s'.set j (s'.val j - 1))
  | parse t good htg =>
    simp only [RAMCode.writes, decide_eq_false_iff_not, not_or] at h
    simp [RAMCode.eval, ramParseState, RAMState.set, h.1, h.2]
  | _ => simp_all [RAMCode.writes, RAMCode.eval, RAMState.set]

#print axioms solution
