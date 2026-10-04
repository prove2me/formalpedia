-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_field_frame
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:42:38.381161+00:00
-- url     : https://prove2.me/submissions/92442d0e-d493-4848-8910-7466ec5e5e8d

import Definitions.Def_ResourceScheduling_Graph_RAMFields

set_option autoImplicit false
open ResourceScheduling.Graph

private theorem iter {V : Type} (f : RAMState V → RAMState V) (b : Bool)
    (h : ∀ s, (f s).field b = s.field b) (k : ℕ) (s : RAMState V) :
    ((f^[k]) s).field b = s.field b := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih, h]

theorem solution {V : Type} [DecidableEq V] (p : RAMCode V) (b : Bool)
    (h : p.effect b = false) (s : RAMState V) : (p.eval s).field b = s.field b := by
  induction p generalizing s with
  | seq p q ihp ihq =>
    simp only [RAMCode.effect, Bool.or_eq_false_iff] at h
    exact (ihq h.2 (p.eval s)).trans (ihp h.1 s)
  | branch j p q ihp ihq =>
    simp only [RAMCode.effect, Bool.or_eq_false_iff] at h
    simp only [RAMCode.eval]; split <;> first | exact ihp h.1 s | exact ihq h.2 s
  | loop j p ih =>
    apply iter
    intro s'
    simpa [RAMState.field, RAMState.set] using ih h (s'.set j (s'.val j - 1))
  | _ => cases b <;> simp_all [RAMCode.effect, RAMCode.eval, RAMState.field, RAMState.set, ramParseState]

#print axioms solution
