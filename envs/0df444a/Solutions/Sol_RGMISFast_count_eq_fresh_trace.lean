-- Prove2me | solution 1 for RGMISFast.count_eq_fresh_trace
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-15T01:29:13.462605+00:00
-- url     : https://prove2.me/submissions/d1e97721-2039-4b3f-9f8e-74c13de138a5

import Definitions.Def_RGMISFast_run
open RGMISFast
set_option autoImplicit false

private theorem fold_preserves {A S : Type*} (P : S → Prop) (f : S → A → S)
    (hf : ∀ s a, P s → P (f s a)) (l : List A) (s : S) (hs : P s) :
    P (l.foldl f s) := by
  induction l generalizing s with
  | nil => exact hs
  | cons a l ih => exact ih (f s a) (hf s a hs)

private def CountOK {V : Type*} (st : RunState V) : Prop :=
  st.count = (st.trace.filter (fun e => e.fresh)).length

private theorem count_call {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (n : ℕ) :
    ∀ caller v (hn : rk r v < n) st, CountOK st →
      CountOK (callF G r n caller v hn st).2 := by
  induction n with
  | zero => intro caller v hn; omega
  | succ n ih =>
    intro caller v hn st hs
    simp only [callF]
    split
    · simpa [CountOK, List.filter_append] using hs
    · let s1 : RunState V := {st with count := st.count + 1, trace := st.trace ++ [⟨caller,v,true⟩]}
      have hs1 : CountOK s1 := by simpa [CountOK, s1, List.filter_append] using hs
      have hf := fold_preserves (fun acc : Bool × RunState V => CountOK acc.2)
        (fun acc (w : {w // w ∈ lowerNbrs G r v}) => if acc.1 then acc else
          callF G r n (some v) w.val
            (by have := rk_lt r ((mem_lowerNbrs G r).1 w.property).2; omega) acc.2)
        (by intro acc w h; split; exact h; exact ih _ _ _ _ h)
        (lowerNbrs G r v).attach (false,s1) hs1
      exact hf

theorem solution {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (r : V → ℝ) :
    (((run G r u).2.trace.filter (fun e => e.fresh)).map (fun e => e.callee)).length = Q G u r := by
  rw [List.length_map]
  exact (count_call G r _ none u _ initState rfl).symm
