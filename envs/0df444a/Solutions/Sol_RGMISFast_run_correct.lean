-- Prove2me | solution 1 for RGMISFast.run_correct
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-15T01:29:12.632755+00:00
-- url     : https://prove2.me/submissions/23fbbd7e-c240-4e7b-9fe9-8eeaa0667231

import Definitions.Def_RGMISFast_tau
open RGMISFast
set_option autoImplicit false

private theorem fold_shortcircuit_correct {A S : Type*} (P : S → Prop)
    (f : A → S → Bool × S) (g : A → Bool)
    (hf : ∀ a st, P st → P (f a st).2 ∧ (f a st).1 = g a)
    (l : List A) (acc : Bool × S) (hp : P acc.2) :
    P (l.foldl (fun acc a => if acc.1 then acc else f a acc.2) acc).2 ∧
    (l.foldl (fun acc a => if acc.1 then acc else f a acc.2) acc).1 =
      (acc.1 || l.any g) := by
  induction l generalizing acc with
  | nil => simpa using hp
  | cons a l ih =>
    simp only [List.foldl_cons, List.any_cons]
    cases ha : acc.1 with
    | true =>
      simp only [ha, Bool.true_eq, ↓reduceIte, Bool.true_or]
      simpa [ha] using ih acc hp
    | false =>
      simp only [ha, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
      obtain ⟨hs, hv⟩ := hf a acc.2 hp
      simpa [hv] using ih (f a acc.2) hs

private def Sound {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (st : RunState V) : Prop :=
  ∀ v b, st.memo v = some b → b = inMIS G r v

private theorem sound_update {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (st : RunState V)
    (hs : Sound G r st) (v : V) (b : Bool) (hb : b = inMIS G r v) :
    Sound G r {st with memo := Function.update st.memo v (some b)} := by
  classical
  intro w c hc
  by_cases hw : w = v
  · subst w
    have he : b = c := by simpa using hc
    exact he.symm.trans hb
  · exact hs w c (by simpa [Function.update_of_ne hw] using hc)

private theorem call_correct {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (n : ℕ) :
    ∀ caller v (hn : rk r v < n) st, Sound G r st →
      Sound G r (callF G r n caller v hn st).2 ∧
      (callF G r n caller v hn st).1 = inMIS G r v := by
  classical
  induction n with
  | zero => intro caller v hn; omega
  | succ n ih =>
    intro caller v hn st hs
    simp only [callF]
    split
    next b hb => exact ⟨hs, hs v b hb⟩
    next hb =>
      let s1 : RunState V := {st with count := st.count + 1, trace := st.trace ++ [⟨caller,v,true⟩]}
      let exec := fun (w : {w // w ∈ lowerNbrs G r v}) (s : RunState V) =>
        callF G r n (some v) w.val
          (by have := rk_lt r ((mem_lowerNbrs G r).1 w.property).2; omega) s
      have hf := fold_shortcircuit_correct (Sound G r) exec
        (fun w => inMIS G r w.val)
        (by intro w s h; exact ih _ _ _ _ h)
        (lowerNbrs G r v).attach (false,s1) hs
      let result := (lowerNbrs G r v).attach.foldl
        (fun acc w => if acc.1 then acc else exec w acc.2) (false,s1)
      have hr : (!result.1) = inMIS G r v := by
        rw [inMIS_eq]
        change (!result.1) = _
        rw [show result.1 = ((lowerNbrs G r v).attach.any (fun w => inMIS G r w.val)) by simpa [result] using hf.2]
        exact List.not_any_eq_all_not
      exact ⟨sound_update G r result.2 hf.1 v _ hr, hr⟩

theorem solution {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (r : V → ℝ) :
    (∀ v b, (run G r u).2.memo v = some b → b = inMIS G r v) ∧
    (run G r u).1 = inMIS G r u := by
  exact call_correct G r _ none u _ initState (by intro v b h; cases h)
