-- Prove2me | solution 1 for TwoAgentSched.TotalTotal.CountPositive.countBody_success_exact
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:22:36.834188+00:00
-- url     : https://prove2.me/submissions/a2cad1e0-673e-426c-9484-9e8a02964036

import Theorems.Thm_CookPvsNP_CanonicalBlockParser_success_exact_shape
import Theorems.Thm_CookPvsNP_CanonicalBlockParser_execution_and_bounds
import Theorems.Thm_StackProgPortLift_liftProgC_exec
import Theorems.Thm_CookPvsNP_stack_transfer
import Definitions.Def_TwoAgentSched_TotalTotal_CountPositive
open CookPvsNP ProjSchedTW.Complexity TwoAgentSched.TotalTotal.CountPositive
open CookPvsNP.CanonicalBlockParser StackProgPortLift

private theorem det {K A : Type} {p : StackProg K A} {s t : K → List A} {n : ℕ}
    (h : p.Exec s t n) : ∀ {u : K → List A} {m : ℕ}, p.Exec s u m → t = u := by
  induction h with
  | act f s => intro u m h2; cases h2; rfl
  | seq hab hbc ihab ihbc =>
    intro u m h2
    cases h2 with
    | seq hab' hbc' =>
      have e := ihab hab'
      rw [← e] at hbc'
      exact ihbc hbc'
  | branchTrue ht hb ih =>
    intro u m h2
    cases h2 with
    | branchTrue _ hb' => exact ih hb'
    | branchFalse hf _ => rw [ht] at hf; cases hf
  | branchFalse ht hb ih =>
    intro u m h2
    cases h2 with
    | branchFalse _ hb' => exact ih hb'
    | branchTrue hf _ => rw [ht] at hf; cases hf
  | loopFalse ht =>
    intro u m h2
    cases h2 with
    | loopFalse _ => rfl
    | loopTrue ht' _ _ => rw [ht] at ht'; cases ht'
  | loopTrue ht hb hrest ihab ihrest =>
    intro u m h2
    cases h2 with
    | loopFalse ht' => rw [ht] at ht'; cases ht'
    | loopTrue _ hb' hrest' =>
      have e := ihab hb'
      rw [← e] at hrest'
      exact ihrest hrest'

private theorem wat {K L A : Type} (r : K ↪ L) (t : K → List A) (s : L → List A) (k : K) : write r t s (r k) = t k := by
  classical
  unfold write
  split
  · rename_i h
    have hk : Classical.choose h = k := r.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

private theorem wout {K L A : Type} (r : K ↪ L) (t : K → List A) (s : L → List A) {l : L} (h : ∀ k, r k ≠ l) : write r t s l = s l := by
  classical
  unfold write
  split
  · rename_i hex
    obtain ⟨k, hk⟩ := hex
    exact (h k hk).elim
  · rfl

private theorem tailrun (a d z c : List BSym) :
    ∃ m, (StackProg.seq (StackProg.branch incrementTest (.act incrementAct) (.act keepAct)) (clearProg 1)).Exec
      (store4 a d z c) (store4 a [] z (if incrementTest (fun k => (store4 a d z c k).head?) then .one :: c else c)) m := by
  let s := store4 a d z c
  let b := incrementTest (fun k => (s k).head?)
  let t := store4 a d z (if b then .one :: c else c)
  have hb : (StackProg.branch incrementTest (.act incrementAct) (.act keepAct)).Exec s t 2 := by
    cases he : b with
    | false =>
      have ht : incrementTest (fun k => (s k).head?) = false := he
      have ha : StackProg.applyAct keepAct s = t := by
        funext k
        fin_cases k <;> simp [StackProg.applyAct, keepAct, StackAct.apply, s, t, he, store4]
      rw [← ha]
      exact StackProg.Exec.branchFalse ht (StackProg.Exec.act _ _)
    | true =>
      have ht : incrementTest (fun k => (s k).head?) = true := he
      have ha : StackProg.applyAct incrementAct s = t := by
        funext k
        fin_cases k <;> simp [StackProg.applyAct, incrementAct, StackAct.apply, s, t, he, store4]
      rw [← ha]
      exact StackProg.Exec.branchTrue ht (StackProg.Exec.act _ _)
  have hc := CookPvsNP.stack_transfer (A := BSym) (1 : Fin 4) (fun _ => false) t
  have heq : transferStore 1 (fun _ => false) t = store4 a [] z (if b then .one :: c else c) := by
    funext k
    fin_cases k <;> simp [transferStore, t, store4]
  rw [heq] at hc
  exact ⟨_, StackProg.Exec.seq hb hc⟩

theorem solution (input status count : List BSym) (out : Fin 4 → List BSym) (steps : ℕ)
    (h : countBody.Exec (store4 input [] status count) out steps)
    (hs : (out 2).head? = some .one) :
    ∃ (n : ℕ) (rest : List BSym), input = encNat n ++ rest ∧
      out = store4 rest [] (.one :: .one :: status)
        (if n = 0 then count else .one :: count) := by
  obtain ⟨rest, digits, os, ps, hp, _, _, _⟩ := CookPvsNP.CanonicalBlockParser.execution_and_bounds.2 input status
  have hdecode : ∀ l k, parseInverse l = some k ↔ parsePorts k = l := by
    intro l k
    fin_cases l <;> fin_cases k <;> decide
  have hproj : project parsePorts (store4 input [] status count) = store input [] status := by
    funext k
    fin_cases k <;> rfl
  have hl := liftProgC_exec parsePorts parseInverse hdecode hp (store4 input [] status count) hproj
  have hw : write parsePorts (store rest digits os) (store4 input [] status count) = store4 rest digits os count := by
    funext k
    fin_cases k
    · simpa [parsePorts, store, store4] using wat parsePorts (store rest digits os) (store4 input [] status count) 0
    · simpa [parsePorts, store, store4] using wat parsePorts (store rest digits os) (store4 input [] status count) 1
    · simpa [parsePorts, store, store4] using wat parsePorts (store rest digits os) (store4 input [] status count) 2
    · simpa [store4] using wout parsePorts (store rest digits os) (store4 input [] status count) (l := 3) (by intro k; fin_cases k <;> decide)
  rw [hw] at hl
  obtain ⟨m, ht⟩ := tailrun rest digits os count
  have hr := StackProg.Exec.seq hl ht
  have ho : out = store4 rest [] os (if incrementTest (fun k => (store4 rest digits os count k).head?) then .one :: count else count) := det h hr
  rw [ho] at hs
  have hos : os.head? = some .one := by simpa [store4] using hs
  cases os with
  | nil => simp at hos
  | cons x xs =>
    have hx : x = .one := by simpa using hos
    subst x
    obtain ⟨n, hi, hd, hx⟩ := success_exact_shape input status rest digits xs ps hp
    refine ⟨n, rest, hi, ?_⟩
    rw [ho, hx, hd]
    have hn : n.bits = [] ↔ n = 0 := by
      constructor
      · intro hb
        apply Nat.eq_of_testBit_eq
        intro i
        simp [Nat.testBit_eq_inth, hb]
      · intro h; subst n; simp
    by_cases hz : n = 0
    · subst n
      simp [incrementTest, store4]
    · have hbits : n.bits ≠ [] := fun h => hz (hn.mp h)
      have hne : (n.bits.map (fun b ↦ if b then BSym.one else BSym.zero)).reverse ≠ [] := by
        simpa using hbits
      cases hrev : (n.bits.map (fun b ↦ if b then BSym.one else BSym.zero)).reverse with
      | nil => exact (hne hrev).elim
      | cons a as => simp [incrementTest, store4, hrev, hz]
