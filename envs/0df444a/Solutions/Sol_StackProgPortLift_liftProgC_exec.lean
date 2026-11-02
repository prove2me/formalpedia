-- Prove2me | solution 1 for StackProgPortLift.liftProgC_exec
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:34:56.376382+00:00
-- url     : https://prove2.me/submissions/471d0859-d6f8-43c2-9f54-6e2fe356b176

import Mathlib
import Definitions.Def_StackProgPortLift

set_option autoImplicit false
open CookPvsNP

namespace StackProgPortLift

private theorem write_at {K L A : Type} (r : K ↪ L) (t : K → List A)
    (s : L → List A) (k : K) : write r t s (r k) = t k := by
  classical
  unfold write
  split
  · rename_i h
    have hk : Classical.choose h = k := r.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

private theorem write_outside {K L A : Type} (r : K ↪ L) (t : K → List A)
    (s : L → List A) {l : L} (h : ∀ k, r k ≠ l) : write r t s l = s l := by
  classical
  unfold write
  split
  · rename_i hex
    obtain ⟨k, hk⟩ := hex
    exact (h k hk).elim
  · rfl

private theorem liftAct_at {K L A : Type} (r : K ↪ L)
    (f : (K → Option A) → K → StackAct A) (h : L → Option A) (k : K) :
    liftAct r f h (r k) = f (fun j ↦ h (r j)) k := by
  classical
  unfold liftAct
  split
  · rename_i hex
    have hk : Classical.choose hex = k := r.injective (Classical.choose_spec hex)
    rw [hk]
  · rename_i hex
    exact (hex ⟨k, rfl⟩).elim

/-- A lifted atomic action simulates the source action and preserves every
    port outside the embedded source interface. -/
theorem lift_applyAct {K L A : Type} (r : K ↪ L)
    (f : (K → Option A) → K → StackAct A) (s : L → List A) :
    StackProg.applyAct (liftAct r f) s =
      write r (StackProg.applyAct f (project r s)) s := by
  classical
  funext l
  by_cases hex : ∃ k, r k = l
  · obtain ⟨k, rfl⟩ := hex
    simp [StackProg.applyAct, project, liftAct_at, write_at]
  · have hout : ∀ k, r k ≠ l := by
      intro k hk
      exact hex ⟨k, hk⟩
    simp [StackProg.applyAct, liftAct, hex, write_outside r _ _ hout, StackAct.apply]



private theorem project_write {K L A : Type} (r : K ↪ L) (t : K → List A)
    (s : L → List A) : project r (write r t s) = t := by
  funext k
  exact write_at r t s k

private theorem write_project {K L A : Type} (r : K ↪ L) (s : L → List A) :
    write r (project r s) s = s := by
  classical
  funext l
  by_cases hex : ∃ k, r k = l
  · obtain ⟨k, rfl⟩ := hex
    rw [write_at]
    rfl
  · have hout : ∀ k, r k ≠ l := by
      intro k hk
      exact hex ⟨k, hk⟩
    exact write_outside r _ _ hout

private theorem write_overwrite {K L A : Type} (r : K ↪ L) (u t : K → List A)
    (s : L → List A) : write r u (write r t s) = write r u s := by
  classical
  funext l
  by_cases hex : ∃ k, r k = l
  · obtain ⟨k, rfl⟩ := hex
    simp only [write_at]
  · have hout : ∀ k, r k ≠ l := by
      intro k hk
      exact hex ⟨k, hk⟩
    rw [write_outside r u _ hout, write_outside r t s hout, write_outside r u s hout]

private theorem projected_heads {K L A : Type} (r : K ↪ L) (base : L → List A)
    (s : K → List A) (hs : project r base = s) :
    (fun k ↦ (base (r k)).head?) = fun k ↦ (s k).head? := by
  funext k
  exact congrArg List.head? (congrFun hs k)

/-- Injectively reindexing a structured stack program simulates every source
    execution with exactly the same step count. Nonselected ports keep their
    original contents. -/
theorem lift_exec {K L A : Type} (r : K ↪ L) {p : StackProg K A}
    {s t : K → List A} {n : ℕ} (h : p.Exec s t n) :
    ∀ base : L → List A, project r base = s →
      (liftProg r p).Exec base (write r t base) n := by
  induction h with
  | act f s =>
    intro base hb
    have heq := lift_applyAct r f base
    rw [hb] at heq
    change (StackProg.act (liftAct r f)).Exec base (write r (StackProg.applyAct f s) base) 1
    rw [← heq]
    exact StackProg.Exec.act _ _
  | @seq p q s t u n m hp hq ihp ihq =>
    intro base hb
    have h1 := ihp base hb
    have h2 := ihq (write r t base) (project_write r t base)
    have hs := StackProg.Exec.seq h1 h2
    rw [write_overwrite] at hs
    simpa only [liftProg] using hs
  | @branchTrue test p q s t n htest hp ih =>
    intro base hb
    have hheads := projected_heads r base s hb
    have hcond : (fun h ↦ test (fun k ↦ h (r k))) (fun l ↦ (base l).head?) = true := by
      change test (fun k ↦ (base (r k)).head?) = true
      rw [hheads]
      exact htest
    have hs := StackProg.Exec.branchTrue (test := fun h : L → Option A ↦ test (fun k ↦ h (r k)))
      (p := liftProg r p) (q := liftProg r q) hcond (ih base hb)
    simpa only [liftProg] using hs
  | @branchFalse test p q s t n htest hq ih =>
    intro base hb
    have hheads := projected_heads r base s hb
    have hcond : (fun h ↦ test (fun k ↦ h (r k))) (fun l ↦ (base l).head?) = false := by
      change test (fun k ↦ (base (r k)).head?) = false
      rw [hheads]
      exact htest
    have hs := StackProg.Exec.branchFalse (test := fun h : L → Option A ↦ test (fun k ↦ h (r k)))
      (p := liftProg r p) (q := liftProg r q) hcond (ih base hb)
    simpa only [liftProg] using hs
  | @loopFalse test p s htest =>
    intro base hb
    have hheads := projected_heads r base s hb
    have hcond : (fun h ↦ test (fun k ↦ h (r k))) (fun l ↦ (base l).head?) = false := by
      change test (fun k ↦ (base (r k)).head?) = false
      rw [hheads]
      exact htest
    have heq : write r s base = base := by
      rw [← hb]
      exact write_project r base
    have hs := StackProg.Exec.loopFalse (test := fun h : L → Option A ↦ test (fun k ↦ h (r k)))
      (p := liftProg r p) (s := base) hcond
    simpa only [liftProg, heq] using hs
  | @loopTrue test p s t u n m htest hp hloop ihp ihloop =>
    intro base hb
    have hheads := projected_heads r base s hb
    have hcond : (fun h ↦ test (fun k ↦ h (r k))) (fun l ↦ (base l).head?) = true := by
      change test (fun k ↦ (base (r k)).head?) = true
      rw [hheads]
      exact htest
    have h1 := ihp base hb
    have h2 : (StackProg.loop (fun h : L → Option A ↦ test (fun k ↦ h (r k)))
        (liftProg r p)).Exec (write r t base) (write r u (write r t base)) m := by
      simpa only [liftProg] using ihloop (write r t base) (project_write r t base)
    have hs := StackProg.Exec.loopTrue
      (test := fun h : L → Option A ↦ test (fun k ↦ h (r k))) (p := liftProg r p) hcond h1 h2
    rw [write_overwrite] at hs
    simpa only [liftProg] using hs

/-- Port lifting leaves every stack outside the embedding unchanged. -/
theorem lift_exec_preserves_other_ports {K L A : Type} (r : K ↪ L) {p : StackProg K A}
    {s t : K → List A} {n : ℕ} (h : p.Exec s t n) (base : L → List A)
    (hb : project r base = s) {l : L} (hout : ∀ k, r k ≠ l) :
    (liftProg r p).Exec base (write r t base) n ∧ write r t base l = base l :=
  ⟨lift_exec r h base hb, write_outside r t base hout⟩



/-- Compose source programs with different local port types on one shared
    global store. The compatibility hypothesis states the exact second
    program input after the first program writes its embedded ports. -/
theorem lift_seq_exec {K J L A : Type} (r : K ↪ L) (q : J ↪ L)
    {p : StackProg K A} {pIn pOut : K → List A} {np : ℕ} (hp : p.Exec pIn pOut np)
    {z : StackProg J A} {zIn zOut : J → List A} {nz : ℕ} (hz : z.Exec zIn zOut nz)
    (base : L → List A) (hbase : project r base = pIn)
    (hcompat : project q (write r pOut base) = zIn) :
    (StackProg.seq (liftProg r p) (liftProg q z)).Exec base
      (write q zOut (write r pOut base)) (np + 1 + nz) :=
  StackProg.Exec.seq (lift_exec r hp base hbase)
    (lift_exec q hz (write r pOut base) hcompat)

theorem liftActC_eq_liftAct {K L A : Type} (r : K ↪ L) (decode : L → Option K)
    (hdecode : ∀ l k, decode l = some k ↔ r k = l)
    (f : (K → Option A) → K → StackAct A) : liftActC r decode f = liftAct r f := by
  classical
  funext h l
  cases hd : decode l with
  | none =>
    have hn : ¬ ∃ k, r k = l := by
      rintro ⟨k, hk⟩
      have hs := (hdecode l k).2 hk
      rw [hd] at hs
      contradiction
    simp [liftActC, liftAct, hd, hn]
  | some k =>
    have hk : r k = l := (hdecode l k).1 hd
    subst l
    simp only [liftActC, hd, liftAct_at]

/-- A verified explicit decoder gives exactly the general mathematical lift. -/
theorem liftProgC_eq_liftProg {K L A : Type} (r : K ↪ L) (decode : L → Option K)
    (hdecode : ∀ l k, decode l = some k ↔ r k = l) (p : StackProg K A) :
    liftProgC r decode p = liftProg r p := by
  induction p with
  | act f => simp only [liftProgC, liftProg, liftActC_eq_liftAct r decode hdecode]
  | seq p q hp hq => simp only [liftProgC, liftProg, hp, hq]
  | branch test p q hp hq => simp only [liftProgC, liftProg, hp, hq]
  | loop test p hp => simp only [liftProgC, liftProg, hp]


end StackProgPortLift

open StackProgPortLift

/-- The computable port lift preserves executions and their exact source-step count. -/
theorem solution {K L A : Type} (r : K ↪ L) (decode : L → Option K)
    (hdecode : ∀ l k, decode l = some k ↔ r k = l)
    {p : StackProg K A} {s t : K → List A} {n : ℕ} (h : p.Exec s t n)
    (base : L → List A) (hb : project r base = s) :
    (liftProgC r decode p).Exec base (write r t base) n := by
  rw [liftProgC_eq_liftProg r decode hdecode]
  exact lift_exec r h base hb
