-- Prove2me | solution 1 for TensorNP.Eigen.graphCode_recognizer_polytime
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:47:24.232207+00:00
-- url     : https://prove2.me/submissions/6db54254-2b58-4e24-bb91-4c7aaa264288

import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_stack_transfer
import Definitions.Def_TensorNP_Eigen_Defs
import Definitions.Def_CookPvsNP_StackMacros
import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Mathlib
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Theorems.Thm_CookPvsNP_stack_copy

namespace TensorGraphRecognizerInternal

open CookPvsNP

namespace StackProgPortLift

/-- Project a larger stack store to the ports selected by an embedding. -/
def project {K L A : Type} (r : K ↪ L) (s : L → List A) : K → List A :=
  fun k ↦ s (r k)

/-- Replace exactly the embedded ports, leaving all other stack contents intact. -/
noncomputable def write {K L A : Type} (r : K ↪ L) (t : K → List A)
    (s : L → List A) : L → List A := by
  classical
  exact fun l ↦ if h : ∃ k, r k = l then t (Classical.choose h) else s l

/-- Lift one action, projecting read heads and keeping every unselected port. -/
noncomputable def liftAct {K L A : Type} (r : K ↪ L)
    (f : (K → Option A) → K → StackAct A) : (L → Option A) → L → StackAct A := by
  classical
  exact fun h l ↦ if hex : ∃ k, r k = l then f (fun k ↦ h (r k)) (Classical.choose hex) else .keep

/-- Lift a structured stack program along an injective port map. -/
noncomputable def liftProg {K L A : Type} (r : K ↪ L) : StackProg K A → StackProg L A
  | .act f => .act (liftAct r f)
  | .seq p q => .seq (liftProg r p) (liftProg r q)
  | .branch test p q => .branch (fun h ↦ test (fun k ↦ h (r k))) (liftProg r p) (liftProg r q)
  | .loop test p => .loop (fun h ↦ test (fun k ↦ h (r k))) (liftProg r p)

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

end StackProgPortLift
namespace StackProgPortLift

/-- Computable action lift when an explicit port decoder is supplied. -/
def liftActC {K L A : Type} (r : K ↪ L) (decode : L → Option K)
    (f : (K → Option A) → K → StackAct A) : (L → Option A) → L → StackAct A :=
  fun h l ↦ match decode l with
    | none => .keep
    | some k => f (fun j ↦ h (r j)) k

/-- Computable program lift when an explicit port decoder is supplied. -/
def liftProgC {K L A : Type} (r : K ↪ L) (decode : L → Option K) :
    StackProg K A → StackProg L A
  | .act f => .act (liftActC r decode f)
  | .seq p q => .seq (liftProgC r decode p) (liftProgC r decode q)
  | .branch test p q => .branch (fun h ↦ test (fun k ↦ h (r k))) (liftProgC r decode p) (liftProgC r decode q)
  | .loop test p => .loop (fun h ↦ test (fun k ↦ h (r k))) (liftProgC r decode p)

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



open CookPvsNP ProjSchedTW.Complexity

namespace TensorBoundedUnaryAdd

/-- The four ports are source, destination, remaining capacity, and status. -/
private def store4 (src dst cap status : List BSym) : Fin 4 → List BSym :=
  fun k ↦ if k = 0 then src else if k = 1 then dst else if k = 2 then cap else status

private def canTransfer (h : Fin 4 → Option BSym) : Bool :=
  (h 0).isSome && (h 2).isSome

private def transferAct (_h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 0 then .pop else if k = 1 then .push .one else if k = 2 then .pop else .keep

/-- Transfer unary tokens until either the source or the fuel is exhausted. -/
def boundedTransferProg : StackProg (Fin 4) BSym := .loop canTransfer (.act transferAct)

private theorem transfer_step (n m d : ℕ) (status : List BSym) :
    StackProg.applyAct transferAct
      (store4 (List.replicate (n+1) .one) (List.replicate d .one)
        (List.replicate (m+1) .one) status) =
    store4 (List.replicate n .one) (List.replicate (d+1) .one)
      (List.replicate m .one) status := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, transferAct, store4, StackAct.apply, List.replicate_succ]

/-- For any number k of available matching source and fuel tokens, the loop
    transfers exactly k provided one residual stack is empty. -/
theorem boundedTransfer_exec (k a b d : ℕ) (status : List BSym) (hstop : a = 0 ∨ b = 0) :
    boundedTransferProg.Exec
      (store4 (List.replicate (k+a) .one) (List.replicate d .one)
        (List.replicate (k+b) .one) status)
      (store4 (List.replicate a .one) (List.replicate (k+d) .one)
        (List.replicate b .one) status) (3*k+1) := by
  induction k generalizing d with
  | zero =>
    have ht : canTransfer (fun j ↦
        (store4 (List.replicate a .one) (List.replicate d .one)
          (List.replicate b .one) status j).head?) = false := by
      rcases hstop with rfl | rfl <;> simp [canTransfer, store4]
    simpa [boundedTransferProg] using
      (StackProg.Exec.loopFalse (test := canTransfer) (p := .act transferAct) ht)
  | succ k ih =>
    have ht : canTransfer (fun j ↦
        (store4 (List.replicate (k+a+1) .one) (List.replicate d .one)
          (List.replicate (k+b+1) .one) status j).head?) = true := by
      simp [canTransfer, store4, List.replicate_succ]
    have ha : (StackProg.act transferAct).Exec
        (store4 (List.replicate (k+a+1) .one) (List.replicate d .one)
          (List.replicate (k+b+1) .one) status)
        (store4 (List.replicate (k+a) .one) (List.replicate (d+1) .one)
          (List.replicate (k+b) .one) status) 1 := by
      simpa only [transfer_step] using
        (StackProg.Exec.act transferAct
          (store4 (List.replicate (k+a+1) .one) (List.replicate d .one)
            (List.replicate (k+b+1) .one) status))
    have h := StackProg.Exec.loopTrue ht ha (ih (d+1))
    have hsrc : (k+1)+a = k+a+1 := by omega
    have hcap : (k+1)+b = k+b+1 := by omega
    have hdst : k+(d+1) = (k+1)+d := by omega
    have htime : 1+1+1+(3*k+1) = 3*(k+1)+1 := by omega
    change (StackProg.loop canTransfer (.act transferAct)).Exec
      (store4 (List.replicate ((k+1)+a) .one) (List.replicate d .one)
        (List.replicate ((k+1)+b) .one) status)
      (store4 (List.replicate a .one) (List.replicate ((k+1)+d) .one)
        (List.replicate b .one) status) (3*(k+1)+1)
    rw [hsrc, hcap, ← hdst, ← htime]
    exact h

/-- With sufficient capacity, all source tokens are added to the destination. -/
theorem boundedTransfer_success (n spare d : ℕ) (status : List BSym) :
    boundedTransferProg.Exec
      (store4 (List.replicate n .one) (List.replicate d .one)
        (List.replicate (n+spare) .one) status)
      (store4 [] (List.replicate (n+d) .one) (List.replicate spare .one) status)
      (3*n+1) := by
  simpa using boundedTransfer_exec n 0 spare d status (Or.inl rfl)

/-- When capacity runs out first, the loop stops with a nonempty source.
    This residual source is an explicit over-cap signal for the next branch. -/
theorem boundedTransfer_exhausted (fuel extra d : ℕ) (status : List BSym) :
    boundedTransferProg.Exec
      (store4 (List.replicate (fuel+(extra+1)) .one) (List.replicate d .one)
        (List.replicate fuel .one) status)
      (store4 (List.replicate (extra+1) .one) (List.replicate (fuel+d) .one) [] status)
      (3*fuel+1) := by
  simpa using boundedTransfer_exec fuel (extra+1) 0 d status (Or.inr rfl)

end TensorBoundedUnaryAdd

namespace TensorBoundedDouble

open StackProgPortLift TensorBoundedUnaryAdd

/-- Source number, temporary copy, remaining fuel, scratch, status. -/
def store5 (src copy fuel scratch status : List BSym) : Fin 5 → List BSym :=
  fun k ↦ if k = 0 then src else if k = 1 then copy else if k = 2 then fuel
    else if k = 3 then scratch else status

def addPorts : Fin 4 ↪ Fin 5 := ⟨![1, 0, 2, 4], by decide⟩
def addDecode : Fin 5 → Option (Fin 4) := ![some 1, some 0, some 2, none, some 3]

private theorem addDecode_correct (l : Fin 5) (k : Fin 4) :
    addDecode l = some k ↔ addPorts k = l := by
  fin_cases l <;> fin_cases k <;> decide

/-- Copy the number, then spend one unit of fuel per added unary token. -/
def boundedDoubleProg : StackProg (Fin 5) BSym :=
  .seq (copyProg 0 1 3) (liftProgC addPorts addDecode boundedTransferProg)

/-- When the fuel contains n+spare tokens, double n within that cap. -/
theorem boundedDouble_success (n spare : ℕ) (status : List BSym) :
    boundedDoubleProg.Exec
      (store5 (List.replicate n .one) [] (List.replicate (n+spare) .one) [] status)
      (write addPorts
        (TensorBoundedUnaryAdd.store4 [] (List.replicate (n+n) .one)
          (List.replicate spare .one) status)
        (store5 (List.replicate n .one) (List.replicate n .one)
          (List.replicate (n+spare) .one) [] status)) (9*n+5) := by
  classical
  let s := store5 (List.replicate n .one) [] (List.replicate (n+spare) .one) [] status
  let m := store5 (List.replicate n .one) (List.replicate n .one)
    (List.replicate (n+spare) .one) [] status
  have he : s 3 = [] := by simp [s, store5]
  have hmid : Function.update s 1 (s 0 ++ s 1) = m := by
    funext k
    fin_cases k <;> simp [s, m, store5, Function.update]
  have hc : (copyProg (0 : Fin 5) 1 3).Exec s m (6*n+3) := by
    have h := stack_copy (0 : Fin 5) 1 3 (by decide) (by decide) (by decide) s he
    rw [hmid] at h
    simpa [s, store5] using h
  have hproject : project addPorts m =
      TensorBoundedUnaryAdd.store4 (List.replicate n .one) (List.replicate n .one)
        (List.replicate (n+spare) .one) status := by
    funext k
    fin_cases k <;> simp [project, addPorts, m, store5, TensorBoundedUnaryAdd.store4]
  have ha := lift_exec addPorts (boundedTransfer_success n spare n status) m hproject
  have h := StackProg.Exec.seq hc ha
  have htime : (6*n+3)+1+(3*n+1) = 9*n+5 := by omega
  rw [← htime]
  simpa only [boundedDoubleProg, liftProgC_eq_liftProg addPorts addDecode addDecode_correct,
    s, m] using h

/-- With fewer than n fuel tokens, doubling stops as soon as the budget is
    empty and leaves a nonempty copy as an explicit over-cap signal. -/
theorem boundedDouble_exhausted (fuel extra : ℕ) (status : List BSym) :
    boundedDoubleProg.Exec
      (store5 (List.replicate (fuel+(extra+1)) .one) [] (List.replicate fuel .one) [] status)
      (write addPorts
        (TensorBoundedUnaryAdd.store4 (List.replicate (extra+1) .one)
          (List.replicate (fuel+(fuel+(extra+1))) .one) [] status)
        (store5 (List.replicate (fuel+(extra+1)) .one)
          (List.replicate (fuel+(extra+1)) .one) (List.replicate fuel .one) [] status))
      ((6*(fuel+(extra+1))+3)+1+(3*fuel+1)) := by
  classical
  let n := fuel+(extra+1)
  let s := store5 (List.replicate n .one) [] (List.replicate fuel .one) [] status
  let m := store5 (List.replicate n .one) (List.replicate n .one)
    (List.replicate fuel .one) [] status
  have he : s 3 = [] := by simp [s, store5]
  have hmid : Function.update s 1 (s 0 ++ s 1) = m := by
    funext k
    fin_cases k <;> simp [s, m, store5, Function.update]
  have hc : (copyProg (0 : Fin 5) 1 3).Exec s m (6*n+3) := by
    have h := stack_copy (0 : Fin 5) 1 3 (by decide) (by decide) (by decide) s he
    rw [hmid] at h
    simpa [s, store5] using h
  have hproject : project addPorts m =
      TensorBoundedUnaryAdd.store4 (List.replicate (fuel+(extra+1)) .one) (List.replicate n .one)
        (List.replicate fuel .one) status := by
    funext k
    fin_cases k <;> simp [project, addPorts, m, n, store5, TensorBoundedUnaryAdd.store4]
  have ha := lift_exec addPorts (boundedTransfer_exhausted fuel extra n status) m hproject
  have h := StackProg.Exec.seq hc ha
  simpa only [boundedDoubleProg, liftProgC_eq_liftProg addPorts addDecode addDecode_correct,
    s, m, n] using h

end TensorBoundedDouble


open CookPvsNP ProjSchedTW.Complexity

namespace TensorBoundedBit

/-- Remaining binary digits, unary value, remaining unary fuel, status. -/
private def store4 (bits value fuel status : List BSym) : Fin 4 → List BSym :=
  fun k ↦ if k = 0 then bits else if k = 1 then value else if k = 2 then fuel else status

private def isZero (h : Fin 4 → Option BSym) : Bool := h 0 == some BSym.zero
private def isOne (h : Fin 4 → Option BSym) : Bool := h 0 == some BSym.one
private def hasFuel (h : Fin 4 → Option BSym) : Bool := h 2 == some BSym.one

private def zeroAct (_h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 0 then .pop else .keep
private def oneAct (_h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 0 then .pop else if k = 1 then .push .one else if k = 2 then .pop else .keep
private def rejectAct (_h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 3 then .push .zero else .keep

/-- Read one bit, spending one fuel token if the bit is one; mark exhaustion
    and all non-bit heads as failures. -/
def boundedBitProg : StackProg (Fin 4) BSym :=
  .branch isZero (.act zeroAct)
    (.branch isOne (.branch hasFuel (.act oneAct) (.act rejectAct)) (.act rejectAct))

private theorem zero_step (tail value fuel status : List BSym) :
    StackProg.applyAct zeroAct (store4 (.zero :: tail) value fuel status) =
      store4 tail value fuel status := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, zeroAct, store4, StackAct.apply]

private theorem one_step (tail value fuel status : List BSym) :
    StackProg.applyAct oneAct (store4 (.one :: tail) value (.one :: fuel) status) =
      store4 tail (.one :: value) fuel status := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, oneAct, store4, StackAct.apply]

private theorem reject_step (bits value fuel status : List BSym) :
    StackProg.applyAct rejectAct (store4 bits value fuel status) =
      store4 bits value fuel (.zero :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, rejectAct, store4, StackAct.apply]

/-- A zero bit consumes no fuel and leaves the unary value unchanged. -/
theorem boundedBit_zero (tail value fuel status : List BSym) :
    boundedBitProg.Exec (store4 (.zero :: tail) value fuel status)
      (store4 tail value fuel status) 2 := by
  have ha : (StackProg.act zeroAct).Exec (store4 (.zero :: tail) value fuel status)
      (store4 tail value fuel status) 1 := by
    simpa only [zero_step] using (StackProg.Exec.act zeroAct (store4 (.zero :: tail) value fuel status))
  exact StackProg.Exec.branchTrue (by rfl) ha

/-- A one bit increments the value and spends exactly one fuel token. -/
theorem boundedBit_one (tail value fuel status : List BSym) :
    boundedBitProg.Exec (store4 (.one :: tail) value (.one :: fuel) status)
      (store4 tail (.one :: value) fuel status) 4 := by
  have ha : (StackProg.act oneAct).Exec (store4 (.one :: tail) value (.one :: fuel) status)
      (store4 tail (.one :: value) fuel status) 1 := by
    simpa only [one_step] using (StackProg.Exec.act oneAct (store4 (.one :: tail) value (.one :: fuel) status))
  have hf := StackProg.Exec.branchTrue (q := .act rejectAct)
    (by rfl : hasFuel (fun k ↦ (store4 (.one :: tail) value (.one :: fuel) status k).head?) = true) ha
  have ho := StackProg.Exec.branchTrue (q := .act rejectAct)
    (by rfl : isOne (fun k ↦ (store4 (.one :: tail) value (.one :: fuel) status k).head?) = true) hf
  exact StackProg.Exec.branchFalse (by rfl) ho

/-- A one bit with no fuel produces the failure marker without incrementing. -/
theorem boundedBit_exhausted (tail value status : List BSym) :
    boundedBitProg.Exec (store4 (.one :: tail) value [] status)
      (store4 (.one :: tail) value [] (.zero :: status)) 4 := by
  have ha : (StackProg.act rejectAct).Exec (store4 (.one :: tail) value [] status)
      (store4 (.one :: tail) value [] (.zero :: status)) 1 := by
    simpa only [reject_step] using (StackProg.Exec.act rejectAct (store4 (.one :: tail) value [] status))
  have hf := StackProg.Exec.branchFalse (p := .act oneAct)
    (by rfl : hasFuel (fun k ↦ (store4 (.one :: tail) value [] status k).head?) = false) ha
  have ho := StackProg.Exec.branchTrue (q := .act rejectAct)
    (by rfl : isOne (fun k ↦ (store4 (.one :: tail) value [] status k).head?) = true) hf
  exact StackProg.Exec.branchFalse (by rfl) ho

end TensorBoundedBit

namespace TensorCappedDecode

open StackProgPortLift TensorBoundedDouble TensorBoundedBit

/-- Bits, unary value, doubling copy, remaining fuel, scratch and status. -/
def store6 (bits value copy fuel scratch status : List BSym) : Fin 6 → List BSym :=
  fun k ↦ if k = 0 then bits else if k = 1 then value else if k = 2 then copy
    else if k = 3 then fuel else if k = 4 then scratch else status

def doublePorts : Fin 5 ↪ Fin 6 := ⟨![1,2,3,4,5], by decide⟩
def doubleDecode : Fin 6 → Option (Fin 5) := ![none,some 0,some 1,some 2,some 3,some 4]
def bitPorts : Fin 4 ↪ Fin 6 := ⟨![0,1,3,5], by decide⟩
def bitDecode : Fin 6 → Option (Fin 4) := ![some 0,some 1,none,some 2,none,some 3]

private theorem doubleDecode_correct (l : Fin 6) (k : Fin 5) :
    doubleDecode l = some k ↔ doublePorts k = l := by
  fin_cases l <;> fin_cases k <;> decide
private theorem bitDecode_correct (l : Fin 6) (k : Fin 4) :
    bitDecode l = some k ↔ bitPorts k = l := by
  fin_cases l <;> fin_cases k <;> decide

private def copyEmpty (h : Fin 6 → Option BSym) : Bool := (h 2).isNone
private def rejectAct (_h : Fin 6 → Option BSym) (k : Fin 6) : StackAct BSym :=
  if k = 5 then .push .zero else .keep
private def shouldLoop (h : Fin 6 → Option BSym) : Bool :=
  (h 0).isSome && (h 5 == some BSym.one)

/-- Double under the fuel cap; only process the bit if doubling succeeded. -/
def cappedDigitProg : StackProg (Fin 6) BSym :=
  .seq (liftProgC doublePorts doubleDecode boundedDoubleProg)
    (.branch copyEmpty (liftProgC bitPorts bitDecode boundedBitProg) (.act rejectAct))

/-- Process digits until the input is exhausted or a failure marker is set. -/
def cappedDecodeProg : StackProg (Fin 6) BSym := .loop shouldLoop cappedDigitProg

private theorem write_add (a b c d x y z t u : List BSym) :
    write TensorBoundedDouble.addPorts (TensorBoundedUnaryAdd.store4 a b c d)
      (TensorBoundedDouble.store5 x y z t u) = TensorBoundedDouble.store5 b a c t d := by
  funext k
  fin_cases k
  · simpa [TensorBoundedDouble.addPorts, TensorBoundedUnaryAdd.store4, TensorBoundedDouble.store5] using
      (StackProgPortLift.write_at TensorBoundedDouble.addPorts (TensorBoundedUnaryAdd.store4 a b c d)
        (TensorBoundedDouble.store5 x y z t u) (1 : Fin 4))
  · simpa [TensorBoundedDouble.addPorts, TensorBoundedUnaryAdd.store4, TensorBoundedDouble.store5] using
      (StackProgPortLift.write_at TensorBoundedDouble.addPorts (TensorBoundedUnaryAdd.store4 a b c d)
        (TensorBoundedDouble.store5 x y z t u) (0 : Fin 4))
  · simpa [TensorBoundedDouble.addPorts, TensorBoundedUnaryAdd.store4, TensorBoundedDouble.store5] using
      (StackProgPortLift.write_at TensorBoundedDouble.addPorts (TensorBoundedUnaryAdd.store4 a b c d)
        (TensorBoundedDouble.store5 x y z t u) (2 : Fin 4))
  · have ho : ∀ j : Fin 4, TensorBoundedDouble.addPorts j ≠ (3 : Fin 5) := by
      intro j; fin_cases j <;> decide
    simpa [TensorBoundedDouble.store5] using
      (StackProgPortLift.write_outside TensorBoundedDouble.addPorts (TensorBoundedUnaryAdd.store4 a b c d)
        (TensorBoundedDouble.store5 x y z t u) ho)
  · simpa [TensorBoundedDouble.addPorts, TensorBoundedUnaryAdd.store4, TensorBoundedDouble.store5] using
      (StackProgPortLift.write_at TensorBoundedDouble.addPorts (TensorBoundedUnaryAdd.store4 a b c d)
        (TensorBoundedDouble.store5 x y z t u) (3 : Fin 4))

private theorem write_double (a b c d e i v q f t s : List BSym) :
    write doublePorts (TensorBoundedDouble.store5 a b c d e) (store6 i v q f t s) =
      store6 i a b c d e := by
  funext k
  fin_cases k
  · have ho : ∀ j : Fin 5, doublePorts j ≠ (0 : Fin 6) := by
      intro j; fin_cases j <;> decide
    simpa [store6] using
      (StackProgPortLift.write_outside doublePorts (TensorBoundedDouble.store5 a b c d e)
        (store6 i v q f t s) ho)
  · simpa [doublePorts, TensorBoundedDouble.store5, store6] using
      (StackProgPortLift.write_at doublePorts (TensorBoundedDouble.store5 a b c d e) (store6 i v q f t s) (0 : Fin 5))
  · simpa [doublePorts, TensorBoundedDouble.store5, store6] using
      (StackProgPortLift.write_at doublePorts (TensorBoundedDouble.store5 a b c d e) (store6 i v q f t s) (1 : Fin 5))
  · simpa [doublePorts, TensorBoundedDouble.store5, store6] using
      (StackProgPortLift.write_at doublePorts (TensorBoundedDouble.store5 a b c d e) (store6 i v q f t s) (2 : Fin 5))
  · simpa [doublePorts, TensorBoundedDouble.store5, store6] using
      (StackProgPortLift.write_at doublePorts (TensorBoundedDouble.store5 a b c d e) (store6 i v q f t s) (3 : Fin 5))
  · simpa [doublePorts, TensorBoundedDouble.store5, store6] using
      (StackProgPortLift.write_at doublePorts (TensorBoundedDouble.store5 a b c d e) (store6 i v q f t s) (4 : Fin 5))

private theorem write_bit (a b c d i v q f t s : List BSym) :
    write bitPorts (TensorBoundedBit.store4 a b c d) (store6 i v q f t s) =
      store6 a b q c t d := by
  funext k
  fin_cases k
  · simpa [bitPorts, TensorBoundedBit.store4, store6] using
      (StackProgPortLift.write_at bitPorts (TensorBoundedBit.store4 a b c d) (store6 i v q f t s) (0 : Fin 4))
  · simpa [bitPorts, TensorBoundedBit.store4, store6] using
      (StackProgPortLift.write_at bitPorts (TensorBoundedBit.store4 a b c d) (store6 i v q f t s) (1 : Fin 4))
  · have ho : ∀ j : Fin 4, bitPorts j ≠ (2 : Fin 6) := by
      intro j; fin_cases j <;> decide
    simpa [store6] using (StackProgPortLift.write_outside bitPorts (TensorBoundedBit.store4 a b c d) (store6 i v q f t s) ho)
  · simpa [bitPorts, TensorBoundedBit.store4, store6] using
      (StackProgPortLift.write_at bitPorts (TensorBoundedBit.store4 a b c d) (store6 i v q f t s) (2 : Fin 4))
  · have ho : ∀ j : Fin 4, bitPorts j ≠ (4 : Fin 6) := by
      intro j; fin_cases j <;> decide
    simpa [store6] using (StackProgPortLift.write_outside bitPorts (TensorBoundedBit.store4 a b c d) (store6 i v q f t s) ho)
  · simpa [bitPorts, TensorBoundedBit.store4, store6] using
      (StackProgPortLift.write_at bitPorts (TensorBoundedBit.store4 a b c d) (store6 i v q f t s) (3 : Fin 4))

private theorem reject_step (bits value copy fuel scratch status : List BSym) :
    StackProg.applyAct rejectAct (store6 bits value copy fuel scratch status) =
      store6 bits value copy fuel scratch (.zero :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, rejectAct, store6, StackAct.apply]

private theorem double_exec6 (bits a b c d e a' b' c' d' e' : List BSym) (steps : ℕ)
    (h : boundedDoubleProg.Exec (TensorBoundedDouble.store5 a b c d e)
      (TensorBoundedDouble.store5 a' b' c' d' e') steps) :
    (liftProgC doublePorts doubleDecode boundedDoubleProg).Exec
      (store6 bits a b c d e) (store6 bits a' b' c' d' e') steps := by
  have hp : project doublePorts (store6 bits a b c d e) = TensorBoundedDouble.store5 a b c d e := by
    funext k
    fin_cases k <;> simp [project, doublePorts, store6, TensorBoundedDouble.store5]
  have hr := lift_exec doublePorts h (store6 bits a b c d e) hp
  rw [write_double] at hr
  simpa only [liftProgC_eq_liftProg doublePorts doubleDecode doubleDecode_correct] using hr

private theorem bit_exec6 (bits value copy fuel scratch status bits' value' fuel' status' : List BSym)
    (steps : ℕ) (h : boundedBitProg.Exec (TensorBoundedBit.store4 bits value fuel status)
      (TensorBoundedBit.store4 bits' value' fuel' status') steps) :
    (liftProgC bitPorts bitDecode boundedBitProg).Exec
      (store6 bits value copy fuel scratch status) (store6 bits' value' copy fuel' scratch status') steps := by
  have hp : project bitPorts (store6 bits value copy fuel scratch status) =
      TensorBoundedBit.store4 bits value fuel status := by
    funext k
    fin_cases k <;> simp [project, bitPorts, store6, TensorBoundedBit.store4]
  have hr := lift_exec bitPorts h (store6 bits value copy fuel scratch status) hp
  rw [write_bit] at hr
  simpa only [liftProgC_eq_liftProg bitPorts bitDecode bitDecode_correct] using hr

/-- With spare fuel, processing a zero digit doubles the unary value. -/
theorem cappedDigit_zero (tail : List BSym) (n spare : ℕ) (status : List BSym) :
    cappedDigitProg.Exec
      (store6 (.zero :: tail) (List.replicate n .one) [] (List.replicate (n+spare) .one) [] status)
      (store6 tail (List.replicate (n+n) .one) [] (List.replicate spare .one) [] status)
      (9*n+9) := by
  have hd0 : boundedDoubleProg.Exec
      (TensorBoundedDouble.store5 (List.replicate n .one) [] (List.replicate (n+spare) .one) [] status)
      (TensorBoundedDouble.store5 (List.replicate (n+n) .one) [] (List.replicate spare .one) [] status)
      (9*n+5) := by simpa only [write_add] using boundedDouble_success n spare status
  have hd := double_exec6 (.zero :: tail) _ _ _ _ _ _ _ _ _ _ _ hd0
  have hb := bit_exec6 (.zero :: tail) (List.replicate (n+n) .one) []
    (List.replicate spare .one) [] status tail (List.replicate (n+n) .one)
    (List.replicate spare .one) status 2 (boundedBit_zero tail _ _ status)
  have hc := StackProg.Exec.branchTrue (q := .act rejectAct)
    (by rfl : copyEmpty (fun k ↦ (store6 (.zero :: tail) (List.replicate (n+n) .one) []
      (List.replicate spare .one) [] status k).head?) = true) hb
  have he := StackProg.Exec.seq hd hc
  have ht : (9*n+5)+1+(1+2) = 9*n+9 := by omega
  rw [← ht]
  exact he

/-- With one extra fuel token, a one digit doubles and increments. -/
theorem cappedDigit_one (tail : List BSym) (n spare : ℕ) (status : List BSym) :
    cappedDigitProg.Exec
      (store6 (.one :: tail) (List.replicate n .one) [] (List.replicate (n+(spare+1)) .one) [] status)
      (store6 tail (List.replicate (n+n+1) .one) [] (List.replicate spare .one) [] status)
      (9*n+11) := by
  have hd0 : boundedDoubleProg.Exec
      (TensorBoundedDouble.store5 (List.replicate n .one) [] (List.replicate (n+(spare+1)) .one) [] status)
      (TensorBoundedDouble.store5 (List.replicate (n+n) .one) [] (List.replicate (spare+1) .one) [] status)
      (9*n+5) := by simpa only [write_add] using boundedDouble_success n (spare+1) status
  have hd := double_exec6 (.one :: tail) _ _ _ _ _ _ _ _ _ _ _ hd0
  have hb := bit_exec6 (.one :: tail) (List.replicate (n+n) .one) []
    (BSym.one :: List.replicate spare .one) [] status tail
    (BSym.one :: List.replicate (n+n) .one) (List.replicate spare .one) status 4
    (boundedBit_one tail _ _ status)
  have hc := StackProg.Exec.branchTrue (q := .act rejectAct)
    (by rfl : copyEmpty (fun k ↦ (store6 (.one :: tail) (List.replicate (n+n) .one) []
      (List.replicate (spare+1) .one) [] status k).head?) = true) (by
        simpa only [List.replicate_succ] using hb)
  have he := StackProg.Exec.seq hd hc
  have ht : (9*n+5)+1+(1+4) = 9*n+11 := by omega
  rw [← ht]
  simpa only [cappedDigitProg, List.replicate_succ] using he

/-- If doubling fits but the one digit cannot be added, mark exhaustion. -/
theorem cappedDigit_one_exhausted (tail : List BSym) (n : ℕ) (status : List BSym) :
    cappedDigitProg.Exec
      (store6 (.one :: tail) (List.replicate n .one) [] (List.replicate n .one) [] status)
      (store6 (.one :: tail) (List.replicate (n+n) .one) [] [] [] (.zero :: status))
      (9*n+11) := by
  have hd0 : boundedDoubleProg.Exec
      (TensorBoundedDouble.store5 (List.replicate n .one) [] (List.replicate (n+0) .one) [] status)
      (TensorBoundedDouble.store5 (List.replicate (n+n) .one) [] [] [] status) (9*n+5) := by
    simpa only [write_add, List.replicate_zero] using boundedDouble_success n 0 status
  have hd := double_exec6 (.one :: tail) _ _ _ _ _ _ _ _ _ _ _ hd0
  have hb := bit_exec6 (.one :: tail) (List.replicate (n+n) .one) [] [] [] status
    (.one :: tail) (List.replicate (n+n) .one) [] (.zero :: status) 4
    (boundedBit_exhausted tail _ status)
  have hc := StackProg.Exec.branchTrue (q := .act rejectAct)
    (by rfl : copyEmpty (fun k ↦ (store6 (.one :: tail) (List.replicate (n+n) .one) [] [] [] status k).head?) = true) hb
  have he := StackProg.Exec.seq hd hc
  have ht : (9*n+5)+1+(1+4) = 9*n+11 := by omega
  rw [← ht]
  simpa only [cappedDigitProg, Nat.add_zero] using he

/-- If doubling exhausts fuel, set failure before attempting the bit. -/
theorem cappedDigit_double_exhausted (bits : List BSym) (fuel extra : ℕ) (status : List BSym) :
    cappedDigitProg.Exec
      (store6 bits (List.replicate (fuel+(extra+1)) .one) [] (List.replicate fuel .one) [] status)
      (store6 bits (List.replicate (fuel+(fuel+(extra+1))) .one)
        (List.replicate (extra+1) .one) [] [] (.zero :: status))
      (((6*(fuel+(extra+1))+3)+1+(3*fuel+1))+1+2) := by
  have hd0 : boundedDoubleProg.Exec
      (TensorBoundedDouble.store5 (List.replicate (fuel+(extra+1)) .one) [] (List.replicate fuel .one) [] status)
      (TensorBoundedDouble.store5 (List.replicate (fuel+(fuel+(extra+1))) .one)
        (List.replicate (extra+1) .one) [] [] status)
      ((6*(fuel+(extra+1))+3)+1+(3*fuel+1)) := by
    simpa only [write_add] using boundedDouble_exhausted fuel extra status
  have hd := double_exec6 bits _ _ _ _ _ _ _ _ _ _ _ hd0
  have ha : (StackProg.act rejectAct).Exec
      (store6 bits (List.replicate (fuel+(fuel+(extra+1))) .one) (List.replicate (extra+1) .one) [] [] status)
      (store6 bits (List.replicate (fuel+(fuel+(extra+1))) .one) (List.replicate (extra+1) .one) [] [] (.zero :: status)) 1 := by
    simpa only [reject_step] using StackProg.Exec.act rejectAct
      (store6 bits (List.replicate (fuel+(fuel+(extra+1))) .one) (List.replicate (extra+1) .one) [] [] status)
  have hc := StackProg.Exec.branchFalse (test := copyEmpty) (p := liftProgC bitPorts bitDecode boundedBitProg)
    (by simp [copyEmpty, store6, List.replicate_succ]) ha
  exact StackProg.Exec.seq hd hc

private theorem boundedBit_bad (a : BSym) (tail value fuel status : List BSym)
    (hz : TensorBoundedBit.isZero (fun k ↦ (TensorBoundedBit.store4 (a :: tail) value fuel status k).head?) = false)
    (ho : TensorBoundedBit.isOne (fun k ↦ (TensorBoundedBit.store4 (a :: tail) value fuel status k).head?) = false) :
    boundedBitProg.Exec (TensorBoundedBit.store4 (a :: tail) value fuel status)
      (TensorBoundedBit.store4 (a :: tail) value fuel (.zero :: status)) 3 := by
  have ha : (StackProg.act TensorBoundedBit.rejectAct).Exec
      (TensorBoundedBit.store4 (a :: tail) value fuel status)
      (TensorBoundedBit.store4 (a :: tail) value fuel (.zero :: status)) 1 := by
    simpa only [TensorBoundedBit.reject_step] using
      StackProg.Exec.act TensorBoundedBit.rejectAct (TensorBoundedBit.store4 (a :: tail) value fuel status)
  have hb := StackProg.Exec.branchFalse (p := .branch TensorBoundedBit.hasFuel
    (.act TensorBoundedBit.oneAct) (.act TensorBoundedBit.rejectAct)) ho ha
  exact StackProg.Exec.branchFalse hz hb

/-- A non-binary digit marks failure after the bounded doubling stage. -/
theorem cappedDigit_bad (a : BSym) (tail : List BSym) (n spare : ℕ) (status : List BSym)
    (hz : a ≠ .zero) (ho : a ≠ .one) :
    cappedDigitProg.Exec
      (store6 (a :: tail) (List.replicate n .one) [] (List.replicate (n+spare) .one) [] status)
      (store6 (a :: tail) (List.replicate (n+n) .one) [] (List.replicate spare .one) [] (.zero :: status))
      (9*n+10) := by
  have hd0 : boundedDoubleProg.Exec
      (TensorBoundedDouble.store5 (List.replicate n .one) [] (List.replicate (n+spare) .one) [] status)
      (TensorBoundedDouble.store5 (List.replicate (n+n) .one) [] (List.replicate spare .one) [] status)
      (9*n+5) := by simpa only [write_add] using boundedDouble_success n spare status
  have hd := double_exec6 (a :: tail) _ _ _ _ _ _ _ _ _ _ _ hd0
  have hzero : TensorBoundedBit.isZero (fun k ↦
      (TensorBoundedBit.store4 (a :: tail) (List.replicate (n+n) .one) (List.replicate spare .one) status k).head?) = false := by
    simp [TensorBoundedBit.isZero, TensorBoundedBit.store4, hz]
  have hone : TensorBoundedBit.isOne (fun k ↦
      (TensorBoundedBit.store4 (a :: tail) (List.replicate (n+n) .one) (List.replicate spare .one) status k).head?) = false := by
    simp [TensorBoundedBit.isOne, TensorBoundedBit.store4, ho]
  have hb := bit_exec6 (a :: tail) (List.replicate (n+n) .one) []
    (List.replicate spare .one) [] status (a :: tail) (List.replicate (n+n) .one)
    (List.replicate spare .one) (.zero :: status) 3 (boundedBit_bad a tail _ _ status hzero hone)
  have hc := StackProg.Exec.branchTrue (q := .act rejectAct)
    (by rfl : copyEmpty (fun k ↦ (store6 (a :: tail) (List.replicate (n+n) .one) []
      (List.replicate spare .one) [] status k).head?) = true) hb
  have he := StackProg.Exec.seq hd hc
  have ht : (9*n+5)+1+(1+3) = 9*n+10 := by omega
  rw [← ht]
  exact he

/-- Interpret a digit as the usual big-endian doubling-and-increment step. -/
def digitValue (n : ℕ) (a : BSym) : ℕ := n+n + if a = .one then 1 else 0

/-- Every single capped digit either consumes one bit while preserving the
    value-plus-fuel invariant, or records failure without exceeding the cap. -/
theorem cappedDigit_progress (a : BSym) (tail : List BSym) (n fuel : ℕ) (status : List BSym) :
    ∃ out steps,
      cappedDigitProg.Exec
        (store6 (a :: tail) (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: status)) out steps ∧
      steps ≤ 9*(n+fuel)+11 ∧
      ((∃ n' fuel', out = store6 tail (List.replicate n' .one) [] (List.replicate fuel' .one) [] (.one :: status) ∧
          n'+fuel'=n+fuel ∧ n' = digitValue n a) ∨
       (∃ bits' value' copy' fuel' scratch',
          out = store6 bits' value' copy' fuel' scratch' (.zero :: .one :: status))) := by
  by_cases hle : n ≤ fuel
  · let spare := fuel-n
    have hf : fuel = n+spare := by dsimp [spare]; omega
    by_cases hz : a = .zero
    · subst a
      refine ⟨store6 tail (List.replicate (n+n) .one) [] (List.replicate spare .one) [] (.one :: status),
        9*n+9, ?_, by omega, Or.inl ⟨n+n, spare, rfl, ?_, ?_⟩⟩
      · simpa only [hf] using cappedDigit_zero tail n spare (.one :: status)
      · omega
      · simp [digitValue]
    · by_cases ho : a = .one
      · subst a
        cases hs : spare with
        | zero =>
          have hf0 : fuel = n := by rw [hs] at hf; omega
          refine ⟨store6 (.one :: tail) (List.replicate (n+n) .one) [] [] [] (.zero :: .one :: status),
            9*n+11, ?_, by omega, Or.inr ⟨_, _, _, _, _, rfl⟩⟩
          simpa only [hf0] using cappedDigit_one_exhausted tail n (.one :: status)
        | succ spare =>
          have hf1 : fuel = n+(spare+1) := by rw [hs] at hf; omega
          refine ⟨store6 tail (List.replicate (n+n+1) .one) [] (List.replicate spare .one) [] (.one :: status),
            9*n+11, ?_, by omega, Or.inl ⟨n+n+1, spare, rfl, ?_, ?_⟩⟩
          · simpa only [hf1] using cappedDigit_one tail n spare (.one :: status)
          · omega
          · simp [digitValue]
      · refine ⟨store6 (a :: tail) (List.replicate (n+n) .one) [] (List.replicate spare .one) [] (.zero :: .one :: status),
          9*n+10, ?_, by omega, Or.inr ⟨_, _, _, _, _, rfl⟩⟩
        simpa only [hf] using cappedDigit_bad a tail n spare (.one :: status) hz ho
  · let extra := n-fuel-1
    have hn : n = fuel+(extra+1) := by dsimp [extra]; omega
    refine ⟨store6 (a :: tail) (List.replicate (fuel+(fuel+(extra+1))) .one)
        (List.replicate (extra+1) .one) [] [] (.zero :: .one :: status),
      ((6*(fuel+(extra+1))+3)+1+(3*fuel+1))+1+2, ?_, ?_, Or.inr ⟨_, _, _, _, _, rfl⟩⟩
    · simpa only [hn] using cappedDigit_double_exhausted (a :: tail) fuel extra (.one :: status)
    · omega

/-- The whole capped digit loop terminates on every symbol list. It either
    consumes all digits while preserving the cap invariant, or stops with a
    failure marker; its cost is bounded by the product of digit count and cap. -/
theorem cappedDecode_total (bits : List BSym) (n fuel : ℕ) (status : List BSym) :
    ∃ out steps,
      cappedDecodeProg.Exec
        (store6 bits (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: status)) out steps ∧
      steps ≤ (9*(n+fuel)+15)*bits.length+1 ∧
      ((∃ n' fuel', out = store6 [] (List.replicate n' .one) [] (List.replicate fuel' .one) [] (.one :: status) ∧
          n'+fuel'=n+fuel ∧ n' = bits.foldl digitValue n) ∨
       (∃ bits' value' copy' fuel' scratch',
          out = store6 bits' value' copy' fuel' scratch' (.zero :: .one :: status))) := by
  induction bits generalizing n fuel with
  | nil =>
    refine ⟨store6 [] (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: status),
      1, ?_, by simp, Or.inl ⟨n, fuel, rfl, rfl, rfl⟩⟩
    exact StackProg.Exec.loopFalse (by rfl)
  | cons a tail ih =>
    have ht : shouldLoop (fun k ↦
        (store6 (a :: tail) (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: status) k).head?) = true := by rfl
    obtain ⟨mid, cost, hdigit, hcost, hresult⟩ := cappedDigit_progress a tail n fuel status
    rcases hresult with ⟨n', fuel', rfl, hsum, hvalueStep⟩ | ⟨bits', value', copy', fuel', scratch', rfl⟩
    · obtain ⟨out, steps, hloop, hsteps, hout⟩ := ih n' fuel'
      have he := StackProg.Exec.loopTrue ht hdigit hloop
      refine ⟨out, 1+cost+1+steps, he, ?_, ?_⟩
      · rw [hsum] at hsteps
        simp only [List.length_cons, Nat.mul_succ]
        omega
      · rcases hout with ⟨n'', fuel'', rfl, hsum', hvalue⟩ | hfail
        · left
          refine ⟨n'', fuel'', rfl, ?_, ?_⟩
          · omega
          · simp only [List.foldl_cons]
            rw [← hvalueStep]
            exact hvalue
        · exact Or.inr hfail
    · have htstop : shouldLoop (fun k ↦
          (store6 bits' value' copy' fuel' scratch' (.zero :: .one :: status) k).head?) = false := by
        simp [shouldLoop, store6]
      have hstop : cappedDecodeProg.Exec
          (store6 bits' value' copy' fuel' scratch' (.zero :: .one :: status))
          (store6 bits' value' copy' fuel' scratch' (.zero :: .one :: status)) 1 := by
        exact StackProg.Exec.loopFalse htstop
      have he := StackProg.Exec.loopTrue ht hdigit hstop
      refine ⟨store6 bits' value' copy' fuel' scratch' (.zero :: .one :: status),
        1+cost+1+1, he, ?_, Or.inr ⟨_, _, _, _, _, rfl⟩⟩
      simp only [List.length_cons, Nat.mul_succ]
      have hnonneg : 0 ≤ (9*(n+fuel)+15)*tail.length := Nat.zero_le _
      omega

private theorem digitValue_ge (n : ℕ) (a : BSym) : n ≤ digitValue n a := by
  simp only [digitValue]
  split <;> omega

private theorem digitFold_ge (bits : List BSym) (n : ℕ) : n ≤ bits.foldl digitValue n := by
  induction bits generalizing n with
  | nil => rfl
  | cons a tail ih =>
    exact le_trans (digitValue_ge n a) (ih (digitValue n a))

/-- A valid binary stream whose completed value fits the initial unary cap is
    never spuriously rejected. The final unary value and unused fuel are exact. -/
theorem cappedDecode_valid (bits : List BSym) (n fuel : ℕ) (status : List BSym)
    (hbits : ∀ a ∈ bits, a = .zero ∨ a = .one)
    (hcap : bits.foldl digitValue n ≤ n+fuel) :
    ∃ steps,
      cappedDecodeProg.Exec
        (store6 bits (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: status))
        (store6 [] (List.replicate (bits.foldl digitValue n) .one) []
          (List.replicate (n+fuel-bits.foldl digitValue n) .one) [] (.one :: status)) steps ∧
      steps ≤ (9*(n+fuel)+15)*bits.length+1 := by
  induction bits generalizing n fuel with
  | nil =>
    refine ⟨1, ?_, by simp⟩
    simpa [cappedDecodeProg] using
      (StackProg.Exec.loopFalse (test := shouldLoop) (p := cappedDigitProg)
      (s := store6 [] (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: status)) (by rfl))
  | cons a tail ih =>
    have htailbits : ∀ b ∈ tail, b = .zero ∨ b = .one := by
      intro b hb
      exact hbits b (by simp [hb])
    have ha := hbits a (by simp)
    have hnext : digitValue n a ≤ (a :: tail).foldl digitValue n := by
      exact digitFold_ge tail (digitValue n a)
    have ht : shouldLoop (fun k ↦
        (store6 (a :: tail) (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: status) k).head?) = true := by rfl
    rcases ha with rfl | rfl
    · let spare := fuel-n
      have hf : fuel = n+spare := by
        dsimp [spare]
        simp only [digitValue, reduceCtorEq, ↓reduceIte, Nat.add_zero] at hnext
        omega
      have hsum : n+n+spare = n+fuel := by omega
      have htailcap : tail.foldl digitValue (n+n) ≤ n+n+spare := by
        simp only [List.foldl_cons, digitValue, reduceCtorEq, ↓reduceIte, Nat.add_zero] at hcap
        omega
      obtain ⟨steps, hr, hsteps⟩ := ih (n+n) spare htailbits htailcap
      have hd : cappedDigitProg.Exec
          (store6 (.zero :: tail) (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: status))
          (store6 tail (List.replicate (n+n) .one) [] (List.replicate spare .one) [] (.one :: status)) (9*n+9) := by
        simpa only [hf] using cappedDigit_zero tail n spare (.one :: status)
      have he := StackProg.Exec.loopTrue ht hd hr
      refine ⟨1+(9*n+9)+1+steps, ?_, ?_⟩
      · simpa only [cappedDecodeProg, List.foldl_cons, digitValue, reduceCtorEq, ↓reduceIte, Nat.add_zero, hsum] using he
      · rw [hsum] at hsteps
        simp only [List.length_cons, Nat.mul_succ]
        omega
    · let spare := fuel-n-1
      have hf : fuel = n+(spare+1) := by
        dsimp [spare]
        simp only [digitValue, ↓reduceIte] at hnext
        omega
      have hsum : n+n+1+spare = n+fuel := by omega
      have htailcap : tail.foldl digitValue (n+n+1) ≤ n+n+1+spare := by
        simp only [List.foldl_cons, digitValue, ↓reduceIte] at hcap
        omega
      obtain ⟨steps, hr, hsteps⟩ := ih (n+n+1) spare htailbits htailcap
      have hd : cappedDigitProg.Exec
          (store6 (.one :: tail) (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: status))
          (store6 tail (List.replicate (n+n+1) .one) [] (List.replicate spare .one) [] (.one :: status)) (9*n+11) := by
        simpa only [hf] using cappedDigit_one tail n spare (.one :: status)
      have he := StackProg.Exec.loopTrue ht hd hr
      refine ⟨1+(9*n+11)+1+steps, ?_, ?_⟩
      · simpa only [cappedDecodeProg, List.foldl_cons, digitValue, ↓reduceIte, hsum] using he
      · rw [hsum] at hsteps
        simp only [List.length_cons, Nat.mul_succ]
        omega

end TensorCappedDecode


namespace TensorCanonicalDigits

/-- Interpret little-endian Boolean digits as a natural number. -/
def bitsValue : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (bitsValue bs)

/-- Every bit list ending in one is the canonical bit representation of its
    computed value. Thus checking the most significant bit suffices for
    canonicality once a nonempty binary block has been scanned. -/
theorem bitsValue_bits_append_true (pre : List Bool) :
    (bitsValue (pre ++ [true])).bits = pre ++ [true] := by
  induction pre with
  | nil => simp [bitsValue]
  | cons b bs ih =>
    have hne : bitsValue (bs ++ [true]) ≠ 0 := by
      intro hz
      rw [hz, Nat.zero_bits] at ih
      have hcons : bs ++ [true] ≠ [] := by simp
      exact hcons ih.symm
    have hcanonical : bitsValue (bs ++ [true]) = 0 → b = true := by
      intro hz
      exact (hne hz).elim
    simpa [bitsValue, ih] using Nat.bits_append_bit (bitsValue (bs ++ [true])) b hcanonical

/-- Zero is represented by the empty block, and all other canonical bit lists
    end in one. -/
theorem nat_bits_canonical (n : ℕ) : n.bits = [] ∨ ∃ pre, n.bits = pre ++ [true] := by
  induction n using Nat.binaryRecFromOne with
  | zero => exact Or.inl (by simp)
  | one => exact Or.inr ⟨[], by simp⟩
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b (fun hz ↦ (hn hz).elim)]
    rcases ih with hempty | ⟨pre, hprefix⟩
    · have hn0 : n = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        simp [Nat.testBit_eq_inth, hempty]
      exact (hn hn0).elim
    · exact Or.inr ⟨b :: pre, by simp [hprefix]⟩

/-- The parser's mathematical canonicality condition is exact: an empty
    block or one ending in one is precisely a canonical `Nat.bits` block. -/
theorem canonical_digits_iff (digits : List Bool) :
    (digits = [] ∨ ∃ pre, digits = pre ++ [true]) ↔ ∃ n : ℕ, n.bits = digits := by
  constructor
  · intro h
    rcases h with rfl | ⟨pre, rfl⟩
    · exact ⟨0, by simp⟩
    · exact ⟨bitsValue (pre ++ [true]), bitsValue_bits_append_true pre⟩
  · rintro ⟨n, rfl⟩
    exact nat_bits_canonical n


/-- Reading the scanner's reversed Boolean digit stack from the top computes
    the little-endian number by the familiar accumulator update `2a+b`. -/
theorem bitsValue_reverse_fold (digits : List Bool) :
    digits.reverse.foldl (fun a bit ↦ 2 * a + bit.toNat) 0 = bitsValue digits := by
  induction digits with
  | nil => rfl
  | cons b bs ih =>
    simp [List.reverse_cons, List.foldl_append, bitsValue, ih, Nat.bit_val]

/-- The mathematical bit decoder is a left inverse of the platform's
    canonical binary representation. -/
theorem bitsValue_nat_bits (n : ℕ) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n hcanonical ih =>
    rw [Nat.bits_append_bit n b hcanonical]
    simp [bitsValue, ih]

open ProjSchedTW.Complexity

private def digitSym (b : Bool) : BSym := if b then .one else .zero
private def symValue (s : BSym) : ℕ := if s = .one then 1 else 0

/-- The exact symbol stack produced by the first-block scanner decodes to the
    original natural number by successive double-and-add operations. -/
theorem scanner_digits_reverse_fold (n : ℕ) :
    ((n.bits.map digitSym).reverse).foldl (fun a sym ↦ 2 * a + symValue sym) 0 = n := by
  rw [← List.map_reverse, List.foldl_map]
  have hstep : (fun (a : ℕ) (bit : Bool) ↦ 2 * a + symValue (digitSym bit)) =
      (fun (a : ℕ) (bit : Bool) ↦ 2 * a + bit.toNat) := by
    funext a bit
    cases bit <;> rfl
  rw [hstep, bitsValue_reverse_fold, bitsValue_nat_bits]

/-- Every double-and-add step is nondecreasing, so processing further bits
    cannot decrease the running value. -/
private theorem bit_fold_nondecreasing (digits : List Bool) (a : ℕ) :
    a ≤ digits.foldl (fun x bit ↦ 2 * x + bit.toNat) a := by
  induction digits generalizing a with
  | nil => simp
  | cons bit digits ih =>
    have hstep : a ≤ 2 * a + bit.toNat := by omega
    exact le_trans hstep (ih (2 * a + bit.toNat))

/-- Every intermediate value while reading the scanner's most-significant-bit
    first digit stack is at most the completed value n. Hence the early cap by
    the input length cannot reject a valid graph code, whose vertex count is
    already bounded by that length. -/
theorem reversed_bits_prefix_value_le (n k : ℕ) :
    ((n.bits.reverse.take k).foldl (fun x bit ↦ 2 * x + bit.toNat) 0) ≤ n := by
  let ds := n.bits.reverse
  have h := bit_fold_nondecreasing (ds.drop k) ((ds.take k).foldl (fun x bit ↦ 2 * x + bit.toNat) 0)
  rw [← List.foldl_append, List.take_append_drop] at h
  change ((n.bits.reverse.take k).foldl (fun x bit ↦ 2 * x + bit.toNat) 0) ≤
    n.bits.reverse.foldl (fun x bit ↦ 2 * x + bit.toNat) 0 at h
  rw [bitsValue_reverse_fold, bitsValue_nat_bits] at h
  exact h

end TensorCanonicalDigits

namespace TensorCappedDecode

open TensorCanonicalDigits

/-- The actual digit stack produced by the prefix parser for encNat n. -/
def scannerDigits (n : ℕ) : List BSym := (n.bits.map TensorCanonicalDigits.digitSym).reverse

private theorem scannerDigits_binary (n : ℕ) :
    ∀ a ∈ scannerDigits n, a = .zero ∨ a = .one := by
  intro a ha
  simp only [scannerDigits, List.mem_reverse, List.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  cases b <;> simp [TensorCanonicalDigits.digitSym]

private theorem scannerDigits_fold (n : ℕ) : (scannerDigits n).foldl digitValue 0 = n := by
  have heq : digitValue = (fun a s ↦ 2*a + TensorCanonicalDigits.symValue s) := by
    funext a s
    simp [digitValue, TensorCanonicalDigits.symValue]
    omega
  rw [heq]
  exact TensorCanonicalDigits.scanner_digits_reverse_fold n

/-- If n fits the input-length cap, the executable loop converts the exact
    parser-produced canonical digit stack to unary n without false rejection. -/
theorem cappedDecode_scannerDigits (n cap : ℕ) (status : List BSym) (hcap : n ≤ cap) :
    ∃ steps,
      cappedDecodeProg.Exec
        (store6 (scannerDigits n) [] [] (List.replicate cap .one) [] (.one :: status))
        (store6 [] (List.replicate n .one) [] (List.replicate (cap-n) .one) [] (.one :: status)) steps ∧
      steps ≤ (9*cap+15)*n.bits.length+1 := by
  have hc : (scannerDigits n).foldl digitValue 0 ≤ 0+cap := by
    simpa [scannerDigits_fold] using hcap
  obtain ⟨steps, hr, hb⟩ := cappedDecode_valid (scannerDigits n) 0 cap status (scannerDigits_binary n) hc
  refine ⟨steps, ?_, ?_⟩
  · simpa only [List.replicate_zero, Nat.zero_add, scannerDigits_fold] using hr
  · simpa [scannerDigits] using hb

end TensorCappedDecode


open CookPvsNP ProjSchedTW.Complexity

namespace TensorGraphPrefix3

/-- Three stacks hold unconsumed input, reversed digits, and status markers. -/
private def store (input acc status : List BSym) : Fin 3 → List BSym :=
  fun k ↦ if k = 0 then input else if k = 1 then acc else status

private def digitSym (b : Bool) : BSym := if b then .one else .zero

private def isDigit (o : Option BSym) : Bool :=
  match o with
  | some .zero | some .one => true
  | _ => false

private def digitTest (h : Fin 3 → Option BSym) : Bool := isDigit (h 0)
private def separatorTest (h : Fin 3 → Option BSym) : Bool := h 0 == some BSym.sep

private def readAct (h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 0 then .pop else if k = 1 then
    match h 0 with
    | some .zero => .push .zero
    | some .one => .push .one
    | _ => .keep
  else .keep

private def acceptAct (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 0 then .pop else if k = 2 then .push .one else .keep

private def rejectAct (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 2 then .push .zero else .keep

/-- A finite program that reads the first 0/1 block, consumes its separator
    on success, and pushes one status marker: one for a separator, zero for a
    missing separator or illegal next symbol. -/
def parseBlockProg : StackProg (Fin 3) BSym :=
  .seq (.loop digitTest (.act readAct))
    (.branch separatorTest (.act acceptAct) (.act rejectAct))

private theorem readAct_step (b : Bool) (rest acc status : List BSym) :
    StackProg.applyAct readAct (store (digitSym b :: rest) acc status) =
      store rest (digitSym b :: acc) status := by
  funext k
  fin_cases k <;> cases b <;>
    simp [StackProg.applyAct, readAct, store, digitSym, StackAct.apply]

private theorem acceptAct_step (tail acc status : List BSym) :
    StackProg.applyAct acceptAct (store (BSym.sep :: tail) acc status) =
      store tail acc (BSym.one :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, acceptAct, store, StackAct.apply]

private theorem rejectAct_step (rest acc status : List BSym) :
    StackProg.applyAct rejectAct (store rest acc status) =
      store rest acc (BSym.zero :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, rejectAct, store, StackAct.apply]

private theorem scan_exec (digits : List Bool) (stop acc status : List BSym)
    (hstop : isDigit stop.head? = false) :
    (StackProg.loop digitTest (.act readAct)).Exec
      (store (digits.map digitSym ++ stop) acc status)
      (store stop ((digits.map digitSym).reverse ++ acc) status)
      (3 * digits.length + 1) := by
  induction digits generalizing acc with
  | nil =>
    apply StackProg.Exec.loopFalse
    simpa [digitTest, store] using hstop
  | cons b digits ih =>
    have htest : digitTest (fun k ↦ (store (digitSym b ::
        (digits.map digitSym ++ stop)) acc status k).head?) = true := by
      cases b <;> rfl
    have hact : (StackProg.act readAct).Exec
        (store (digitSym b :: (digits.map digitSym ++ stop)) acc status)
        (store (digits.map digitSym ++ stop) (digitSym b :: acc) status) 1 := by
      rw [← readAct_step]
      exact StackProg.Exec.act _ _
    have hloop := StackProg.Exec.loopTrue htest hact (ih (digitSym b :: acc))
    simpa [List.reverse_cons, List.append_assoc, Nat.mul_add,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hloop

/-- A terminated block is consumed and accepted, with exact cost 3d+4. -/
theorem parseBlockProg_success (digits : List Bool) (tail acc status : List BSym) :
    parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.sep :: tail) acc status)
      (store tail ((digits.map digitSym).reverse ++ acc) (BSym.one :: status))
      (3 * digits.length + 4) := by
  have hs := scan_exec digits (BSym.sep :: tail) acc status (by rfl)
  have hact : (StackProg.act acceptAct).Exec
      (store (BSym.sep :: tail) ((digits.map digitSym).reverse ++ acc) status)
      (store tail ((digits.map digitSym).reverse ++ acc) (BSym.one :: status)) 1 := by
    rw [← acceptAct_step]
    exact StackProg.Exec.act _ _
  have ht : separatorTest (fun k ↦
      (store (BSym.sep :: tail) ((digits.map digitSym).reverse ++ acc) status k).head?) = true := rfl
  have hb : (StackProg.branch separatorTest (.act acceptAct) (.act rejectAct)).Exec
      (store (BSym.sep :: tail) ((digits.map digitSym).reverse ++ acc) status)
      (store tail ((digits.map digitSym).reverse ++ acc) (BSym.one :: status)) 2 :=
    StackProg.Exec.branchTrue ht hact
  have hseq := StackProg.Exec.seq hs hb
  convert hseq using 1 <;> simp [parseBlockProg] <;> omega

/-- A minus sign in place of the separator is rejected and left unconsumed. -/
theorem parseBlockProg_reject_minus (digits : List Bool) (tail acc status : List BSym) :
    parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.minus :: tail) acc status)
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status))
      (3 * digits.length + 4) := by
  have hs := scan_exec digits (BSym.minus :: tail) acc status (by rfl)
  have hact : (StackProg.act rejectAct).Exec
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) status)
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status)) 1 := by
    rw [← rejectAct_step]
    exact StackProg.Exec.act _ _
  have ht : separatorTest (fun k ↦
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) status k).head?) = false := rfl
  have hb : (StackProg.branch separatorTest (.act acceptAct) (.act rejectAct)).Exec
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) status)
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status)) 2 :=
    StackProg.Exec.branchFalse ht hact
  have hseq := StackProg.Exec.seq hs hb
  convert hseq using 1 <;> simp [parseBlockProg] <;> omega

/-- End of input in place of the separator is rejected. -/
theorem parseBlockProg_reject_eof (digits : List Bool) (acc status : List BSym) :
    parseBlockProg.Exec
      (store (digits.map digitSym) acc status)
      (store [] ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status))
      (3 * digits.length + 4) := by
  have hs := scan_exec digits [] acc status (by rfl)
  have hact : (StackProg.act rejectAct).Exec
      (store [] ((digits.map digitSym).reverse ++ acc) status)
      (store [] ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status)) 1 := by
    rw [← rejectAct_step]
    exact StackProg.Exec.act _ _
  have ht : separatorTest (fun k ↦
      (store [] ((digits.map digitSym).reverse ++ acc) status k).head?) = false := rfl
  have hb : (StackProg.branch separatorTest (.act acceptAct) (.act rejectAct)).Exec
      (store [] ((digits.map digitSym).reverse ++ acc) status)
      (store [] ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status)) 2 :=
    StackProg.Exec.branchFalse ht hact
  have hseq := StackProg.Exec.seq hs hb
  convert hseq using 1 <;> simp [parseBlockProg] <;> omega


/-- A terminated block is canonical when it is empty or has most significant
    digit one; status zero from the first stage is always rejected. -/
private def canonicalTest (h : Fin 3 → Option BSym) : Bool :=
  (h 2 == some BSym.one) &&
    match h 1 with
    | none | some .one => true
    | _ => false

private def markTrueAct (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 2 then .push .one else .keep

private def markFalseAct (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 2 then .push .zero else .keep

/-- The delimiter parser followed by a finite-control canonicality check.
    The top status marker is one exactly on a terminated block that is empty
    or ends in one; the previous delimiter status is kept just below it. -/
def parseCanonicalBlockProg : StackProg (Fin 3) BSym :=
  .seq parseBlockProg (.branch canonicalTest (.act markTrueAct) (.act markFalseAct))

private theorem markTrue_step (input acc status : List BSym) :
    StackProg.applyAct markTrueAct (store input acc status) =
      store input acc (BSym.one :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, markTrueAct, store, StackAct.apply]

private theorem markFalse_step (input acc status : List BSym) :
    StackProg.applyAct markFalseAct (store input acc status) =
      store input acc (BSym.zero :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, markFalseAct, store, StackAct.apply]

/-- Empty blocks and nonempty blocks ending in one are accepted and leave
    their reversed digits available for decoding. -/
theorem parseCanonicalBlockProg_accept (digits : List Bool) (tail status : List BSym)
    (hcanon : digits = [] ∨ ∃ pre, digits = pre ++ [true]) :
    parseCanonicalBlockProg.Exec
      (store (digits.map digitSym ++ BSym.sep :: tail) [] status)
      (store tail (digits.map digitSym).reverse (BSym.one :: BSym.one :: status))
      (3 * digits.length + 7) := by
  have hp : parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.sep :: tail) [] status)
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (3 * digits.length + 4) := by
    simpa using parseBlockProg_success digits tail [] status
  have ht : canonicalTest (fun k ↦
      (store tail (digits.map digitSym).reverse (BSym.one :: status) k).head?) = true := by
    rcases hcanon with rfl | ⟨pre, rfl⟩
    · rfl
    · simp [canonicalTest, store, List.map_append, List.reverse_append, digitSym]
  have ha : (StackProg.act markTrueAct).Exec
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (store tail (digits.map digitSym).reverse (BSym.one :: BSym.one :: status)) 1 := by
    simpa only [markTrue_step] using
      (StackProg.Exec.act markTrueAct (store tail (digits.map digitSym).reverse (BSym.one :: status)))
  have hb : (StackProg.branch canonicalTest (.act markTrueAct) (.act markFalseAct)).Exec
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (store tail (digits.map digitSym).reverse (BSym.one :: BSym.one :: status)) 2 :=
    StackProg.Exec.branchTrue ht ha
  have hs := StackProg.Exec.seq hp hb
  convert hs using 1 <;> simp [parseCanonicalBlockProg] <;> omega

/-- A nonempty block with most significant digit zero is rejected. -/
theorem parseCanonicalBlockProg_reject_high_zero (pre : List Bool) (tail status : List BSym) :
    parseCanonicalBlockProg.Exec
      (store ((pre ++ [false]).map digitSym ++ BSym.sep :: tail) [] status)
      (store tail ((pre ++ [false]).map digitSym).reverse (BSym.zero :: BSym.one :: status))
      (3 * (pre ++ [false]).length + 7) := by
  let digits := pre ++ [false]
  have hp : parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.sep :: tail) [] status)
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (3 * digits.length + 4) := by
    simpa using parseBlockProg_success digits tail [] status
  have ht : canonicalTest (fun k ↦
      (store tail (digits.map digitSym).reverse (BSym.one :: status) k).head?) = false := by
    simp [digits, canonicalTest, store, List.map_append, List.reverse_append, digitSym]
  have ha : (StackProg.act markFalseAct).Exec
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (store tail (digits.map digitSym).reverse (BSym.zero :: BSym.one :: status)) 1 := by
    rw [← markFalse_step]
    exact StackProg.Exec.act _ _
  have hb : (StackProg.branch canonicalTest (.act markTrueAct) (.act markFalseAct)).Exec
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (store tail (digits.map digitSym).reverse (BSym.zero :: BSym.one :: status)) 2 :=
    StackProg.Exec.branchFalse ht ha
  have hs := StackProg.Exec.seq hp hb
  convert hs using 1 <;> simp [parseCanonicalBlockProg, digits] <;> omega


/-- A minus sign where the delimiter is required remains rejected by the full
    two-stage parser, regardless of the scanned digit sequence. -/
theorem parseCanonicalBlockProg_reject_minus (digits : List Bool) (tail status : List BSym) :
    parseCanonicalBlockProg.Exec
      (store (digits.map digitSym ++ BSym.minus :: tail) [] status)
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status))
      (3 * digits.length + 7) := by
  have hp : parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.minus :: tail) [] status)
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status))
      (3 * digits.length + 4) := by
    simpa using parseBlockProg_reject_minus digits tail [] status
  have ht : canonicalTest (fun k ↦
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status) k).head?) = false := by
    simp [canonicalTest, store]
  have ha : (StackProg.act markFalseAct).Exec
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status))
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status)) 1 := by
    simpa only [markFalse_step] using
      (StackProg.Exec.act markFalseAct
        (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status)))
  have hb : (StackProg.branch canonicalTest (.act markTrueAct) (.act markFalseAct)).Exec
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status))
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status)) 2 :=
    StackProg.Exec.branchFalse ht ha
  have hs := StackProg.Exec.seq hp hb
  convert hs using 1 <;> simp [parseCanonicalBlockProg] <;> omega

/-- A missing separator at end of input remains rejected by both stages. -/
theorem parseCanonicalBlockProg_reject_eof (digits : List Bool) (status : List BSym) :
    parseCanonicalBlockProg.Exec
      (store (digits.map digitSym) [] status)
      (store [] (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status))
      (3 * digits.length + 7) := by
  have hp : parseBlockProg.Exec
      (store (digits.map digitSym) [] status)
      (store [] (digits.map digitSym).reverse (BSym.zero :: status))
      (3 * digits.length + 4) := by
    simpa using parseBlockProg_reject_eof digits [] status
  have ht : canonicalTest (fun k ↦
      (store [] (digits.map digitSym).reverse (BSym.zero :: status) k).head?) = false := by
    simp [canonicalTest, store]
  have ha : (StackProg.act markFalseAct).Exec
      (store [] (digits.map digitSym).reverse (BSym.zero :: status))
      (store [] (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status)) 1 := by
    simpa only [markFalse_step] using
      (StackProg.Exec.act markFalseAct (store [] (digits.map digitSym).reverse (BSym.zero :: status)))
  have hb : (StackProg.branch canonicalTest (.act markTrueAct) (.act markFalseAct)).Exec
      (store [] (digits.map digitSym).reverse (BSym.zero :: status))
      (store [] (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status)) 2 :=
    StackProg.Exec.branchFalse ht ha
  have hs := StackProg.Exec.seq hp hb
  convert hs using 1 <;> simp [parseCanonicalBlockProg] <;> omega


/-- Every Boolean block is empty, ends in one, or ends in zero. -/
private theorem digit_end_cases (digits : List Bool) :
    digits = [] ∨ (∃ pre, digits = pre ++ [true]) ∨ ∃ pre, digits = pre ++ [false] := by
  cases hr : digits.reverse with
  | nil =>
    left
    have h := congrArg List.reverse hr
    simpa using h
  | cons b pre =>
    have h : digits = pre.reverse ++ [b] := by
      have h' := congrArg List.reverse hr
      simpa using h'
    cases b with
    | false => exact Or.inr (Or.inr ⟨pre.reverse, h⟩)
    | true => exact Or.inr (Or.inl ⟨pre.reverse, h⟩)

/-- Every alphabet string decomposes into its maximal 0/1 prefix followed by
    a separator, a minus sign, or end of input. -/
private theorem split_digit_prefix (input : List BSym) :
    ∃ digits : List Bool, ∃ stop : List BSym,
      input = digits.map digitSym ++ stop ∧
        (stop = [] ∨ (∃ tail, stop = BSym.sep :: tail) ∨ ∃ tail, stop = BSym.minus :: tail) := by
  induction input with
  | nil => exact ⟨[], [], rfl, Or.inl rfl⟩
  | cons a input ih =>
    cases a with
    | zero =>
      obtain ⟨digits, stop, heq, hstop⟩ := ih
      refine ⟨false :: digits, stop, ?_, hstop⟩
      simp [digitSym, heq]
    | one =>
      obtain ⟨digits, stop, heq, hstop⟩ := ih
      refine ⟨true :: digits, stop, ?_, hstop⟩
      simp [digitSym, heq]
    | minus => exact ⟨[], BSym.minus :: input, by simp, Or.inr (Or.inr ⟨input, rfl⟩)⟩
    | sep => exact ⟨[], BSym.sep :: input, by simp, Or.inr (Or.inl ⟨input, rfl⟩)⟩

/-- The concrete canonical-block parser terminates on every input in linear
    stack-program time, including malformed input and end of input. -/
theorem parseCanonicalBlockProg_total (input status : List BSym) :
    ∃ out steps, parseCanonicalBlockProg.Exec (store input [] status) out steps ∧
      steps ≤ 3 * input.length + 7 := by
  obtain ⟨digits, stop, hw, hstop⟩ := split_digit_prefix input
  subst input
  have hbound : 3 * digits.length + 7 ≤ 3 * (digits.map digitSym ++ stop).length + 7 := by
    simp only [List.length_append, List.length_map]
    omega
  rcases hstop with hempty | ⟨tail, hsep⟩ | ⟨tail, hminus⟩
  · subst stop
    refine ⟨store [] (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status),
      3 * digits.length + 7, ?_, hbound⟩
    simpa using parseCanonicalBlockProg_reject_eof digits status
  · subst stop
    rcases digit_end_cases digits with hempty | ⟨pre, htrue⟩ | ⟨pre, hfalse⟩
    · refine ⟨store tail (digits.map digitSym).reverse (BSym.one :: BSym.one :: status),
        3 * digits.length + 7, ?_, hbound⟩
      exact parseCanonicalBlockProg_accept digits tail status (Or.inl hempty)
    · refine ⟨store tail (digits.map digitSym).reverse (BSym.one :: BSym.one :: status),
        3 * digits.length + 7, ?_, hbound⟩
      exact parseCanonicalBlockProg_accept digits tail status (Or.inr ⟨pre, htrue⟩)
    · subst digits
      refine ⟨store tail ((pre ++ [false]).map digitSym).reverse (BSym.zero :: BSym.one :: status),
        3 * (pre ++ [false]).length + 7, ?_, hbound⟩
      exact parseCanonicalBlockProg_reject_high_zero pre tail status
  · subst stop
    refine ⟨store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status),
      3 * digits.length + 7, ?_, hbound⟩
    exact parseCanonicalBlockProg_reject_minus digits tail status

/-- On every input, the parser terminates with at most one output digit for
    each input symbol, including malformed and truncated encodings. -/
theorem parseCanonicalBlockProg_total_length (input status : List BSym) :
    ∃ rest digits outstatus steps,
      parseCanonicalBlockProg.Exec (store input [] status) (store rest digits outstatus) steps ∧
      steps ≤ 3*input.length+7 ∧ digits.length ≤ input.length := by
  obtain ⟨digits, stop, hw, hstop⟩ := split_digit_prefix input
  subst input
  have hbound : 3*digits.length+7 ≤ 3*(digits.map digitSym ++ stop).length+7 := by
    simp only [List.length_append, List.length_map]
    omega
  have hlen : (digits.map digitSym).reverse.length ≤ (digits.map digitSym ++ stop).length := by
    simp only [List.length_reverse, List.length_map, List.length_append]
    omega
  rcases hstop with hempty | ⟨tail, hsep⟩ | ⟨tail, hminus⟩
  · subst stop
    refine ⟨[], (digits.map digitSym).reverse, .zero :: .zero :: status,
      3*digits.length+7, ?_, hbound, hlen⟩
    simpa using parseCanonicalBlockProg_reject_eof digits status
  · subst stop
    rcases digit_end_cases digits with hempty | ⟨pre, htrue⟩ | ⟨pre, hfalse⟩
    · exact ⟨tail, (digits.map digitSym).reverse, .one :: .one :: status,
        3*digits.length+7, parseCanonicalBlockProg_accept digits tail status (Or.inl hempty), hbound, hlen⟩
    · exact ⟨tail, (digits.map digitSym).reverse, .one :: .one :: status,
        3*digits.length+7, parseCanonicalBlockProg_accept digits tail status (Or.inr ⟨pre, htrue⟩), hbound, hlen⟩
    · subst digits
      exact ⟨tail, ((pre ++ [false]).map digitSym).reverse, .zero :: .one :: status,
        3*(pre ++ [false]).length+7, parseCanonicalBlockProg_reject_high_zero pre tail status, hbound, hlen⟩
  · subst stop
    exact ⟨.minus :: tail, (digits.map digitSym).reverse, .zero :: .zero :: status,
      3*digits.length+7, parseCanonicalBlockProg_reject_minus digits tail status, hbound, hlen⟩

end TensorGraphPrefix3

namespace TensorGraphPrefix3

/-- Actual canonical natural blocks are parsed into the MSB-first digit stack. -/
theorem parseCanonicalBlockProg_encNat (n : ℕ) (tail status : List BSym) :
    parseCanonicalBlockProg.Exec
      (store (encNat n ++ tail) [] status)
      (store tail (n.bits.map digitSym).reverse (BSym.one :: BSym.one :: status))
      (3*n.bits.length+7) := by
  have hmap : (n.bits.map fun b ↦ if b then BSym.one else BSym.zero) = n.bits.map digitSym := by
    apply List.map_congr_left
    intro b hb
    cases b <;> rfl
  have hcode : encNat n ++ tail = n.bits.map digitSym ++ BSym.sep :: tail := by
    simp only [encNat, List.append_assoc, List.singleton_append, hmap]
  rw [hcode]
  exact parseCanonicalBlockProg_accept n.bits tail status (TensorCanonicalDigits.nat_bits_canonical n)

end TensorGraphPrefix3

namespace TensorPrefixDecode

open StackProgPortLift TensorGraphPrefix3 TensorCappedDecode

/-- Input remainder, digit stack, unary value, copy, fuel, scratch, status. -/
def store7 (input digits value copy fuel scratch status : List BSym) : Fin 7 → List BSym :=
  fun k ↦ if k = 0 then input else if k = 1 then digits else if k = 2 then value
    else if k = 3 then copy else if k = 4 then fuel else if k = 5 then scratch else status

def parsePorts : Fin 3 ↪ Fin 7 := ⟨![0,1,6], by decide⟩
def parseInverse : Fin 7 → Option (Fin 3) := ![some 0,some 1,none,none,none,none,some 2]
def decodePorts : Fin 6 ↪ Fin 7 := ⟨![1,2,3,4,5,6], by decide⟩
def decodeInverse : Fin 7 → Option (Fin 6) := ![none,some 0,some 1,some 2,some 3,some 4,some 5]

private theorem parseInverse_correct (l : Fin 7) (k : Fin 3) :
    parseInverse l = some k ↔ parsePorts k = l := by fin_cases l <;> fin_cases k <;> decide
private theorem decodeInverse_correct (l : Fin 7) (k : Fin 6) :
    decodeInverse l = some k ↔ decodePorts k = l := by fin_cases l <;> fin_cases k <;> decide

private def accepted (h : Fin 7 → Option BSym) : Bool := h 6 == some BSym.one
private def keepAct (_h : Fin 7 → Option BSym) (_k : Fin 7) : StackAct BSym := .keep

/-- Parse a canonical first block; only then run its capped unary decoder. -/
def prefixDecodeProg : StackProg (Fin 7) BSym :=
  .seq (liftProgC parsePorts parseInverse parseCanonicalBlockProg)
    (.branch accepted (liftProgC decodePorts decodeInverse cappedDecodeProg) (.act keepAct))

private theorem write_parse (a b c i ds v cp f tmp st : List BSym) :
    write parsePorts (TensorGraphPrefix3.store a b c) (store7 i ds v cp f tmp st) =
      store7 a b v cp f tmp c := by
  funext k
  fin_cases k
  · simpa [parsePorts, TensorGraphPrefix3.store, TensorCappedDecode.store6, store7] using
      (StackProgPortLift.write_at parsePorts (TensorGraphPrefix3.store a b c) (store7 i ds v cp f tmp st) (0 : Fin 3))
  · simpa [parsePorts, TensorGraphPrefix3.store, TensorCappedDecode.store6, store7] using
      (StackProgPortLift.write_at parsePorts (TensorGraphPrefix3.store a b c) (store7 i ds v cp f tmp st) (1 : Fin 3))
  · have ho : ∀ j : Fin 3, parsePorts j ≠ (2 : Fin 7) := by
      intro j; fin_cases j <;> decide
    simpa [store7] using (StackProgPortLift.write_outside parsePorts (TensorGraphPrefix3.store a b c) (store7 i ds v cp f tmp st) ho)
  · have ho : ∀ j : Fin 3, parsePorts j ≠ (3 : Fin 7) := by
      intro j; fin_cases j <;> decide
    simpa [store7] using (StackProgPortLift.write_outside parsePorts (TensorGraphPrefix3.store a b c) (store7 i ds v cp f tmp st) ho)
  · have ho : ∀ j : Fin 3, parsePorts j ≠ (4 : Fin 7) := by
      intro j; fin_cases j <;> decide
    simpa [store7] using (StackProgPortLift.write_outside parsePorts (TensorGraphPrefix3.store a b c) (store7 i ds v cp f tmp st) ho)
  · have ho : ∀ j : Fin 3, parsePorts j ≠ (5 : Fin 7) := by
      intro j; fin_cases j <;> decide
    simpa [store7] using (StackProgPortLift.write_outside parsePorts (TensorGraphPrefix3.store a b c) (store7 i ds v cp f tmp st) ho)
  · simpa [parsePorts, TensorGraphPrefix3.store, TensorCappedDecode.store6, store7] using
      (StackProgPortLift.write_at parsePorts (TensorGraphPrefix3.store a b c) (store7 i ds v cp f tmp st) (2 : Fin 3))

private theorem write_decode (a b c d e f i ds v cp fuel tmp st : List BSym) :
    write decodePorts (TensorCappedDecode.store6 a b c d e f) (store7 i ds v cp fuel tmp st) =
      store7 i a b c d e f := by
  funext k
  fin_cases k
  · have ho : ∀ j : Fin 6, decodePorts j ≠ (0 : Fin 7) := by
      intro j; fin_cases j <;> decide
    simpa [store7] using (StackProgPortLift.write_outside decodePorts (TensorCappedDecode.store6 a b c d e f) (store7 i ds v cp fuel tmp st) ho)
  · simpa [decodePorts, TensorGraphPrefix3.store, TensorCappedDecode.store6, store7] using
      (StackProgPortLift.write_at decodePorts (TensorCappedDecode.store6 a b c d e f) (store7 i ds v cp fuel tmp st) (0 : Fin 6))
  · simpa [decodePorts, TensorGraphPrefix3.store, TensorCappedDecode.store6, store7] using
      (StackProgPortLift.write_at decodePorts (TensorCappedDecode.store6 a b c d e f) (store7 i ds v cp fuel tmp st) (1 : Fin 6))
  · simpa [decodePorts, TensorGraphPrefix3.store, TensorCappedDecode.store6, store7] using
      (StackProgPortLift.write_at decodePorts (TensorCappedDecode.store6 a b c d e f) (store7 i ds v cp fuel tmp st) (2 : Fin 6))
  · simpa [decodePorts, TensorGraphPrefix3.store, TensorCappedDecode.store6, store7] using
      (StackProgPortLift.write_at decodePorts (TensorCappedDecode.store6 a b c d e f) (store7 i ds v cp fuel tmp st) (3 : Fin 6))
  · simpa [decodePorts, TensorGraphPrefix3.store, TensorCappedDecode.store6, store7] using
      (StackProgPortLift.write_at decodePorts (TensorCappedDecode.store6 a b c d e f) (store7 i ds v cp fuel tmp st) (4 : Fin 6))
  · simpa [decodePorts, TensorGraphPrefix3.store, TensorCappedDecode.store6, store7] using
      (StackProgPortLift.write_at decodePorts (TensorCappedDecode.store6 a b c d e f) (store7 i ds v cp fuel tmp st) (5 : Fin 6))

private theorem parse_exec7 (i ds v cp f tmp st i' ds' st' : List BSym) (steps : ℕ)
    (h : parseCanonicalBlockProg.Exec (TensorGraphPrefix3.store i ds st)
      (TensorGraphPrefix3.store i' ds' st') steps) :
    (liftProgC parsePorts parseInverse parseCanonicalBlockProg).Exec
      (store7 i ds v cp f tmp st) (store7 i' ds' v cp f tmp st') steps := by
  have hp : project parsePorts (store7 i ds v cp f tmp st) = TensorGraphPrefix3.store i ds st := by
    funext k
    fin_cases k <;> simp [project, parsePorts, store7, TensorGraphPrefix3.store]
  have hr := lift_exec parsePorts h (store7 i ds v cp f tmp st) hp
  rw [write_parse] at hr
  simpa only [liftProgC_eq_liftProg parsePorts parseInverse parseInverse_correct] using hr

private theorem decode_exec7 (i ds v cp f tmp st : List BSym) (out : Fin 6 → List BSym) (steps : ℕ)
    (h : cappedDecodeProg.Exec (TensorCappedDecode.store6 ds v cp f tmp st) out steps) :
    (liftProgC decodePorts decodeInverse cappedDecodeProg).Exec
      (store7 i ds v cp f tmp st) (write decodePorts out (store7 i ds v cp f tmp st)) steps := by
  have hp : project decodePorts (store7 i ds v cp f tmp st) = TensorCappedDecode.store6 ds v cp f tmp st := by
    funext k
    fin_cases k <;> simp [project, decodePorts, store7, TensorCappedDecode.store6]
  have hr := lift_exec decodePorts h (store7 i ds v cp f tmp st) hp
  simpa only [liftProgC_eq_liftProg decodePorts decodeInverse decodeInverse_correct] using hr

private theorem keep_exec (s : Fin 7 → List BSym) : (StackProg.act keepAct).Exec s s 1 := by
  have heq : StackProg.applyAct keepAct s = s := by
    funext k
    simp [StackProg.applyAct, keepAct, StackAct.apply]
  simpa only [heq] using StackProg.Exec.act keepAct s

/-- The combined executable halts for every input and every cap. The parser
    bounds its digit output by input length, so decoding is polynomial even on
    malformed input. -/
theorem prefixDecode_total (input status : List BSym) (cap : ℕ) :
    ∃ out steps,
      prefixDecodeProg.Exec
        (store7 input [] [] [] (List.replicate cap .one) [] status) out steps ∧
      steps ≤ (9*cap+15)*input.length + 3*input.length + 10 := by
  obtain ⟨rest, digits, outstatus, psteps, hp, hpbound, hdlen⟩ :=
    parseCanonicalBlockProg_total_length input status
  have hparse := parse_exec7 input [] [] [] (List.replicate cap .one) [] status
    rest digits outstatus psteps hp
  by_cases hok : outstatus.head? = some BSym.one
  · have hshape : ∃ tail, outstatus = .one :: tail := by
      cases outstatus with
      | nil => simp at hok
      | cons a tail =>
        cases a <;> simp_all
    obtain ⟨tail, rfl⟩ := hshape
    obtain ⟨out, dsteps, hdecode, hdbound, _⟩ := cappedDecode_total digits 0 cap tail
    have hdecode7 := decode_exec7 rest digits [] [] (List.replicate cap .one) [] (.one :: tail) out dsteps (by
      simpa using hdecode)
    have ha : accepted (fun k ↦
        (store7 rest digits [] [] (List.replicate cap .one) [] (.one :: tail) k).head?) = true := by rfl
    have hb := StackProg.Exec.branchTrue (q := .act keepAct) ha hdecode7
    have he := StackProg.Exec.seq hparse hb
    refine ⟨write decodePorts out (store7 rest digits [] [] (List.replicate cap .one) [] (.one :: tail)),
      psteps+1+(1+dsteps), he, ?_⟩
    have hm := Nat.mul_le_mul_left (9*cap+15) hdlen
    simp only [Nat.zero_add] at hdbound
    omega
  · have ha : accepted (fun k ↦
        (store7 rest digits [] [] (List.replicate cap .one) [] outstatus k).head?) = false := by
      simp [accepted, store7, hok]
    have hb := StackProg.Exec.branchFalse (p := liftProgC decodePorts decodeInverse cappedDecodeProg)
      ha (keep_exec (store7 rest digits [] [] (List.replicate cap .one) [] outstatus))
    have he := StackProg.Exec.seq hparse hb
    refine ⟨store7 rest digits [] [] (List.replicate cap .one) [] outstatus,
      psteps+1+2, he, ?_⟩
    have hn : 0 ≤ (9*cap+15)*input.length := Nat.zero_le _
    omega

/-- Canonical encNat n is parsed and converted to unary n when it fits the cap;
    the unconsumed suffix and remaining fuel are preserved exactly. -/
theorem prefixDecode_encNat (n cap : ℕ) (tail status : List BSym) (hcap : n ≤ cap) :
    ∃ steps,
      prefixDecodeProg.Exec
        (store7 (encNat n ++ tail) [] [] [] (List.replicate cap .one) [] status)
        (store7 tail [] (List.replicate n .one) [] (List.replicate (cap-n) .one) []
          (.one :: .one :: status)) steps ∧
      steps ≤ (9*cap+18)*n.bits.length+10 := by
  have hmap : (n.bits.map TensorGraphPrefix3.digitSym).reverse = scannerDigits n := by
    unfold scannerDigits
    congr 1
  have hp : parseCanonicalBlockProg.Exec
      (TensorGraphPrefix3.store (encNat n ++ tail) [] status)
      (TensorGraphPrefix3.store tail (scannerDigits n) (.one :: .one :: status))
      (3*n.bits.length+7) := by
    simpa only [hmap] using parseCanonicalBlockProg_encNat n tail status
  have hparse := parse_exec7 (encNat n ++ tail) [] [] [] (List.replicate cap .one) [] status
    tail (scannerDigits n) (.one :: .one :: status) (3*n.bits.length+7) hp
  obtain ⟨dsteps, hd, hdbound⟩ := cappedDecode_scannerDigits n cap (.one :: status) hcap
  have hdecode7 := decode_exec7 tail (scannerDigits n) [] [] (List.replicate cap .one) []
    (.one :: .one :: status)
    (TensorCappedDecode.store6 [] (List.replicate n .one) [] (List.replicate (cap-n) .one) [] (.one :: .one :: status)) dsteps hd
  rw [write_decode] at hdecode7
  have ha : accepted (fun k ↦
      (store7 tail (scannerDigits n) [] [] (List.replicate cap .one) [] (.one :: .one :: status) k).head?) = true := by rfl
  have hb := StackProg.Exec.branchTrue (q := .act keepAct) ha hdecode7
  have he := StackProg.Exec.seq hparse hb
  refine ⟨(3*n.bits.length+7)+1+(1+dsteps), he, ?_⟩
  nlinarith


/-- All-input decoding has a usable outcome invariant: a successful output
    carries a unary value and complementary fuel summing to cap; all other
    outputs have a non-success status marker. -/
theorem prefixDecode_total_structured (input status : List BSym) (cap : ℕ) :
    ∃ out steps,
      prefixDecodeProg.Exec (store7 input [] [] [] (List.replicate cap .one) [] status) out steps ∧
      steps ≤ (9*cap+15)*input.length + 3*input.length + 10 ∧
      ((∃ rest n fuel tail, out = store7 rest [] (List.replicate n .one) []
          (List.replicate fuel .one) [] (.one :: tail) ∧ n+fuel=cap) ∨
       (out 6).head? ≠ some BSym.one) := by
  obtain ⟨rest, digits, outstatus, psteps, hp, hpbound, hdlen⟩ :=
    parseCanonicalBlockProg_total_length input status
  have hparse := parse_exec7 input [] [] [] (List.replicate cap .one) [] status
    rest digits outstatus psteps hp
  by_cases hok : outstatus.head? = some BSym.one
  · have hshape : ∃ tail, outstatus = .one :: tail := by
      cases outstatus with
      | nil => simp at hok
      | cons a tail => cases a <;> simp_all
    obtain ⟨tail, rfl⟩ := hshape
    obtain ⟨out, dsteps, hdecode, hdbound, hresult⟩ := cappedDecode_total digits 0 cap tail
    have hdecode7 := decode_exec7 rest digits [] [] (List.replicate cap .one) [] (.one :: tail) out dsteps (by
      simpa using hdecode)
    have ha : accepted (fun k ↦
        (store7 rest digits [] [] (List.replicate cap .one) [] (.one :: tail) k).head?) = true := by rfl
    have hb := StackProg.Exec.branchTrue (q := .act keepAct) ha hdecode7
    have he := StackProg.Exec.seq hparse hb
    refine ⟨write decodePorts out (store7 rest digits [] [] (List.replicate cap .one) [] (.one :: tail)),
      psteps+1+(1+dsteps), he, ?_, ?_⟩
    · have hm := Nat.mul_le_mul_left (9*cap+15) hdlen
      simp only [Nat.zero_add] at hdbound
      omega
    · rcases hresult with ⟨n, fuel, hout, hsum, _⟩ | ⟨bits, value, copy, fuel, scratch, hout⟩
      · left
        refine ⟨rest, n, fuel, tail, ?_, ?_⟩
        · rw [hout, write_decode]
        · simpa only [Nat.zero_add] using hsum
      · right
        rw [hout, write_decode]
        simp [store7]
  · have ha : accepted (fun k ↦
        (store7 rest digits [] [] (List.replicate cap .one) [] outstatus k).head?) = false := by
      simp [accepted, store7, hok]
    have hb := StackProg.Exec.branchFalse (p := liftProgC decodePorts decodeInverse cappedDecodeProg)
      ha (keep_exec (store7 rest digits [] [] (List.replicate cap .one) [] outstatus))
    have he := StackProg.Exec.seq hparse hb
    refine ⟨store7 rest digits [] [] (List.replicate cap .one) [] outstatus,
      psteps+1+2, he, ?_, Or.inr ?_⟩
    · have hn : 0 ≤ (9*cap+15)*input.length := Nat.zero_le _
      omega
    · simpa [store7] using hok

end TensorPrefixDecode


open CookPvsNP ProjSchedTW.Complexity

namespace TensorInputUnaryLength

/-- Input, temporary copy, unary length, and scratch. -/
private def store4 (input copy count scratch : List BSym) : Fin 4 → List BSym :=
  fun k ↦ if k = 0 then input else if k = 1 then copy else if k = 2 then count else scratch

private def hasCopy (h : Fin 4 → Option BSym) : Bool := (h 1).isSome

private def countAct (_h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 1 then .pop else if k = 2 then .push .one else .keep

/-- Consume one arbitrary copied input symbol for each unary token written. -/
def countProg : StackProg (Fin 4) BSym := .loop hasCopy (.act countAct)

/-- The input is preserved; both temporary stacks are emptied. -/
def inputLengthProg : StackProg (Fin 4) BSym := .seq (copyProg 0 1 3) countProg

private theorem count_step (input rest : List BSym) (a : BSym) (n : ℕ) :
    StackProg.applyAct countAct (store4 input (a :: rest) (List.replicate n .one) []) =
      store4 input rest (List.replicate (n+1) .one) [] := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, countAct, store4, StackAct.apply, List.replicate_succ]

/-- Actual loop execution: arbitrary input symbols count equally. -/
theorem countProg_exec (input copy : List BSym) (n : ℕ) :
    countProg.Exec (store4 input copy (List.replicate n .one) [])
      (store4 input [] (List.replicate (copy.length+n) .one) [])
      (3*copy.length+1) := by
  induction copy generalizing n with
  | nil =>
    simpa [countProg] using
      (StackProg.Exec.loopFalse (test := hasCopy) (p := .act countAct)
        (s := store4 input [] (List.replicate n .one) []) (by rfl))
  | cons a copy ih =>
    have ht : hasCopy (fun k ↦ (store4 input (a :: copy) (List.replicate n .one) [] k).head?) = true := rfl
    have ha : (StackProg.act countAct).Exec
        (store4 input (a :: copy) (List.replicate n .one) [])
        (store4 input copy (List.replicate (n+1) .one) []) 1 := by
      simpa only [count_step] using
        (StackProg.Exec.act countAct (store4 input (a :: copy) (List.replicate n .one) []))
    have hr := ih (n+1)
    have h := StackProg.Exec.loopTrue ht ha hr
    simpa [countProg, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      Nat.mul_add] using h

/-- Compute a unary input-length cap while preserving the original input,
    in exactly 9|input|+5 source steps. -/
theorem inputLengthProg_exec (input : List BSym) :
    inputLengthProg.Exec (store4 input [] [] [])
      (store4 input [] (List.replicate input.length .one) []) (9*input.length+5) := by
  classical
  let s := store4 input [] [] []
  let m := store4 input input [] []
  have he : s 3 = [] := by simp [s, store4]
  have hmid : Function.update s 1 (s 0 ++ s 1) = m := by
    funext k
    fin_cases k <;> simp [s, m, store4, Function.update]
  have hc : (copyProg (0 : Fin 4) 1 3).Exec s m (6*input.length+3) := by
    have h := stack_copy (0 : Fin 4) 1 3 (by decide) (by decide) (by decide) s he
    rw [hmid] at h
    simpa [s, store4] using h
  have ht : countProg.Exec m (store4 input [] (List.replicate input.length .one) [])
      (3*input.length+1) := by
    simpa [m] using countProg_exec input input 0
  have hs := StackProg.Exec.seq hc ht
  have htime : (6*input.length+3)+1+(3*input.length+1) = 9*input.length+5 := by omega
  rw [← htime]
  simpa [inputLengthProg, s] using hs

end TensorInputUnaryLength

namespace TensorPrefixDecode

open StackProgPortLift TensorInputUnaryLength

def lengthPorts : Fin 4 ↪ Fin 7 := ⟨![0,2,4,5], by decide⟩
def lengthInverse : Fin 7 → Option (Fin 4) := ![some 0,none,some 1,none,some 2,some 3,none]

private theorem lengthInverse_correct (l : Fin 7) (k : Fin 4) :
    lengthInverse l = some k ↔ lengthPorts k = l := by fin_cases l <;> fin_cases k <;> decide

/-- Compute an input-length unary cap before parsing and decoding. -/
def cappedPrefixProg : StackProg (Fin 7) BSym :=
  .seq (liftProgC lengthPorts lengthInverse inputLengthProg) prefixDecodeProg

private theorem write_length (a b c d i digits value copy fuel scratch status : List BSym) :
    write lengthPorts (TensorInputUnaryLength.store4 a b c d)
      (store7 i digits value copy fuel scratch status) =
      store7 a digits b copy c d status := by
  funext k
  fin_cases k
  · simpa [lengthPorts, TensorInputUnaryLength.store4, store7] using
      (StackProgPortLift.write_at lengthPorts (TensorInputUnaryLength.store4 a b c d)
        (store7 i digits value copy fuel scratch status) (0 : Fin 4))
  · have ho : ∀ j : Fin 4, lengthPorts j ≠ (1 : Fin 7) := by
      intro j; fin_cases j <;> decide
    simpa [store7] using (StackProgPortLift.write_outside lengthPorts (TensorInputUnaryLength.store4 a b c d)
      (store7 i digits value copy fuel scratch status) ho)
  · simpa [lengthPorts, TensorInputUnaryLength.store4, store7] using
      (StackProgPortLift.write_at lengthPorts (TensorInputUnaryLength.store4 a b c d)
        (store7 i digits value copy fuel scratch status) (1 : Fin 4))
  · have ho : ∀ j : Fin 4, lengthPorts j ≠ (3 : Fin 7) := by
      intro j; fin_cases j <;> decide
    simpa [store7] using (StackProgPortLift.write_outside lengthPorts (TensorInputUnaryLength.store4 a b c d)
      (store7 i digits value copy fuel scratch status) ho)
  · simpa [lengthPorts, TensorInputUnaryLength.store4, store7] using
      (StackProgPortLift.write_at lengthPorts (TensorInputUnaryLength.store4 a b c d)
        (store7 i digits value copy fuel scratch status) (2 : Fin 4))
  · simpa [lengthPorts, TensorInputUnaryLength.store4, store7] using
      (StackProgPortLift.write_at lengthPorts (TensorInputUnaryLength.store4 a b c d)
        (store7 i digits value copy fuel scratch status) (3 : Fin 4))
  · have ho : ∀ j : Fin 4, lengthPorts j ≠ (6 : Fin 7) := by
      intro j; fin_cases j <;> decide
    simpa [store7] using (StackProgPortLift.write_outside lengthPorts (TensorInputUnaryLength.store4 a b c d)
      (store7 i digits value copy fuel scratch status) ho)

private theorem inputLength_exec7 (input digits copy status : List BSym) :
    (liftProgC lengthPorts lengthInverse inputLengthProg).Exec
      (store7 input digits [] copy [] [] status)
      (store7 input digits [] copy (List.replicate input.length .one) [] status)
      (9*input.length+5) := by
  have hp : project lengthPorts (store7 input digits [] copy [] [] status) =
      TensorInputUnaryLength.store4 input [] [] [] := by
    funext k
    fin_cases k <;> simp [project, lengthPorts, store7, TensorInputUnaryLength.store4]
  have hr := lift_exec lengthPorts (inputLengthProg_exec input) (store7 input digits [] copy [] [] status) hp
  rw [write_length] at hr
  simpa only [liftProgC_eq_liftProg lengthPorts lengthInverse lengthInverse_correct] using hr

/-- A complete cap-generation plus prefix-decoding program halts in quadratic
    time in the input length on all inputs, including malformed blocks. -/
theorem cappedPrefix_total (input status : List BSym) :
    ∃ out steps,
      cappedPrefixProg.Exec (store7 input [] [] [] [] [] status) out steps ∧
      steps ≤ (9*input.length+15)*input.length + 12*input.length+16 := by
  obtain ⟨out, steps, hr, hb⟩ := prefixDecode_total input status input.length
  have hc := inputLength_exec7 input [] [] status
  have he := StackProg.Exec.seq hc hr
  refine ⟨out, 9*input.length+5+1+steps, he, ?_⟩
  omega

/-- On a canonical natural prefix whose value is at most the full input
    length, cap generation and decoding produce exactly that unary value. -/
theorem cappedPrefix_encNat (n : ℕ) (tail status : List BSym)
    (hcap : n ≤ (encNat n ++ tail).length) :
    ∃ steps,
      cappedPrefixProg.Exec (store7 (encNat n ++ tail) [] [] [] [] [] status)
        (store7 tail [] (List.replicate n .one) []
          (List.replicate ((encNat n ++ tail).length-n) .one) [] (.one :: .one :: status)) steps ∧
      steps ≤ 9*(encNat n ++ tail).length+6 +
        (9*(encNat n ++ tail).length+18)*n.bits.length+10 := by
  let input := encNat n ++ tail
  obtain ⟨steps, hr, hb⟩ := prefixDecode_encNat n input.length tail status hcap
  have hc := inputLength_exec7 input [] [] status
  have he := StackProg.Exec.seq hc hr
  refine ⟨9*input.length+5+1+steps, ?_, ?_⟩
  · exact he
  · dsimp [input] at *
    omega

/-- The full cap-and-prefix program either returns a unary dimension bounded
    by input length or leaves a non-success status marker. -/
theorem cappedPrefix_total_structured (input status : List BSym) :
    ∃ out steps,
      cappedPrefixProg.Exec (store7 input [] [] [] [] [] status) out steps ∧
      steps ≤ (9*input.length+15)*input.length + 12*input.length+16 ∧
      ((∃ rest n fuel tail, out = store7 rest [] (List.replicate n .one) []
          (List.replicate fuel .one) [] (.one :: tail) ∧ n+fuel=input.length) ∨
       (out 6).head? ≠ some BSym.one) := by
  obtain ⟨out, steps, hr, hb, hstatus⟩ := prefixDecode_total_structured input status input.length
  have hc := inputLength_exec7 input [] [] status
  have he := StackProg.Exec.seq hc hr
  refine ⟨out, 9*input.length+5+1+steps, he, ?_, hstatus⟩
  omega


end TensorPrefixDecode


open CookPvsNP ProjSchedTW.Complexity

namespace TensorUnarySquare

/-- Ports 0–3 hold source counter, result, loop counter, and scratch. -/
private def store4 (src dst counter tmp : List BSym) : Fin 4 → List BSym :=
  fun k ↦ if k = 0 then src else if k = 1 then dst else if k = 2 then counter else tmp

private def ports : Fin 4 ↪ Fin 4 := Function.Embedding.refl _

/-- Copy a unary v counter into a loop stack, then copy the source once per
    loop token into the result. The original counter is preserved. -/
def squareProg : StackProg (Fin 4) BSym :=
  .seq (copyProg 0 2 3) (repeatCopyProg ports)

/-- The actual finite stack program writes v² unary symbols, preserves v, and
    clears its two working stacks, in a quadratic number of program steps. -/
theorem squareProg_exec (n : ℕ) :
    squareProg.Exec (store4 (List.replicate n BSym.one) [] [] [])
      (store4 (List.replicate n BSym.one) (List.replicate (n * n) BSym.one) [] [])
      ((6 * n + 3) + 1 + ((6 * n + 7) * n + 1)) := by
  classical
  let s := store4 (List.replicate n BSym.one) [] [] []
  let m := store4 (List.replicate n BSym.one) [] (List.replicate n BSym.one) []
  have he : s 3 = [] := by simp [s, store4]
  have hmid : Function.update s 2 (s 0 ++ s 2) = m := by
    funext k
    fin_cases k <;> simp [s, m, store4, Function.update]
  have hc : (copyProg (0 : Fin 4) 2 3).Exec s m (6 * n + 3) := by
    have h := stack_copy (0 : Fin 4) 2 3 (by decide) (by decide) (by decide) s he
    rw [hmid] at h
    simpa [s, store4] using h
  have hem : m (ports 3) = [] := by simp [m, store4, ports]
  have hend : Function.update (Function.update m (ports 2) []) (ports 1)
      ((List.replicate (m (ports 2)).length (m (ports 0))).flatten ++ m (ports 1)) =
      store4 (List.replicate n BSym.one) (List.replicate (n * n) BSym.one) [] [] := by
    funext k
    fin_cases k <;> simp [m, store4, ports, Function.update]
  have hr : (repeatCopyProg ports).Exec m
      (store4 (List.replicate n BSym.one) (List.replicate (n * n) BSym.one) [] [])
      ((6 * n + 7) * n + 1) := by
    have h := stack_repeat_copy ports m hem
    rw [hend] at h
    simpa [m, store4, ports] using h
  have hs := StackProg.Exec.seq hc hr
  simpa [squareProg, s] using hs

end TensorUnarySquare


open CookPvsNP ProjSchedTW.Complexity

namespace TensorAdjacencyScan

/-- Input, unary entries remaining, reversed adjacency bits, and status. -/
def store (input counter bits status : List BSym) : Fin 4 → List BSym :=
  fun k ↦ if k = 0 then input else if k = 1 then counter else if k = 2 then bits else status

def bitSym (b : Bool) : BSym := if b then .one else .zero

def bitBlock (b : Bool) : List BSym := if b then [.one, .sep] else [.sep]

def bitBlocks (bs : List Bool) : List BSym := bs.flatMap bitBlock

private def loopTest (h : Fin 4 → Option BSym) : Bool :=
  (h 1 == some BSym.one) && (h 3 == some BSym.one)

private def sepTest (h : Fin 4 → Option BSym) : Bool := h 0 == some BSym.sep
private def oneTest (h : Fin 4 → Option BSym) : Bool := h 0 == some BSym.one

private def zeroAct (_h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 0 then .pop else if k = 1 then .pop else if k = 2 then .push .zero else .keep

private def prefixAct (_h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 0 then .pop else .keep

private def oneAct (_h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 0 then .pop else if k = 1 then .pop else if k = 2 then .push .one else .keep

private def rejectAct (_h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 3 then .push .zero else .keep

/-- Consume exactly one canonical Boolean-valued natural block; mark errors. -/
def readBitProg : StackProg (Fin 4) BSym :=
  .branch sepTest (.act zeroAct)
    (.branch oneTest (.seq (.act prefixAct)
      (.branch sepTest (.act oneAct) (.act rejectAct))) (.act rejectAct))

/-- Read one block per unary token, stopping immediately on a rejected block. -/
def scanProg : StackProg (Fin 4) BSym := .loop loopTest readBitProg

private lemma zero_step (tail counter bits status : List BSym) :
    StackProg.applyAct zeroAct (store (.sep :: tail) (.one :: counter) bits status) =
      store tail counter (.zero :: bits) status := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, zeroAct, store, StackAct.apply]

private lemma prefix_step (tail counter bits status : List BSym) :
    StackProg.applyAct prefixAct (store (.one :: tail) counter bits status) =
      store tail counter bits status := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, prefixAct, store, StackAct.apply]

private lemma one_step (tail counter bits status : List BSym) :
    StackProg.applyAct oneAct (store (.sep :: tail) (.one :: counter) bits status) =
      store tail counter (.one :: bits) status := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, oneAct, store, StackAct.apply]

private lemma readBit_success (b : Bool) (tail counter bits status : List BSym) :
    readBitProg.Exec (store (bitBlock b ++ tail) (.one :: counter) bits status)
      (store tail counter (bitSym b :: bits) status) (if b then 6 else 2) := by
  cases b
  · have ha : (StackProg.act zeroAct).Exec
        (store (.sep :: tail) (.one :: counter) bits status)
        (store tail counter (.zero :: bits) status) 1 := by
      rw [← zero_step]
      exact StackProg.Exec.act _ _
    exact StackProg.Exec.branchTrue (by rfl) ha
  · have hp : (StackProg.act prefixAct).Exec
        (store (.one :: .sep :: tail) (.one :: counter) bits status)
        (store (.sep :: tail) (.one :: counter) bits status) 1 := by
      simpa only [prefix_step] using
        (StackProg.Exec.act prefixAct (store (.one :: .sep :: tail) (.one :: counter) bits status))
    have hc : (StackProg.act oneAct).Exec
        (store (.sep :: tail) (.one :: counter) bits status)
        (store tail counter (.one :: bits) status) 1 := by
      rw [← one_step]
      exact StackProg.Exec.act _ _
    have hb := StackProg.Exec.branchTrue (p := .act oneAct) (q := .act rejectAct)
      (by rfl : sepTest (fun k ↦ (store (.sep :: tail) (.one :: counter) bits status k).head?) = true) hc
    have hs := StackProg.Exec.seq hp hb
    have hb1 := StackProg.Exec.branchTrue (p := .seq (.act prefixAct)
        (.branch sepTest (.act oneAct) (.act rejectAct))) (q := .act rejectAct)
      (by rfl : oneTest (fun k ↦ (store (.one :: .sep :: tail) (.one :: counter) bits status k).head?) = true) hs
    exact StackProg.Exec.branchFalse (by rfl) hb1

/-- Successful canonical block scans consume one counter token per entry. -/
theorem scanProg_success (xs : List Bool) (tail bits status : List BSym) :
    scanProg.Exec
      (store (bitBlocks xs ++ tail) (List.replicate xs.length .one) bits (.one :: status))
      (store tail [] ((xs.map bitSym).reverse ++ bits) (.one :: status))
      (xs.foldr (fun b n ↦ (if b then 8 else 4) + n) 1) := by
  induction xs generalizing bits with
  | nil =>
    apply StackProg.Exec.loopFalse
    rfl
  | cons b xs ih =>
    have ht : loopTest (fun k ↦
        (store (bitBlock b ++ (bitBlocks xs ++ tail))
          (.one :: List.replicate xs.length .one) bits (.one :: status) k).head?) = true := rfl
    have hb := readBit_success b (bitBlocks xs ++ tail)
      (List.replicate xs.length .one) bits (.one :: status)
    have hi := ih (bitSym b :: bits)
    have he := StackProg.Exec.loopTrue ht hb hi
    cases b <;> simpa [scanProg, bitBlocks, bitBlock, bitSym, List.reverse_cons,
      List.append_assoc, List.replicate_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

/-- The per-entry scanner reads the canonical encodings of zero and one. -/
theorem bitBlock_eq_encNat (b : Bool) : bitBlock b = encNat (if b then 1 else 0) := by
  cases b <;> decide

/-- The block stream coincides with the published list-of-naturals encoding. -/
theorem bitBlocks_eq_encNats (xs : List Bool) :
    bitBlocks xs = encNats (xs.map (fun b ↦ if b then 1 else 0)) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    change bitBlock b ++ bitBlocks xs =
      encNat (if b then 1 else 0) ++ encNats (xs.map (fun b ↦ if b then 1 else 0))
    rw [bitBlock_eq_encNat, ih]

/-- Successful scans have a linear bound in the number of entries. -/
theorem scan_cost_bound (xs : List Bool) :
    xs.foldr (fun b n ↦ (if b then 8 else 4) + n) 1 ≤ 8 * xs.length + 1 := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    cases b <;> simp_all <;> omega


private lemma reject_step (input counter bits status : List BSym) :
    StackProg.applyAct rejectAct (store input counter bits status) =
      store input counter bits (.zero :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, rejectAct, store, StackAct.apply]

private lemma readBit_bad_head (input counter bits status : List BSym)
    (hsep : sepTest (fun k ↦ (store input (.one :: counter) bits status k).head?) = false)
    (hone : oneTest (fun k ↦ (store input (.one :: counter) bits status k).head?) = false) :
    readBitProg.Exec (store input (.one :: counter) bits status)
      (store input (.one :: counter) bits (.zero :: status)) 3 := by
  have ha : (StackProg.act rejectAct).Exec (store input (.one :: counter) bits status)
      (store input (.one :: counter) bits (.zero :: status)) 1 := by
    simpa only [reject_step] using
      (StackProg.Exec.act rejectAct (store input (.one :: counter) bits status))
  have hb := StackProg.Exec.branchFalse (p := .seq (.act prefixAct)
      (.branch sepTest (.act oneAct) (.act rejectAct))) hone ha
  exact StackProg.Exec.branchFalse hsep hb

private lemma readBit_bad_one (tail counter bits status : List BSym)
    (hsep : sepTest (fun k ↦ (store tail (.one :: counter) bits status k).head?) = false) :
    readBitProg.Exec (store (.one :: tail) (.one :: counter) bits status)
      (store tail (.one :: counter) bits (.zero :: status)) 6 := by
  have hp : (StackProg.act prefixAct).Exec
      (store (.one :: tail) (.one :: counter) bits status)
      (store tail (.one :: counter) bits status) 1 := by
    simpa only [prefix_step] using
      (StackProg.Exec.act prefixAct (store (.one :: tail) (.one :: counter) bits status))
  have ha : (StackProg.act rejectAct).Exec
      (store tail (.one :: counter) bits status)
      (store tail (.one :: counter) bits (.zero :: status)) 1 := by
    simpa only [reject_step] using
      (StackProg.Exec.act rejectAct (store tail (.one :: counter) bits status))
  have hb := StackProg.Exec.branchFalse (p := .act oneAct) hsep ha
  have hs := StackProg.Exec.seq hp hb
  have hone := StackProg.Exec.branchTrue (q := .act rejectAct)
    (by rfl : oneTest (fun k ↦ (store (.one :: tail) (.one :: counter) bits status k).head?) = true) hs
  exact StackProg.Exec.branchFalse (by rfl) hone


/-- Each iteration either consumes a valid Boolean block or marks rejection. -/
private lemma readBit_progress (input counter bits status : List BSym) :
    (∃ b tail, input = bitBlock b ++ tail) ∨
    ∃ input' cost, cost ≤ 6 ∧
      readBitProg.Exec (store input (.one :: counter) bits status)
        (store input' (.one :: counter) bits (.zero :: status)) cost := by
  cases input with
  | nil =>
    right
    refine ⟨[], 3, by omega, ?_⟩
    exact readBit_bad_head [] counter bits status (by rfl) (by rfl)
  | cons a tail =>
    cases a with
    | zero =>
      right
      refine ⟨.zero :: tail, 3, by omega, ?_⟩
      exact readBit_bad_head (.zero :: tail) counter bits status (by rfl) (by rfl)
    | minus =>
      right
      refine ⟨.minus :: tail, 3, by omega, ?_⟩
      exact readBit_bad_head (.minus :: tail) counter bits status (by rfl) (by rfl)
    | sep =>
      left
      exact ⟨false, tail, rfl⟩
    | one =>
      cases tail with
      | nil =>
        right
        refine ⟨[], 6, by omega, ?_⟩
        exact readBit_bad_one [] counter bits status (by rfl)
      | cons a tail =>
        cases a with
        | sep =>
          left
          exact ⟨true, tail, rfl⟩
        | zero =>
          right
          refine ⟨.zero :: tail, 6, by omega, ?_⟩
          exact readBit_bad_one (.zero :: tail) counter bits status (by rfl)
        | one =>
          right
          refine ⟨.one :: tail, 6, by omega, ?_⟩
          exact readBit_bad_one (.one :: tail) counter bits status (by rfl)
        | minus =>
          right
          refine ⟨.minus :: tail, 6, by omega, ?_⟩
          exact readBit_bad_one (.minus :: tail) counter bits status (by rfl)


/-- On arbitrary input, the scanner halts in at most eight steps per unary token plus one. -/
theorem scanProg_total (n : ℕ) (input bits status : List BSym) :
    ∃ input' counter' bits' status' steps,
      steps ≤ 8 * n + 1 ∧
      scanProg.Exec (store input (List.replicate n .one) bits (.one :: status))
        (store input' counter' bits' status') steps := by
  induction n generalizing input bits with
  | zero =>
    refine ⟨input, [], bits, .one :: status, 1, by simp, ?_⟩
    apply StackProg.Exec.loopFalse
    rfl
  | succ n ih =>
    rcases readBit_progress input (List.replicate n .one) bits (.one :: status) with
      ⟨b, tail, rfl⟩ | ⟨input', cost, hcost, hbody⟩
    · obtain ⟨out, counter', bits', status', steps, hsteps, hrun⟩ := ih tail (bitSym b :: bits)
      have ht : loopTest (fun k ↦
          (store (bitBlock b ++ tail) (.one :: List.replicate n .one) bits (.one :: status) k).head?) =
            true := rfl
      have hb := readBit_success b tail (List.replicate n .one) bits (.one :: status)
      have he := StackProg.Exec.loopTrue ht hb hrun
      refine ⟨out, counter', bits', status', 1 + (if b then 6 else 2) + 1 + steps, ?_, ?_⟩
      · cases b <;> simp_all <;> omega
      · simpa only [scanProg, List.replicate_succ] using he
    · have ht : loopTest (fun k ↦
          (store input (.one :: List.replicate n .one) bits (.one :: status) k).head?) = true := rfl
      have hstop : scanProg.Exec
          (store input' (.one :: List.replicate n .one) bits (.zero :: .one :: status))
          (store input' (.one :: List.replicate n .one) bits (.zero :: .one :: status)) 1 := by
        apply StackProg.Exec.loopFalse
        rfl
      have he := StackProg.Exec.loopTrue ht hbody hstop
      refine ⟨input', .one :: List.replicate n .one, bits, .zero :: .one :: status,
        1 + cost + 1 + 1, ?_, ?_⟩
      · omega
      · simpa only [scanProg, List.replicate_succ] using he


private def completeTest (h : Fin 4 → Option BSym) : Bool :=
  h 0 == none && h 3 == some BSym.one

private def acceptAct (_h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 3 then .push .one else .keep

/-- Check both end-of-input and the scanner's success status. -/
def completeProg : StackProg (Fin 4) BSym :=
  .branch completeTest (.act acceptAct) (.act rejectAct)

/-- Scan a unary number of Boolean blocks and then require end-of-input. -/
def scanCompleteProg : StackProg (Fin 4) BSym := .seq scanProg completeProg

private lemma accept_step (input counter bits status : List BSym) :
    StackProg.applyAct acceptAct (store input counter bits status) =
      store input counter bits (.one :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, acceptAct, store, StackAct.apply]

/-- Completion accepts an exhausted input whose scanner status is successful. -/
theorem completeProg_success (counter bits status : List BSym) :
    completeProg.Exec (store [] counter bits (.one :: status))
      (store [] counter bits (.one :: .one :: status)) 2 := by
  have ha : (StackProg.act acceptAct).Exec (store [] counter bits (.one :: status))
      (store [] counter bits (.one :: .one :: status)) 1 := by
    simpa only [accept_step] using
      (StackProg.Exec.act acceptAct (store [] counter bits (.one :: status)))
  exact StackProg.Exec.branchTrue (by rfl) ha

/-- Completion always halts in exactly two source steps. -/
theorem completeProg_total (input counter bits status : List BSym) :
    ∃ marker : BSym, completeProg.Exec (store input counter bits status)
      (store input counter bits (marker :: status)) 2 := by
  cases ht : completeTest (fun k ↦ (store input counter bits status k).head?) with
  | false =>
    refine ⟨.zero, ?_⟩
    have ha : (StackProg.act rejectAct).Exec (store input counter bits status)
        (store input counter bits (.zero :: status)) 1 := by
      simpa only [reject_step] using (StackProg.Exec.act rejectAct (store input counter bits status))
    exact StackProg.Exec.branchFalse ht ha
  | true =>
    refine ⟨.one, ?_⟩
    have ha : (StackProg.act acceptAct).Exec (store input counter bits status)
        (store input counter bits (.one :: status)) 1 := by
      simpa only [accept_step] using (StackProg.Exec.act acceptAct (store input counter bits status))
    exact StackProg.Exec.branchTrue ht ha

/-- The combined program terminates on every input in linear time in the unary count. -/
theorem scanCompleteProg_total (n : ℕ) (input bits status : List BSym) :
    ∃ input' counter' bits' status' steps,
      steps ≤ 8 * n + 4 ∧
      scanCompleteProg.Exec (store input (List.replicate n .one) bits (.one :: status))
        (store input' counter' bits' status') steps := by
  obtain ⟨input', counter', bits', status', steps, hsteps, hscan⟩ := scanProg_total n input bits status
  obtain ⟨marker, hfinish⟩ := completeProg_total input' counter' bits' status'
  refine ⟨input', counter', bits', marker :: status', steps + 3, by omega, ?_⟩
  exact StackProg.Exec.seq hscan hfinish

/-- On an exact canonical bit stream, the completion marker reports success. -/
theorem scanCompleteProg_success (xs : List Bool) (bits status : List BSym) :
    ∃ steps, steps ≤ 8 * xs.length + 4 ∧
      scanCompleteProg.Exec
        (store (bitBlocks xs) (List.replicate xs.length .one) bits (.one :: status))
        (store [] [] ((xs.map bitSym).reverse ++ bits) (.one :: .one :: status)) steps := by
  let steps := xs.foldr (fun b n ↦ (if b then 8 else 4) + n) 1
  refine ⟨steps + 3, ?_, ?_⟩
  · have h := scan_cost_bound xs
    simp only [steps]
    omega
  · have hscan := scanProg_success xs [] bits status
    have hfinish := completeProg_success [] ((xs.map bitSym).reverse ++ bits) status
    simpa only [scanCompleteProg, List.append_nil, steps] using StackProg.Exec.seq hscan hfinish

end TensorAdjacencyScan

namespace TensorSquareScan

open StackProgPortLift TensorUnarySquare TensorAdjacencyScan

/-- The square macro operates on ports 1, 2, 3, 4. -/
def squarePorts : Fin 4 ↪ Fin 6 := ⟨![1, 2, 3, 4], by decide⟩

/-- The scanner operates on ports 0, 2, 3, 5. -/
def scanPorts : Fin 4 ↪ Fin 6 := ⟨![0, 2, 3, 5], by decide⟩

/-- Explicit, finite inverse maps for the two concrete port embeddings. -/
def squareDecode : Fin 6 → Option (Fin 4) := ![none, some 0, some 1, some 2, some 3, none]
def scanDecode : Fin 6 → Option (Fin 4) := ![some 0, none, some 1, some 2, none, some 3]

private theorem squareDecode_correct (l : Fin 6) (k : Fin 4) :
    squareDecode l = some k ↔ squarePorts k = l := by
  fin_cases l <;> fin_cases k <;> decide

private theorem scanDecode_correct (l : Fin 6) (k : Fin 4) :
    scanDecode l = some k ↔ scanPorts k = l := by
  fin_cases l <;> fin_cases k <;> decide

/-- Six shared ports: input, source, count, bits, scratch, status. -/
def store6 (input src count bits tmp status : List BSym) : Fin 6 → List BSym :=
  fun k ↦ if k = 0 then input else if k = 1 then src else if k = 2 then count
    else if k = 3 then bits else if k = 4 then tmp else status

/-- Square the source counter and then scan exactly that many Boolean blocks.
    The two independently verified programs run on one six-stack store. -/
def squareScanProg : StackProg (Fin 6) BSym :=
  .seq (liftProgC squarePorts squareDecode squareProg) (liftProgC scanPorts scanDecode scanCompleteProg)

theorem squareScan_success (n : ℕ) (xs : List Bool) (status : List BSym)
    (hlen : xs.length = n * n) :
    ∃ steps, steps ≤ 8 * (n * n) + 4 ∧
      squareScanProg.Exec
        (store6 (bitBlocks xs) (List.replicate n .one) [] [] [] (.one :: status))
        (write scanPorts
          (TensorAdjacencyScan.store [] [] ((xs.map bitSym).reverse) (.one :: .one :: status))
          (write squarePorts
            (TensorUnarySquare.store4 (List.replicate n .one) (List.replicate (n*n) .one) [] [])
            (store6 (bitBlocks xs) (List.replicate n .one) [] [] [] (.one :: status))))
        (((6*n+3)+1+((6*n+7)*n+1)) + 1 + steps) := by
  classical
  let base := store6 (bitBlocks xs) (List.replicate n .one) [] [] [] (.one :: status)
  let squareEnd := TensorUnarySquare.store4 (List.replicate n .one) (List.replicate (n*n) .one) [] []
  have hbase : project squarePorts base =
      TensorUnarySquare.store4 (List.replicate n .one) [] [] [] := by
    funext k
    fin_cases k <;> simp [project, squarePorts, base, store6, TensorUnarySquare.store4]
  have hout0 : ∀ k : Fin 4, squarePorts k ≠ (0 : Fin 6) := by
    intro k
    fin_cases k <;> decide
  have hout5 : ∀ k : Fin 4, squarePorts k ≠ (5 : Fin 6) := by
    intro k
    fin_cases k <;> decide
  have hm0 : write squarePorts squareEnd base 0 = bitBlocks xs := by
    simpa [base, store6] using (StackProgPortLift.write_outside squarePorts squareEnd base hout0)
  have hm5 : write squarePorts squareEnd base 5 = .one :: status := by
    simpa [base, store6] using (StackProgPortLift.write_outside squarePorts squareEnd base hout5)
  have hm2 : write squarePorts squareEnd base 2 = List.replicate (n*n) .one := by
    simpa [squarePorts, squareEnd, TensorUnarySquare.store4] using
      (StackProgPortLift.write_at squarePorts squareEnd base (1 : Fin 4))
  have hm3 : write squarePorts squareEnd base 3 = [] := by
    simpa [squarePorts, squareEnd, TensorUnarySquare.store4] using
      (StackProgPortLift.write_at squarePorts squareEnd base (2 : Fin 4))
  have hcompat : project scanPorts (write squarePorts squareEnd base) =
      TensorAdjacencyScan.store (bitBlocks xs) (List.replicate xs.length .one) [] (.one :: status) := by
    funext k
    fin_cases k <;> simp [project, scanPorts, TensorAdjacencyScan.store, hm0, hm2, hm3, hm5, hlen]
  obtain ⟨steps, hsteps, hrun⟩ := scanCompleteProg_success xs [] status
  have hrun' : scanCompleteProg.Exec
      (TensorAdjacencyScan.store (bitBlocks xs) (List.replicate xs.length .one) [] (.one :: status))
      (TensorAdjacencyScan.store [] [] ((xs.map bitSym).reverse) (.one :: .one :: status)) steps := by
    simpa using hrun
  refine ⟨steps, by simpa [hlen] using hsteps, ?_⟩
  have h := lift_seq_exec squarePorts scanPorts (squareProg_exec n) hrun' base hbase hcompat
  simpa only [squareScanProg, liftProgC_eq_liftProg squarePorts squareDecode squareDecode_correct,
    liftProgC_eq_liftProg scanPorts scanDecode scanDecode_correct, base, squareEnd] using h

/-- The composite also halts on every input, bounded by the quadratic cost
    of making the unary square plus the linear-in-square scanner cost. -/
theorem squareScan_total (n : ℕ) (input status : List BSym) :
    ∃ input' counter' bits' status' steps,
      steps ≤ 8 * (n*n) + 4 ∧
      squareScanProg.Exec
        (store6 input (List.replicate n .one) [] [] [] (.one :: status))
        (write scanPorts (TensorAdjacencyScan.store input' counter' bits' status')
          (write squarePorts
            (TensorUnarySquare.store4 (List.replicate n .one) (List.replicate (n*n) .one) [] [])
            (store6 input (List.replicate n .one) [] [] [] (.one :: status))))
        (((6*n+3)+1+((6*n+7)*n+1)) + 1 + steps) := by
  classical
  let base := store6 input (List.replicate n .one) [] [] [] (.one :: status)
  let squareEnd := TensorUnarySquare.store4 (List.replicate n .one) (List.replicate (n*n) .one) [] []
  have hbase : project squarePorts base =
      TensorUnarySquare.store4 (List.replicate n .one) [] [] [] := by
    funext k
    fin_cases k <;> simp [project, squarePorts, base, store6, TensorUnarySquare.store4]
  have hout0 : ∀ k : Fin 4, squarePorts k ≠ (0 : Fin 6) := by
    intro k
    fin_cases k <;> decide
  have hout5 : ∀ k : Fin 4, squarePorts k ≠ (5 : Fin 6) := by
    intro k
    fin_cases k <;> decide
  have hm0 : write squarePorts squareEnd base 0 = input := by
    simpa [base, store6] using (StackProgPortLift.write_outside squarePorts squareEnd base hout0)
  have hm5 : write squarePorts squareEnd base 5 = .one :: status := by
    simpa [base, store6] using (StackProgPortLift.write_outside squarePorts squareEnd base hout5)
  have hm2 : write squarePorts squareEnd base 2 = List.replicate (n*n) .one := by
    simpa [squarePorts, squareEnd, TensorUnarySquare.store4] using
      (StackProgPortLift.write_at squarePorts squareEnd base (1 : Fin 4))
  have hm3 : write squarePorts squareEnd base 3 = [] := by
    simpa [squarePorts, squareEnd, TensorUnarySquare.store4] using
      (StackProgPortLift.write_at squarePorts squareEnd base (2 : Fin 4))
  have hcompat : project scanPorts (write squarePorts squareEnd base) =
      TensorAdjacencyScan.store input (List.replicate (n*n) .one) [] (.one :: status) := by
    funext k
    fin_cases k <;> simp [project, scanPorts, TensorAdjacencyScan.store, hm0, hm2, hm3, hm5]
  obtain ⟨input', counter', bits', status', steps, hsteps, hrun⟩ :=
    scanCompleteProg_total (n*n) input [] status
  refine ⟨input', counter', bits', status', steps, hsteps, ?_⟩
  have h := lift_seq_exec squarePorts scanPorts (squareProg_exec n) hrun base hbase hcompat
  simpa only [squareScanProg, liftProgC_eq_liftProg squarePorts squareDecode squareDecode_correct,
    liftProgC_eq_liftProg scanPorts scanDecode scanDecode_correct, base, squareEnd] using h

/-- When the unary dimension was capped by m, the entire composite has
    an explicit quadratic cost bound in m, even for malformed scanner input. -/
theorem squareScan_total_capped (n m : ℕ) (input status : List BSym) (hnm : n ≤ m) :
    ∃ input' counter' bits' status' steps,
      steps ≤ 14 * (m*m) + 13*m + 10 ∧
      squareScanProg.Exec
        (store6 input (List.replicate n .one) [] [] [] (.one :: status))
        (write scanPorts (TensorAdjacencyScan.store input' counter' bits' status')
          (write squarePorts
            (TensorUnarySquare.store4 (List.replicate n .one) (List.replicate (n*n) .one) [] [])
            (store6 input (List.replicate n .one) [] [] [] (.one :: status)))) steps := by
  obtain ⟨input', counter', bits', status', steps, hsteps, hrun⟩ := squareScan_total n input status
  refine ⟨input', counter', bits', status', ((6*n+3)+1+((6*n+7)*n+1)) + 1 + steps, ?_, hrun⟩
  have hsq : n*n ≤ m*m := Nat.mul_le_mul hnm hnm
  nlinarith

/-- The scanner leaves the original unary source counter in port 1 intact. -/
theorem squareScan_preserves_source (n : ℕ) (input status input' counter' bits' status' : List BSym) :
    (write scanPorts (TensorAdjacencyScan.store input' counter' bits' status')
      (write squarePorts
        (TensorUnarySquare.store4 (List.replicate n .one) (List.replicate (n*n) .one) [] [])
        (store6 input (List.replicate n .one) [] [] [] (.one :: status)))) 1 =
      List.replicate n .one := by
  classical
  have hout : ∀ k : Fin 4, scanPorts k ≠ (1 : Fin 6) := by
    intro k
    fin_cases k <;> decide
  rw [StackProgPortLift.write_outside scanPorts _ _ hout]
  simpa [squarePorts, TensorUnarySquare.store4] using
    (StackProgPortLift.write_at squarePorts
      (TensorUnarySquare.store4 (List.replicate n .one) (List.replicate (n*n) .one) [] [])
      (store6 input (List.replicate n .one) [] [] [] (.one :: status)) (0 : Fin 4))

end TensorSquareScan

namespace TensorPrefixDecode

open StackProgPortLift TensorSquareScan

def graphPorts : Fin 6 ↪ Fin 7 := ⟨![0,2,3,1,5,6], by decide⟩
def graphInverse : Fin 7 → Option (Fin 6) := ![some 0,some 3,some 1,some 2,none,some 4,some 5]

private theorem graphInverse_correct (l : Fin 7) (k : Fin 6) :
    graphInverse l = some k ↔ graphPorts k = l := by fin_cases l <;> fin_cases k <;> decide

/-- Generate an input-length cap, parse the dimension, then square and scan
    the matrix blocks only if all earlier stages reported success. -/
def cappedGraphScanProg : StackProg (Fin 7) BSym :=
  .seq cappedPrefixProg
    (.branch accepted (liftProgC graphPorts graphInverse squareScanProg) (.act keepAct))

/-- The actual composed cap, prefix, unary-square and matrix-block scanner
    halts on every input within a quadratic number of stack-program steps. -/
theorem cappedGraphScan_total (input status : List BSym) :
    ∃ out steps,
      cappedGraphScanProg.Exec (store7 input [] [] [] [] [] status) out steps ∧
      steps ≤ 23*(input.length*input.length)+40*input.length+28 := by
  obtain ⟨mid, psteps, hp, hpbound, hshape⟩ := cappedPrefix_total_structured input status
  rcases hshape with ⟨rest, n, fuel, tail, rfl, hsum⟩ | hbad
  · have hnm : n ≤ input.length := by omega
    obtain ⟨rin, counter, bits, st, gsteps, hgbound, hg⟩ :=
      squareScan_total_capped n input.length rest tail hnm
    have hproject : project graphPorts
        (store7 rest [] (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: tail)) =
        TensorSquareScan.store6 rest (List.replicate n .one) [] [] [] (.one :: tail) := by
      funext k
      fin_cases k <;> simp [project, graphPorts, store7, TensorSquareScan.store6]
    have hrun := lift_exec graphPorts hg
      (store7 rest [] (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: tail)) hproject
    have hrun' := hrun
    rw [← liftProgC_eq_liftProg graphPorts graphInverse graphInverse_correct squareScanProg] at hrun'
    have ht : accepted (fun k ↦
        (store7 rest [] (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: tail) k).head?) = true := by rfl
    have hb := StackProg.Exec.branchTrue (q := .act keepAct) ht hrun'
    have he := StackProg.Exec.seq hp hb
    refine ⟨_, psteps+1+(1+gsteps), he, ?_⟩
    nlinarith
  · have ht : accepted (fun k ↦ (mid k).head?) = false := by
      simp [accepted, hbad]
    have hb := StackProg.Exec.branchFalse (p := liftProgC graphPorts graphInverse squareScanProg)
      ht (keep_exec mid)
    have he := StackProg.Exec.seq hp hb
    refine ⟨mid, psteps+1+2, he, ?_⟩
    nlinarith

end TensorPrefixDecode

namespace TensorAdjacencyScan

/-- Decode one canonical Boolean-valued block and return the unconsumed tail. -/
def decodeBit : List BSym → Option (Bool × List BSym)
  | .sep :: tail => some (false, tail)
  | .one :: .sep :: tail => some (true, tail)
  | _ => none

/-- Decode a fixed number of Boolean-valued blocks. -/
def decodeBits : ℕ → List BSym → Option (List Bool × List BSym)
  | 0, input => some ([], input)
  | n+1, input => do
      let (b, rest) ← decodeBit input
      let (bs, tail) ← decodeBits n rest
      some (b :: bs, tail)

theorem decodeBit_enc (b : Bool) (tail : List BSym) :
    decodeBit (bitBlock b ++ tail) = some (b, tail) := by
  cases b <;> rfl

theorem decodeBits_enc (bs : List Bool) (tail : List BSym) :
    decodeBits bs.length (bitBlocks bs ++ tail) = some (bs, tail) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [bitBlocks] at ih
    cases b <;> simp [decodeBits, decodeBit, bitBlocks, bitBlock, ih]

/-- A successful single-block decode has consumed exactly its canonical block. -/
theorem decodeBit_sound (input : List BSym) (b : Bool) (tail : List BSym)
    (h : decodeBit input = some (b, tail)) : input = bitBlock b ++ tail := by
  cases input with
  | nil => simp [decodeBit] at h
  | cons a xs =>
    cases a with
    | sep =>
      simp only [decodeBit, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | zero => simp [decodeBit] at h
    | minus => simp [decodeBit] at h
    | one =>
      cases xs with
      | nil => simp [decodeBit] at h
      | cons c xs =>
        cases c <;> simp [decodeBit, bitBlock] at h ⊢ <;> aesop

/-- Successful decoding identifies the exact number of blocks and remaining tail. -/
theorem decodeBits_sound (n : ℕ) (input : List BSym) (bs : List Bool) (tail : List BSym)
    (h : decodeBits n input = some (bs, tail)) :
    bs.length = n ∧ input = bitBlocks bs ++ tail := by
  induction n generalizing input bs with
  | zero =>
    simp only [decodeBits, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [bitBlocks]
  | succ n ih =>
    cases hp : decodeBit input with
    | none => simp [decodeBits, hp] at h
    | some p =>
      rcases p with ⟨b, rest⟩
      cases hq : decodeBits n rest with
      | none => simp [decodeBits, hp, hq] at h
      | some q =>
        rcases q with ⟨bs', tail'⟩
        simp [decodeBits, hp, hq] at h
        rcases h with ⟨rfl, rfl⟩
        obtain ⟨hlen, hinput⟩ := ih rest bs' hq
        have hfirst := decodeBit_sound input b rest hp
        constructor
        · simp [hlen]
        · rw [hfirst, hinput]
          simp [bitBlocks, List.append_assoc]

/-- Every successful pure decode is realized by the checked stack scanner. -/
theorem scanProg_of_decode (n : ℕ) (input : List BSym) (bs : List Bool) (tail bits status : List BSym)
    (h : decodeBits n input = some (bs, tail)) :
    ∃ steps, steps ≤ 8*n+1 ∧
      scanProg.Exec (store input (List.replicate n .one) bits (.one :: status))
        (store tail [] ((bs.map bitSym).reverse ++ bits) (.one :: status)) steps := by
  obtain ⟨hlen, hin⟩ := decodeBits_sound n input bs tail h
  subst n
  subst input
  exact ⟨_, scan_cost_bound bs, scanProg_success bs tail bits status⟩


/-- A non-decodable next block makes the scanner mark an error. -/
private lemma decodeBit_none_reject (input counter bits status : List BSym)
    (h : decodeBit input = none) :
    ∃ input' cost, cost ≤ 6 ∧
      readBitProg.Exec (store input (.one :: counter) bits status)
        (store input' (.one :: counter) bits (.zero :: status)) cost := by
  cases input with
  | nil =>
    exact ⟨[], 3, by omega, readBit_bad_head [] counter bits status (by rfl) (by rfl)⟩
  | cons a tail =>
    cases a with
    | zero =>
      exact ⟨.zero :: tail, 3, by omega,
        readBit_bad_head (.zero :: tail) counter bits status (by rfl) (by rfl)⟩
    | minus =>
      exact ⟨.minus :: tail, 3, by omega,
        readBit_bad_head (.minus :: tail) counter bits status (by rfl) (by rfl)⟩
    | sep => simp [decodeBit] at h
    | one =>
      cases tail with
      | nil => exact ⟨[], 6, by omega, readBit_bad_one [] counter bits status (by rfl)⟩
      | cons a tail =>
        cases a with
        | sep => simp [decodeBit] at h
        | zero => exact ⟨.zero :: tail, 6, by omega,
            readBit_bad_one (.zero :: tail) counter bits status (by rfl)⟩
        | one => exact ⟨.one :: tail, 6, by omega,
            readBit_bad_one (.one :: tail) counter bits status (by rfl)⟩
        | minus => exact ⟨.minus :: tail, 6, by omega,
            readBit_bad_one (.minus :: tail) counter bits status (by rfl)⟩

/-- If n blocks cannot be decoded, the stack program marks rejection within 8n+1 steps. -/
theorem scanProg_decode_none (n : ℕ) (input bits status : List BSym)
    (h : decodeBits n input = none) :
    ∃ input' counter' bits' steps,
      steps ≤ 8 * n + 1 ∧
      scanProg.Exec (store input (List.replicate n .one) bits (.one :: status))
        (store input' counter' bits' (.zero :: .one :: status)) steps := by
  induction n generalizing input bits with
  | zero => simp [decodeBits] at h
  | succ n ih =>
    cases hb : decodeBit input with
    | none =>
      obtain ⟨input', cost, hc, hbody⟩ :=
        decodeBit_none_reject input (List.replicate n .one) bits (.one :: status) hb
      have ht : loopTest (fun k ↦
          (store input (.one :: List.replicate n .one) bits (.one :: status) k).head?) = true := rfl
      have hstop : scanProg.Exec
          (store input' (.one :: List.replicate n .one) bits (.zero :: .one :: status))
          (store input' (.one :: List.replicate n .one) bits (.zero :: .one :: status)) 1 := by
        apply StackProg.Exec.loopFalse
        rfl
      have he := StackProg.Exec.loopTrue ht hbody hstop
      refine ⟨input', .one :: List.replicate n .one, bits, 1 + cost + 1 + 1, ?_, ?_⟩
      · omega
      · simpa only [scanProg, List.replicate_succ] using he
    | some pair =>
      rcases pair with ⟨b, rest⟩
      have hrest : decodeBits n rest = none := by
        cases hr : decodeBits n rest with
        | none => rfl
        | some result =>
          rcases result with ⟨bs, tail⟩
          simp [decodeBits, hb, hr] at h
      have hin := decodeBit_sound input b rest hb
      obtain ⟨input', counter', bits', cost, hc, hrun⟩ := ih rest (bitSym b :: bits) hrest
      have ht : loopTest (fun k ↦
          (store (bitBlock b ++ rest) (.one :: List.replicate n .one) bits (.one :: status) k).head?) =
            true := rfl
      have hbody := readBit_success b rest (List.replicate n .one) bits (.one :: status)
      have he := StackProg.Exec.loopTrue ht hbody hrun
      refine ⟨input', counter', bits', 1 + (if b then 6 else 2) + 1 + cost, ?_, ?_⟩
      · cases b <;> simp_all <;> omega
      · simpa only [scanProg, List.replicate_succ, hin] using he


/-- Completion rejects whenever the scanner already marked an error. -/
private theorem completeProg_bad_status (input counter bits status : List BSym) :
    completeProg.Exec (store input counter bits (.zero :: status))
      (store input counter bits (.zero :: .zero :: status)) 2 := by
  have ha : (StackProg.act rejectAct).Exec (store input counter bits (.zero :: status))
      (store input counter bits (.zero :: .zero :: status)) 1 := by
    simpa only [reject_step] using
      (StackProg.Exec.act rejectAct (store input counter bits (.zero :: status)))
  have ht : completeTest (fun k ↦ (store input counter bits (.zero :: status) k).head?) = false := by
    simp [completeTest, store]
  exact StackProg.Exec.branchFalse ht ha

/-- Completion rejects trailing symbols after the required blocks. -/
private theorem completeProg_extra_input (a : BSym) (tail counter bits status : List BSym) :
    completeProg.Exec (store (a :: tail) counter bits (.one :: status))
      (store (a :: tail) counter bits (.zero :: .one :: status)) 2 := by
  have ha : (StackProg.act rejectAct).Exec (store (a :: tail) counter bits (.one :: status))
      (store (a :: tail) counter bits (.zero :: .one :: status)) 1 := by
    simpa only [reject_step] using
      (StackProg.Exec.act rejectAct (store (a :: tail) counter bits (.one :: status)))
  exact StackProg.Exec.branchFalse (by rfl) ha

/-- An input that fails block decoding causes the complete scanner to reject. -/
theorem scanComplete_decode_none (n : ℕ) (input bits status : List BSym)
    (h : decodeBits n input = none) :
    ∃ input' counter' bits' steps, steps ≤ 8 * n + 4 ∧
      scanCompleteProg.Exec (store input (List.replicate n .one) bits (.one :: status))
        (store input' counter' bits' (.zero :: .zero :: .one :: status)) steps := by
  obtain ⟨input', counter', bits', steps, hs, hr⟩ := scanProg_decode_none n input bits status h
  have hf := completeProg_bad_status input' counter' bits' (.one :: status)
  refine ⟨input', counter', bits', steps + 3, by omega, ?_⟩
  exact StackProg.Exec.seq hr hf

/-- A decoded prefix with extra trailing input is rejected. -/
theorem scanComplete_decode_extra (n : ℕ) (input bits status : List BSym)
    (bs : List Bool) (a : BSym) (tail : List BSym)
    (h : decodeBits n input = some (bs, a :: tail)) :
    ∃ steps, steps ≤ 8*n+4 ∧
      scanCompleteProg.Exec (store input (List.replicate n .one) bits (.one :: status))
        (store (a :: tail) [] ((bs.map bitSym).reverse ++ bits) (.zero :: .one :: status)) steps := by
  obtain ⟨steps, hs, hr⟩ := scanProg_of_decode n input bs (a :: tail) bits status h
  have hf := completeProg_extra_input a tail [] ((bs.map bitSym).reverse ++ bits) status
  refine ⟨steps+3, by omega, ?_⟩
  exact StackProg.Exec.seq hr hf

/-- An exact decoded stream is accepted by the complete scanner. -/
theorem scanComplete_decode_exact (n : ℕ) (input bits status : List BSym)
    (bs : List Bool) (h : decodeBits n input = some (bs, [])) :
    ∃ steps, steps ≤ 8*n+4 ∧
      scanCompleteProg.Exec (store input (List.replicate n .one) bits (.one :: status))
        (store [] [] ((bs.map bitSym).reverse ++ bits) (.one :: .one :: status)) steps := by
  obtain ⟨steps, hs, hr⟩ := scanProg_of_decode n input bs [] bits status h
  have hf := completeProg_success [] ((bs.map bitSym).reverse ++ bits) status
  refine ⟨steps+3, by omega, ?_⟩
  exact StackProg.Exec.seq hr hf


theorem exec_det {K A : Type} {p : StackProg K A} {s t : K → List A} {n : ℕ}
    (h : p.Exec s t n) : ∀ {u : K → List A} {m : ℕ}, p.Exec s u m → t = u := by
  induction h with
  | act f s =>
      intro u m h2
      cases h2
      rfl
  | seq hab hbc ihab ihbc =>
      intro u m h2
      cases h2 with
      | seq hab' hbc' =>
          have e : _ = _ := ihab hab'
          rw [← e] at hbc'
          exact ihbc hbc'
  | branchTrue ht hb ih =>
      intro u m h2
      cases h2 with
      | branchTrue _ hb' => exact ih hb'
      | branchFalse hf _ =>
          rw [ht] at hf
          cases hf
  | branchFalse ht hb ih =>
      intro u m h2
      cases h2 with
      | branchFalse _ hb' => exact ih hb'
      | branchTrue hf _ =>
          rw [ht] at hf
          cases hf
  | loopFalse ht =>
      intro u m h2
      cases h2 with
      | loopFalse _ => rfl
      | loopTrue ht' _ _ =>
          rw [ht] at ht'
          cases ht'
  | loopTrue ht hb hrest ihab ihrest =>
      intro u m h2
      cases h2 with
      | loopFalse ht' =>
          rw [ht] at ht'
          cases ht'
      | loopTrue _ hb' hrest' =>
          have e : _ = _ := ihab hb'
          rw [← e] at hrest'
          exact ihrest hrest'



/-- The complete scanner accepts exactly the streams decoded as n complete Boolean blocks. -/
theorem scanComplete_accept_iff (n : ℕ) (input bits status : List BSym) :
    (∃ input' counter' bits' rest steps,
      scanCompleteProg.Exec (store input (List.replicate n .one) bits (.one :: status))
        (store input' counter' bits' (.one :: rest)) steps) ↔
      ∃ bs, decodeBits n input = some (bs, []) := by
  constructor
  · rintro ⟨input', counter', bits', rest, steps, hacc⟩
    cases hd : decodeBits n input with
    | none =>
      obtain ⟨badInput, badCounter, badBits, badSteps, _, hbad⟩ :=
        scanComplete_decode_none n input bits status hd
      have heq := exec_det hacc hbad
      have hs := congrFun heq (3 : Fin 4)
      simp [store] at hs
    | some result =>
      rcases result with ⟨bs, tail⟩
      cases tail with
      | nil => exact ⟨bs, rfl⟩
      | cons a tail =>
        obtain ⟨badSteps, _, hbad⟩ := scanComplete_decode_extra n input bits status bs a tail hd
        have heq := exec_det hacc hbad
        have hs := congrFun heq (3 : Fin 4)
        simp [store] at hs
  · rintro ⟨bs, h⟩
    obtain ⟨steps, _, hrun⟩ := scanComplete_decode_exact n input bits status bs h
    exact ⟨[], [], (bs.map bitSym).reverse ++ bits, .one :: status, steps, hrun⟩

end TensorAdjacencyScan


namespace TensorSquareScan

open StackProgPortLift TensorUnarySquare TensorAdjacencyScan

/-- Any exact scanner trace can be preceded by the checked square macro on the
    shared six-stack store, preserving its output and adding the exact cost. -/
theorem squareScan_of_scanner (n : ℕ) (input status : List BSym)
    (out : Fin 4 → List BSym) (steps : ℕ)
    (hrun : scanCompleteProg.Exec
      (TensorAdjacencyScan.store input (List.replicate (n*n) .one) [] (.one :: status)) out steps) :
    squareScanProg.Exec
      (store6 input (List.replicate n .one) [] [] [] (.one :: status))
      (write scanPorts out (write squarePorts
        (TensorUnarySquare.store4 (List.replicate n .one) (List.replicate (n*n) .one) [] [])
        (store6 input (List.replicate n .one) [] [] [] (.one :: status))))
      (((6*n+3)+1+((6*n+7)*n+1)) + 1 + steps) := by
  classical
  let base := store6 input (List.replicate n .one) [] [] [] (.one :: status)
  let squareEnd := TensorUnarySquare.store4 (List.replicate n .one) (List.replicate (n*n) .one) [] []
  have hbase : project squarePorts base = TensorUnarySquare.store4 (List.replicate n .one) [] [] [] := by
    funext k
    fin_cases k <;> simp [project, squarePorts, base, store6, TensorUnarySquare.store4]
  have hout0 : ∀ k : Fin 4, squarePorts k ≠ (0 : Fin 6) := by intro k; fin_cases k <;> decide
  have hout5 : ∀ k : Fin 4, squarePorts k ≠ (5 : Fin 6) := by intro k; fin_cases k <;> decide
  have hm0 : write squarePorts squareEnd base 0 = input := by
    simpa [base, store6] using (StackProgPortLift.write_outside squarePorts squareEnd base hout0)
  have hm5 : write squarePorts squareEnd base 5 = .one :: status := by
    simpa [base, store6] using (StackProgPortLift.write_outside squarePorts squareEnd base hout5)
  have hm2 : write squarePorts squareEnd base 2 = List.replicate (n*n) .one := by
    simpa [squarePorts, squareEnd, TensorUnarySquare.store4] using
      (StackProgPortLift.write_at squarePorts squareEnd base (1 : Fin 4))
  have hm3 : write squarePorts squareEnd base 3 = [] := by
    simpa [squarePorts, squareEnd, TensorUnarySquare.store4] using
      (StackProgPortLift.write_at squarePorts squareEnd base (2 : Fin 4))
  have hcompat : project scanPorts (write squarePorts squareEnd base) =
      TensorAdjacencyScan.store input (List.replicate (n*n) .one) [] (.one :: status) := by
    funext k
    fin_cases k <;> simp [project, scanPorts, TensorAdjacencyScan.store, hm0, hm2, hm3, hm5]
  have h := lift_seq_exec squarePorts scanPorts (squareProg_exec n) hrun base hbase hcompat
  simpa only [squareScanProg, liftProgC_eq_liftProg squarePorts squareDecode squareDecode_correct,
    liftProgC_eq_liftProg scanPorts scanDecode scanDecode_correct, base, squareEnd] using h

end TensorSquareScan


namespace TensorAdjacencyScan

/-- Acceptance fixes the complete matrix-block stream and every relevant
    scanner output: no trailing symbols, no count remaining, and precisely
    the reversed Boolean matrix entries. -/
theorem scanComplete_accepted_shape (n : ℕ) (input status rin counter bits rest : List BSym) (steps : ℕ)
    (hscan : scanCompleteProg.Exec (store input (List.replicate n .one) [] (.one :: status))
      (store rin counter bits (.one :: rest)) steps) :
    ∃ bs : List Bool, bs.length = n ∧ input = bitBlocks bs ∧
      rin = [] ∧ counter = [] ∧ bits = (bs.map bitSym).reverse := by
  obtain ⟨bs, hdecode⟩ := (scanComplete_accept_iff n input [] status).mp
    ⟨rin, counter, bits, rest, steps, hscan⟩
  obtain ⟨hlen, hin⟩ := decodeBits_sound n input bs [] hdecode
  obtain ⟨canonicalSteps, _, hcanonical⟩ := scanComplete_decode_exact n input [] status bs hdecode
  have heq := exec_det hscan hcanonical
  have h0 := congrFun heq (0 : Fin 4)
  have h1 := congrFun heq (1 : Fin 4)
  have h2 := congrFun heq (2 : Fin 4)
  refine ⟨bs, hlen, by simpa using hin, ?_, ?_, ?_⟩
  · simpa [store] using h0
  · simpa [store] using h1
  · simpa [store] using h2

end TensorAdjacencyScan

namespace TensorPrefixDecode

open StackProgPortLift TensorSquareScan TensorAdjacencyScan

/-- On every input, the combined front end halts quadratically. If it reports
    success, its output is exactly an n×n Boolean matrix, with unary n bounded
    by input length, exhausted input/count ports, and row-major bits reversed.
    Otherwise its top status is a failure. -/
theorem cappedGraphScan_total_shape (input status : List BSym) :
    ∃ out steps,
      cappedGraphScanProg.Exec (store7 input [] [] [] [] [] status) out steps ∧
      steps ≤ 23*(input.length*input.length)+40*input.length+28 ∧
      ((∃ (n : ℕ) (bs : List Bool), n ≤ input.length ∧ bs.length = n*n ∧
          out 0 = [] ∧ out 1 = (bs.map bitSym).reverse ∧
          out 2 = List.replicate n .one ∧ out 3 = [] ∧ (out 6).head? = some .one) ∨
       (out 6).head? ≠ some .one) := by
  obtain ⟨mid, psteps, hp, hpbound, hshape⟩ := cappedPrefix_total_structured input status
  rcases hshape with ⟨rest, n, fuel, tail, rfl, hsum⟩ | hbad
  · have hnm : n ≤ input.length := by omega
    obtain ⟨rin, counter, bits, st, ssteps, hsbound, hscan⟩ :=
      scanCompleteProg_total (n*n) rest [] tail
    let localOut := write TensorSquareScan.scanPorts (TensorAdjacencyScan.store rin counter bits st)
      (write TensorSquareScan.squarePorts
        (TensorUnarySquare.store4 (List.replicate n .one) (List.replicate (n*n) .one) [] [])
        (TensorSquareScan.store6 rest (List.replicate n .one) [] [] [] (.one :: tail)))
    let base := store7 rest [] (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: tail)
    let out := write graphPorts localOut base
    have hsq := squareScan_of_scanner n rest tail (TensorAdjacencyScan.store rin counter bits st) ssteps hscan
    have hproj : project graphPorts base =
        TensorSquareScan.store6 rest (List.replicate n .one) [] [] [] (.one :: tail) := by
      funext k
      fin_cases k <;> simp [project, graphPorts, base, store7, TensorSquareScan.store6]
    have hlift := lift_exec graphPorts hsq base hproj
    rw [← liftProgC_eq_liftProg graphPorts graphInverse graphInverse_correct squareScanProg] at hlift
    have ht : accepted (fun k ↦ (base k).head?) = true := by simp [accepted, base, store7]
    have hb := StackProg.Exec.branchTrue (q := .act keepAct) ht hlift
    have he := StackProg.Exec.seq hp hb
    let gcost := (((6*n+3)+1+((6*n+7)*n+1))+1+ssteps)
    have hcost : gcost ≤ 14*(input.length*input.length)+13*input.length+10 := by
      have hsqle : n*n ≤ input.length*input.length := Nat.mul_le_mul hnm hnm
      dsimp [gcost]
      nlinarith
    have hstatus : out 6 = st := by
      change write graphPorts localOut base (graphPorts 5) = st
      rw [StackProgPortLift.write_at]
      change write TensorSquareScan.scanPorts _ _ (TensorSquareScan.scanPorts 3) = st
      rw [StackProgPortLift.write_at]
      simp [TensorAdjacencyScan.store]
    have hin : out 0 = rin := by
      change write graphPorts localOut base (graphPorts 0) = rin
      rw [StackProgPortLift.write_at]
      change write TensorSquareScan.scanPorts _ _ (TensorSquareScan.scanPorts 0) = rin
      rw [StackProgPortLift.write_at]
      simp [TensorAdjacencyScan.store]
    have hbits : out 1 = bits := by
      change write graphPorts localOut base (graphPorts 3) = bits
      rw [StackProgPortLift.write_at]
      change write TensorSquareScan.scanPorts _ _ (TensorSquareScan.scanPorts 2) = bits
      rw [StackProgPortLift.write_at]
      simp [TensorAdjacencyScan.store]
    have hcounter : out 3 = counter := by
      change write graphPorts localOut base (graphPorts 2) = counter
      rw [StackProgPortLift.write_at]
      change write TensorSquareScan.scanPorts _ _ (TensorSquareScan.scanPorts 1) = counter
      rw [StackProgPortLift.write_at]
      simp [TensorAdjacencyScan.store]
    have hvalue : out 2 = List.replicate n .one := by
      change write graphPorts localOut base (graphPorts 1) = _
      rw [StackProgPortLift.write_at]
      exact squareScan_preserves_source n rest tail rin counter bits st
    refine ⟨out, psteps+1+(1+gcost), he, ?_, ?_⟩
    · nlinarith
    · by_cases haccept : st.head? = some .one
      · have hst : ∃ suffix, st = .one :: suffix := by
          cases st with
          | nil => simp at haccept
          | cons sym suffix => cases sym <;> simp_all
        obtain ⟨suffix, hst⟩ := hst
        have hscan' : scanCompleteProg.Exec
            (TensorAdjacencyScan.store rest (List.replicate (n*n) .one) [] (.one :: tail))
            (TensorAdjacencyScan.store rin counter bits (.one :: suffix)) ssteps := by
          simpa only [hst] using hscan
        obtain ⟨bs, hlen, _, hrin, hcounter', hbits'⟩ :=
          scanComplete_accepted_shape (n*n) rest tail rin counter bits suffix ssteps hscan' 
        left
        refine ⟨n, bs, hnm, hlen, ?_, ?_, hvalue, ?_, ?_⟩
        · simpa [hrin] using hin
        · simpa [hbits'] using hbits
        · simpa [hcounter'] using hcounter
        · rw [hstatus, hst]
          rfl
      · right
        simpa [hstatus] using haccept
  · have ht : accepted (fun k ↦ (mid k).head?) = false := by simp [accepted, hbad]
    have hb := StackProg.Exec.branchFalse (p := liftProgC graphPorts graphInverse squareScanProg)
      ht (keep_exec mid)
    have he := StackProg.Exec.seq hp hb
    refine ⟨mid, psteps+1+2, he, ?_, Or.inr hbad⟩
    nlinarith

end TensorPrefixDecode

namespace TensorGraphPrefix3

/-- All-input parser classification: a successful marker identifies an exact
    canonical natural-number prefix and its true MSB-first digits. -/
theorem parseCanonicalBlockProg_total_canonical (input status : List BSym) :
    ∃ rest outdigits outstatus steps,
      parseCanonicalBlockProg.Exec (store input [] status) (store rest outdigits outstatus) steps ∧
      steps ≤ 3*input.length+7 ∧ outdigits.length ≤ input.length ∧
      ((∃ n, input = encNat n ++ rest ∧ outdigits = TensorCappedDecode.scannerDigits n ∧
          outstatus = .one :: .one :: status) ∨ outstatus.head? ≠ some .one) := by
  obtain ⟨digits, stop, hw, hstop⟩ := split_digit_prefix input
  subst input
  have hbound : 3*digits.length+7 ≤ 3*(digits.map digitSym ++ stop).length+7 := by
    simp only [List.length_append, List.length_map]
    omega
  have hlen : (digits.map digitSym).reverse.length ≤ (digits.map digitSym ++ stop).length := by
    simp only [List.length_reverse, List.length_map, List.length_append]
    omega
  rcases hstop with hempty | ⟨tail, hsep⟩ | ⟨tail, hminus⟩
  · subst stop
    refine ⟨[], (digits.map digitSym).reverse, .zero :: .zero :: status,
      3*digits.length+7, ?_, hbound, hlen, Or.inr (by simp)⟩
    simpa using parseCanonicalBlockProg_reject_eof digits status
  · subst stop
    rcases digit_end_cases digits with hempty | ⟨pre, htrue⟩ | ⟨pre, hfalse⟩
    · have hcanonical : digits = [] ∨ ∃ pre, digits = pre ++ [true] := Or.inl hempty
      obtain ⟨n, hn⟩ := (TensorCanonicalDigits.canonical_digits_iff digits).mp hcanonical
      refine ⟨tail, (digits.map digitSym).reverse, .one :: .one :: status, 3*digits.length+7,
        parseCanonicalBlockProg_accept digits tail status hcanonical, hbound, hlen, Or.inl ⟨n, ?_, ?_, rfl⟩⟩
      · rw [← hn]
        simp [encNat, digitSym, List.append_assoc]
      · rw [← hn]
        rfl
    · have hcanonical : digits = [] ∨ ∃ pre, digits = pre ++ [true] := Or.inr ⟨pre, htrue⟩
      obtain ⟨n, hn⟩ := (TensorCanonicalDigits.canonical_digits_iff digits).mp hcanonical
      refine ⟨tail, (digits.map digitSym).reverse, .one :: .one :: status, 3*digits.length+7,
        parseCanonicalBlockProg_accept digits tail status hcanonical, hbound, hlen, Or.inl ⟨n, ?_, ?_, rfl⟩⟩
      · rw [← hn]
        simp [encNat, digitSym, List.append_assoc]
      · rw [← hn]
        rfl
    · subst digits
      exact ⟨tail, ((pre ++ [false]).map digitSym).reverse, .zero :: .one :: status,
        3*(pre ++ [false]).length+7, parseCanonicalBlockProg_reject_high_zero pre tail status,
        hbound, hlen, Or.inr (by simp)⟩
  · subst stop
    exact ⟨.minus :: tail, (digits.map digitSym).reverse, .zero :: .zero :: status,
      3*digits.length+7, parseCanonicalBlockProg_reject_minus digits tail status,
      hbound, hlen, Or.inr (by simp)⟩

end TensorGraphPrefix3

namespace TensorPrefixDecode

open StackProgPortLift TensorGraphPrefix3 TensorCappedDecode

/-- All-input prefix-plus-decoder provenance: an accepted output dimension n
    came from the exact canonical input prefix encNat n; rejected input is
    marked as non-success. The remaining unary fuel completes the cap. -/
theorem prefixDecode_total_canonical (input status : List BSym) (cap : ℕ) :
    ∃ out steps,
      prefixDecodeProg.Exec (store7 input [] [] [] (List.replicate cap .one) [] status) out steps ∧
      steps ≤ (9*cap+15)*input.length + 3*input.length + 10 ∧
      ((∃ rest n fuel, input = encNat n ++ rest ∧ n+fuel=cap ∧
          out = store7 rest [] (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: .one :: status)) ∨
       (out 6).head? ≠ some .one) := by
  obtain ⟨rest, digits, outstatus, psteps, hp, hpbound, hdlen, hclass⟩ :=
    parseCanonicalBlockProg_total_canonical input status
  have hparse := parse_exec7 input [] [] [] (List.replicate cap .one) [] status
    rest digits outstatus psteps hp
  rcases hclass with ⟨n, hin, hdigits, hstatus⟩ | hbad
  · subst outstatus
    obtain ⟨out, dsteps, hdecode, hdbound, hresult⟩ := cappedDecode_total digits 0 cap (.one :: status)
    have hdecode7 := decode_exec7 rest digits [] [] (List.replicate cap .one) [] (.one :: .one :: status) out dsteps (by
      simpa using hdecode)
    have ha : accepted (fun k ↦
        (store7 rest digits [] [] (List.replicate cap .one) [] (.one :: .one :: status) k).head?) = true := by rfl
    have hb := StackProg.Exec.branchTrue (q := .act keepAct) ha hdecode7
    have he := StackProg.Exec.seq hparse hb
    refine ⟨write decodePorts out (store7 rest digits [] [] (List.replicate cap .one) [] (.one :: .one :: status)),
      psteps+1+(1+dsteps), he, ?_, ?_⟩
    · have hm := Nat.mul_le_mul_left (9*cap+15) hdlen
      simp only [Nat.zero_add] at hdbound
      omega
    · rcases hresult with ⟨n', fuel, hout, hsum, hvalue⟩ | ⟨bits, value, copy, fuel, scratch, hout⟩
      · have hn : n' = n := by
          rw [hdigits, scannerDigits_fold] at hvalue
          exact hvalue
        rw [hn] at hsum hout
        left
        refine ⟨rest, n, fuel, hin, ?_, ?_⟩
        · simpa only [Nat.zero_add] using hsum
        · rw [hout, write_decode]
      · right
        rw [hout, write_decode]
        simp [store7]
  · have ha : accepted (fun k ↦
        (store7 rest digits [] [] (List.replicate cap .one) [] outstatus k).head?) = false := by
      simp [accepted, store7, hbad]
    have hb := StackProg.Exec.branchFalse (p := liftProgC decodePorts decodeInverse cappedDecodeProg)
      ha (keep_exec (store7 rest digits [] [] (List.replicate cap .one) [] outstatus))
    have he := StackProg.Exec.seq hparse hb
    refine ⟨store7 rest digits [] [] (List.replicate cap .one) [] outstatus,
      psteps+1+2, he, ?_, Or.inr ?_⟩
    · have hn : 0 ≤ (9*cap+15)*input.length := Nat.zero_le _
      omega
    · simpa [store7] using hbad

end TensorPrefixDecode


namespace TensorPrefixDecode

open StackProgPortLift TensorInputUnaryLength

/-- After generating its own input-length cap, a successful prefix decoder
    identifies an exact canonical input prefix and its dimension. -/
theorem cappedPrefix_total_canonical (input status : List BSym) :
    ∃ out steps,
      cappedPrefixProg.Exec (store7 input [] [] [] [] [] status) out steps ∧
      steps ≤ (9*input.length+15)*input.length + 12*input.length+16 ∧
      ((∃ rest n fuel, input = encNat n ++ rest ∧ n+fuel=input.length ∧
          out = store7 rest [] (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: .one :: status)) ∨
       (out 6).head? ≠ some .one) := by
  obtain ⟨out, steps, hr, hb, hstatus⟩ := prefixDecode_total_canonical input status input.length
  have hc := inputLength_exec7 input [] [] status
  have he := StackProg.Exec.seq hc hr
  refine ⟨out, 9*input.length+5+1+steps, he, ?_, hstatus⟩
  omega

end TensorPrefixDecode


namespace TensorPrefixDecode

open StackProgPortLift TensorSquareScan TensorAdjacencyScan

/-- A successful matrix scan has exact input provenance: the input was the
    canonical dimension code followed by precisely n² Boolean blocks. -/
theorem cappedGraphScan_total_canonical (input status : List BSym) :
    ∃ out steps,
      cappedGraphScanProg.Exec (store7 input [] [] [] [] [] status) out steps ∧
      steps ≤ 23*(input.length*input.length)+40*input.length+28 ∧
      ((∃ (n : ℕ) (bs : List Bool), n ≤ input.length ∧ bs.length = n*n ∧
          input = encNat n ++ bitBlocks bs ∧ out 0 = [] ∧ out 1 = (bs.map bitSym).reverse ∧
          out 2 = List.replicate n .one ∧ out 3 = [] ∧ (out 6).head? = some .one) ∨
       (out 6).head? ≠ some .one) := by
  obtain ⟨mid, psteps, hp, hpbound, hshape⟩ := cappedPrefix_total_canonical input status
  rcases hshape with ⟨rest, n, fuel, horig, hsum, rfl⟩ | hbad
  · let tail := .one :: status
    have hnm : n ≤ input.length := by omega
    obtain ⟨rin, counter, bits, st, ssteps, hsbound, hscan⟩ :=
      scanCompleteProg_total (n*n) rest [] tail
    let localOut := write TensorSquareScan.scanPorts (TensorAdjacencyScan.store rin counter bits st)
      (write TensorSquareScan.squarePorts
        (TensorUnarySquare.store4 (List.replicate n .one) (List.replicate (n*n) .one) [] [])
        (TensorSquareScan.store6 rest (List.replicate n .one) [] [] [] (.one :: tail)))
    let base := store7 rest [] (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: tail)
    let out := write graphPorts localOut base
    have hsq := squareScan_of_scanner n rest tail (TensorAdjacencyScan.store rin counter bits st) ssteps hscan
    have hproj : project graphPorts base =
        TensorSquareScan.store6 rest (List.replicate n .one) [] [] [] (.one :: tail) := by
      funext k
      fin_cases k <;> simp [project, graphPorts, base, store7, TensorSquareScan.store6]
    have hlift := lift_exec graphPorts hsq base hproj
    rw [← liftProgC_eq_liftProg graphPorts graphInverse graphInverse_correct squareScanProg] at hlift
    have ht : accepted (fun k ↦ (base k).head?) = true := by simp [accepted, base, store7]
    have hb := StackProg.Exec.branchTrue (q := .act keepAct) ht hlift
    have he := StackProg.Exec.seq hp hb
    let gcost := (((6*n+3)+1+((6*n+7)*n+1))+1+ssteps)
    have hcost : gcost ≤ 14*(input.length*input.length)+13*input.length+10 := by
      have hsqle : n*n ≤ input.length*input.length := Nat.mul_le_mul hnm hnm
      dsimp [gcost]
      nlinarith
    have hstatus : out 6 = st := by
      change write graphPorts localOut base (graphPorts 5) = st
      rw [StackProgPortLift.write_at]
      change write TensorSquareScan.scanPorts _ _ (TensorSquareScan.scanPorts 3) = st
      rw [StackProgPortLift.write_at]
      simp [TensorAdjacencyScan.store]
    have hin : out 0 = rin := by
      change write graphPorts localOut base (graphPorts 0) = rin
      rw [StackProgPortLift.write_at]
      change write TensorSquareScan.scanPorts _ _ (TensorSquareScan.scanPorts 0) = rin
      rw [StackProgPortLift.write_at]
      simp [TensorAdjacencyScan.store]
    have hbits : out 1 = bits := by
      change write graphPorts localOut base (graphPorts 3) = bits
      rw [StackProgPortLift.write_at]
      change write TensorSquareScan.scanPorts _ _ (TensorSquareScan.scanPorts 2) = bits
      rw [StackProgPortLift.write_at]
      simp [TensorAdjacencyScan.store]
    have hcounter : out 3 = counter := by
      change write graphPorts localOut base (graphPorts 2) = counter
      rw [StackProgPortLift.write_at]
      change write TensorSquareScan.scanPorts _ _ (TensorSquareScan.scanPorts 1) = counter
      rw [StackProgPortLift.write_at]
      simp [TensorAdjacencyScan.store]
    have hvalue : out 2 = List.replicate n .one := by
      change write graphPorts localOut base (graphPorts 1) = _
      rw [StackProgPortLift.write_at]
      exact squareScan_preserves_source n rest tail rin counter bits st
    refine ⟨out, psteps+1+(1+gcost), he, ?_, ?_⟩
    · nlinarith
    · by_cases haccept : st.head? = some .one
      · have hst : ∃ suffix, st = .one :: suffix := by
          cases st with
          | nil => simp at haccept
          | cons sym suffix => cases sym <;> simp_all
        obtain ⟨suffix, hst⟩ := hst
        have hscan' : scanCompleteProg.Exec
            (TensorAdjacencyScan.store rest (List.replicate (n*n) .one) [] (.one :: tail))
            (TensorAdjacencyScan.store rin counter bits (.one :: suffix)) ssteps := by
          simpa only [hst] using hscan
        obtain ⟨bs, hlen, hrest, hrin, hcounter', hbits'⟩ :=
          scanComplete_accepted_shape (n*n) rest tail rin counter bits suffix ssteps hscan' 
        left
        refine ⟨n, bs, hnm, hlen, ?_, ?_, ?_, hvalue, ?_, ?_⟩
        · simpa [hrest] using horig
        · simpa [hrin] using hin
        · simpa [hbits'] using hbits
        · simpa [hcounter'] using hcounter
        · rw [hstatus, hst]
          rfl
      · right
        simpa [hstatus] using haccept
  · have ht : accepted (fun k ↦ (mid k).head?) = false := by simp [accepted, hbad]
    have hb := StackProg.Exec.branchFalse (p := liftProgC graphPorts graphInverse squareScanProg)
      ht (keep_exec mid)
    have he := StackProg.Exec.seq hp hb
    refine ⟨mid, psteps+1+2, he, ?_, Or.inr hbad⟩
    nlinarith


end TensorPrefixDecode

/-- A Boolean adjacency matrix with symmetric, zero-diagonal entries defines a simple graph. -/
def graphOfMatrix {v : ℕ} (m : Fin v → Fin v → Bool)
    (hsym : ∀ i j, m i j = m j i) (hdiag : ∀ i, m i i = false) : SimpleGraph (Fin v) where
  Adj i j := m i j = true
  symm := by
    constructor
    intro i j h
    rw [← hsym]
    exact h
  loopless := by
    constructor
    intro i h
    rw [hdiag] at h
    contradiction

/-- The matrix encoded in row-major order with the standard binary block convention. -/
def matrixCode {v : ℕ} (m : Fin v → Fin v → Bool) : List BSym :=
  encNats (v :: (List.ofFn fun i : Fin v ↦ List.ofFn fun j : Fin v ↦
    if m i j then 1 else 0).flatten)

/-- The published graph code of a symmetric irreflexive matrix is exactly its row-major code. -/
theorem graphOfMatrix_code {v : ℕ} (m : Fin v → Fin v → Bool)
    (hsym : ∀ i j, m i j = m j i) (hdiag : ∀ i, m i i = false) :
    TensorNP.Eigen.graphCode (graphOfMatrix m hsym hdiag) = matrixCode m := by
  classical
  simp only [TensorNP.Eigen.graphCode, matrixCode, graphOfMatrix]
  apply congrArg encNats
  simp only [List.singleton_append]
  apply congrArg (List.cons v)
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  by_cases h : m i j = true <;> simp [h]

/-- Unflatten a length-v² bit stream in the same row-major order as graphCode. -/
def matrixOfBits {v : ℕ} (bits : List Bool) (h : bits.length = v * v) : Fin v → Fin v → Bool :=
  fun i j ↦ bits.get (Fin.cast h.symm (finProdFinEquiv (i, j)))

/-- Flattening the row-major matrix reconstructed from a well-sized list restores that list. -/
theorem matrixOfBits_flatten {v : ℕ} (bits : List Bool) (h : bits.length = v * v) :
    (List.ofFn fun i : Fin v ↦ List.ofFn fun j : Fin v ↦ matrixOfBits bits h i j).flatten = bits := by
  have hfn : (List.ofFn fun k : Fin (v*v) ↦ bits.get (Fin.cast h.symm k)) = bits := by
    apply List.ext_getElem
    · simp [h]
    · intro i h1 h2
      simp [List.get_ofFn]
  rw [List.ofFn_mul] at hfn
  simpa [matrixOfBits, finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using hfn

/-- A Boolean matrix is symmetric exactly when each row equals the corresponding column. -/
theorem matrix_symmetric_iff_rows {v : ℕ} (m : Fin v → Fin v → Bool) :
    (∀ i j, m i j = m j i) ↔
      (∀ i, List.ofFn (m i) = List.ofFn (fun j ↦ m j i)) := by
  constructor
  · intro h i
    apply congrArg List.ofFn
    funext j
    exact h i j
  · intro h i j
    have hh := congrArg (fun xs : List Bool ↦ xs[j.val]?) (h i)
    simpa using hh

/-- Zero diagonal is exactly the assertion that every symbol in the diagonal list is false. -/
theorem matrix_diagonal_iff_all_false {v : ℕ} (m : Fin v → Fin v → Bool) :
    (∀ i, m i i = false) ↔
      (∀ b ∈ List.ofFn (fun i : Fin v ↦ m i i), b = false) := by
  constructor
  · intro h b hb
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hb
    rw [← hi]
    exact h i
  · intro h i
    apply h
    apply List.mem_ofFn.mpr
    exact ⟨i, rfl⟩


open ProjSchedTW.Complexity

/-- Pure counterpart of the checked stride-gather stack program. -/
def gatheredPure (stride : ℕ) : ℕ → List BSym → List BSym
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, a :: tail => a :: gatheredPure stride n (tail.drop stride)

/-- If every requested position exists, gathering is the row-major stride index list. -/
theorem gatheredPure_eq_ofFn (stride n : ℕ) (data : List BSym)
    (h : ∀ i, i < n → i * (stride + 1) < data.length) :
    gatheredPure stride n data =
      List.ofFn (fun i : Fin n ↦ data[i.val * (stride + 1)]'(h i.val i.isLt)) := by
  induction n generalizing data with
  | zero => simp [gatheredPure]
  | succ n ih =>
    cases data with
    | nil =>
      have := h 0 (by omega)
      simp at this
    | cons a tail =>
      have htail : ∀ i, i < n → i * (stride + 1) < (tail.drop stride).length := by
        intro i hi
        have hh := h (i + 1) (by omega)
        simp only [List.length_cons, Nat.add_mul, one_mul] at hh
        simp only [List.length_drop]
        omega
      have hr := ih (tail.drop stride) htail
      rw [gatheredPure, hr, List.ofFn_succ]
      congr 1
      · simp
      · apply congrArg List.ofFn
        funext i
        simp only [Function.comp_apply, Fin.val_succ, List.getElem_drop]
        have hidx : (i.val + 1) * (stride + 1) = (stride + i.val * (stride + 1)) + 1 := by ring
        simp only [hidx, List.getElem_cons_succ]


/-- Every diagonal stride position lies within a v×v row-major matrix. -/
theorem diag_stride_lt (v : ℕ) (i : Fin v) : i.val * (v + 1) < v * v := by
  have hi : i.val + 1 ≤ v := by omega
  have hm := Nat.mul_le_mul_right (v + 1) hi
  nlinarith

/-- Reversing a row-major v×v matrix reverses the order of its diagonal. -/
theorem diag_reverse_index (v : ℕ) (i : Fin v) :
    v*v - 1 - i.val * (v+1) = (v-1-i.val)*v + (v-1-i.val) := by
  let t := v - 1 - i.val
  have ht : t + i.val + 1 = v := by dsimp [t]; have := i.isLt; omega
  have hm := congrArg (fun x : ℕ ↦ x * v) ht
  simp only [Nat.add_mul, one_mul] at hm
  have hi := diag_stride_lt v i
  simp only [Nat.mul_add, Nat.mul_one] at hi ⊢
  dsimp [t] at ht hm
  omega


open CookPvsNP ProjSchedTW.Complexity

namespace TensorDiagonalGather

/-- Data, preserved unary stride, row tokens, work tokens, copy scratch, reversed output. -/
def store (data stride rows work scratch output : List BSym) : Fin 6 → List BSym :=
  fun k ↦ if k = 0 then data else if k = 1 then stride else if k = 2 then rows
    else if k = 3 then work else if k = 4 then scratch else output

private def hasRow (h : Fin 6 → Option BSym) : Bool :=
  (h 2 == some BSym.one) && (h 0 != none)

private def canSkip (h : Fin 6 → Option BSym) : Bool :=
  (h 3 == some BSym.one) && (h 0 != none)

private def takeAct (h : Fin 6 → Option BSym) (k : Fin 6) : StackAct BSym :=
  if k = 0 ∨ k = 2 then .pop else if k = 5 then
    match h 0 with | some a => .push a | none => .keep
  else .keep

private def skipAct (_h : Fin 6 → Option BSym) (k : Fin 6) : StackAct BSym :=
  if k = 0 ∨ k = 3 then .pop else .keep

/-- Extract the first element of each stride-separated group. -/
def gatherProg : StackProg (Fin 6) BSym :=
  .loop hasRow (.seq (.act takeAct)
    (.seq (copyProg 1 3 4) (.loop canSkip (.act skipAct))))

private lemma take_step (a : BSym) (data stride rows work scratch output : List BSym) :
    StackProg.applyAct takeAct (store (a :: data) stride (.one :: rows) work scratch output) =
      store data stride rows work scratch (a :: output) := by
  funext k
  fin_cases k <;> cases a <;> simp [StackProg.applyAct, takeAct, store, StackAct.apply]

private lemma skip_step (a : BSym) (data stride rows work scratch output : List BSym) :
    StackProg.applyAct skipAct (store (a :: data) stride rows (.one :: work) scratch output) =
      store data stride rows work scratch output := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, skipAct, store, StackAct.apply]

/-- The stride loop drops at most k symbols and preserves unused stride tokens. -/
private theorem skipLoop_exact (k : ℕ) (data stride rows scratch output : List BSym) :
    (StackProg.loop canSkip (.act skipAct)).Exec
      (store data stride rows (List.replicate k .one) scratch output)
      (store (data.drop k) stride rows (List.replicate (k - data.length) .one) scratch output)
      (3 * min k data.length + 1) := by
  induction k generalizing data with
  | zero =>
    simp only [List.replicate_zero, List.drop_zero, Nat.zero_sub, Nat.zero_min, Nat.mul_zero, Nat.zero_add]
    apply StackProg.Exec.loopFalse
    simp [canSkip, store]
  | succ k ih =>
    cases data with
    | nil =>
      apply StackProg.Exec.loopFalse
      simp [canSkip, store]
    | cons a data =>
      have ht : canSkip (fun port ↦
          (store (a :: data) stride rows (.one :: List.replicate k .one) scratch output port).head?) = true := by
        cases a <;> rfl
      have ha : (StackProg.act skipAct).Exec
          (store (a :: data) stride rows (.one :: List.replicate k .one) scratch output)
          (store data stride rows (List.replicate k .one) scratch output) 1 := by
        simpa only [skip_step] using
          (StackProg.Exec.act skipAct (store (a :: data) stride rows
            (.one :: List.replicate k .one) scratch output))
      have he := StackProg.Exec.loopTrue ht ha (ih data)
      simpa [List.replicate_succ, Nat.succ_min_succ, Nat.succ_sub_succ,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

/-- One gather iteration takes one symbol, copies the stride, then skips up to that stride. -/
theorem gatherBody_spec (a : BSym) (data rows output : List BSym) (stride : ℕ) :
    (StackProg.seq (.act takeAct) (.seq (copyProg 1 3 4) (.loop canSkip (.act skipAct)))).Exec
      (store (a :: data) (List.replicate stride .one) (.one :: rows) [] [] output)
      (store (data.drop stride) (List.replicate stride .one) rows
        (List.replicate (stride - data.length) .one) [] (a :: output))
      (1 + 1 + (6 * stride + 3) + 1 + (3 * min stride data.length + 1)) := by
  have ht : (StackProg.act takeAct).Exec
      (store (a :: data) (List.replicate stride .one) (.one :: rows) [] [] output)
      (store data (List.replicate stride .one) rows [] [] (a :: output)) 1 := by
    simpa only [take_step] using (StackProg.Exec.act takeAct
      (store (a :: data) (List.replicate stride .one) (.one :: rows) [] [] output))
  let s := store data (List.replicate stride .one) rows [] [] (a :: output)
  have hc := stack_copy (1 : Fin 6) 3 4 (by decide) (by decide) (by decide) s (by simp [s, store])
  have hupdate : Function.update s 3 (s 1 ++ s 3) =
      store data (List.replicate stride .one) rows (List.replicate stride .one) [] (a :: output) := by
    funext k
    fin_cases k <;> simp [s, store, Function.update]
  rw [hupdate] at hc
  have hs := skipLoop_exact stride data (List.replicate stride .one) rows [] (a :: output)
  have hseq := StackProg.Exec.seq hc hs
  have hfull := StackProg.Exec.seq ht hseq
  simpa [s, store, Nat.add_assoc] using hfull


/-- Abstract behavior of the stride gatherer, before reversing onto its output stack. -/
def gathered (stride : ℕ) : ℕ → List BSym → List BSym
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, a :: tail => a :: gathered stride n (tail.drop stride)

@[simp] private lemma gathered_nil (stride n : ℕ) : gathered stride n [] = [] := by
  cases n <;> rfl

/-- The gatherer terminates for every finite data list and unary row/stride counts. -/
theorem gatherProg_total (stride n : ℕ) (data output : List BSym) :
    ∃ data' rows' work' steps,
      steps ≤ (9 * stride + 9) * n + 1 ∧
      gatherProg.Exec
        (store data (List.replicate stride .one) (List.replicate n .one) [] [] output)
        (store data' (List.replicate stride .one) rows' work' []
          ((gathered stride n data).reverse ++ output)) steps := by
  induction n generalizing data output with
  | zero =>
    refine ⟨data, [], [], 1, by simp, ?_⟩
    simp only [List.replicate_zero, gathered, List.reverse_nil, List.nil_append]
    apply StackProg.Exec.loopFalse
    simp [hasRow, store]
  | succ n ih =>
    cases data with
    | nil =>
      refine ⟨[], .one :: List.replicate n .one, [], 1, by omega, ?_⟩
      simp only [List.replicate_succ, gathered, List.reverse_nil, List.nil_append]
      apply StackProg.Exec.loopFalse
      simp [hasRow, store]
    | cons a data =>
      have ht : hasRow (fun k ↦
          (store (a :: data) (List.replicate stride .one) (.one :: List.replicate n .one) [] [] output k).head?) =
            true := by cases a <;> rfl
      have hb := gatherBody_spec a data (List.replicate n .one) output stride
      by_cases hlen : stride ≤ data.length
      · have hsub : stride - data.length = 0 := Nat.sub_eq_zero_of_le hlen
        simp only [hsub, List.replicate_zero] at hb
        obtain ⟨data', rows', work', steps, hsteps, hrun⟩ := ih (data.drop stride) (a :: output)
        have he := StackProg.Exec.loopTrue ht hb hrun
        refine ⟨data', rows', work', 1 + (1 + 1 + (6 * stride + 3) + 1 +
          (3 * min stride data.length + 1)) + 1 + steps, ?_, ?_⟩
        · have hmin := Nat.min_le_left stride data.length
          simp only [Nat.mul_succ]
          omega
        · simpa [gatherProg, gathered, List.replicate_succ, List.reverse_cons, List.append_assoc] using he
      · have hdrop : data.drop stride = [] := List.drop_eq_nil_of_le (by omega)
        rw [hdrop] at hb
        have hstop : gatherProg.Exec
            (store [] (List.replicate stride .one) (List.replicate n .one)
              (List.replicate (stride - data.length) .one) [] (a :: output))
            (store [] (List.replicate stride .one) (List.replicate n .one)
              (List.replicate (stride - data.length) .one) [] (a :: output)) 1 := by
          apply StackProg.Exec.loopFalse
          simp [hasRow, store]
        have he := StackProg.Exec.loopTrue ht hb hstop
        refine ⟨[], List.replicate n .one, List.replicate (stride - data.length) .one,
          1 + (1 + 1 + (6 * stride + 3) + 1 + (3 * min stride data.length + 1)) + 1 + 1,
          ?_, ?_⟩
        · have hmin := Nat.min_le_left stride data.length
          simp only [Nat.mul_succ]
          omega
        · simpa [gatherProg, gathered, hdrop, gathered_nil, List.replicate_succ, List.reverse_cons, List.append_assoc] using he

end TensorDiagonalGather

def diagSymbol (b : Bool) : BSym := if b then .one else .zero

def reverseFin {v : ℕ} (i : Fin v) : Fin v := ⟨v - 1 - i.val, by have := i.isLt; omega⟩

/-- Stride sampling of a reversed row-major matrix visits its diagonal in reverse order. -/
theorem gathered_reversed_diagonal {v : ℕ} (bits : List Bool) (h : bits.length = v*v) :
    gatheredPure v v ((bits.map diagSymbol).reverse) =
      List.ofFn (fun i : Fin v ↦ diagSymbol (matrixOfBits bits h (reverseFin i) (reverseFin i))) := by
  have hpos : ∀ i, i < v → i * (v + 1) < ((bits.map diagSymbol).reverse).length := by
    intro i hi
    simpa [h] using diag_stride_lt v ⟨i, hi⟩
  rw [gatheredPure_eq_ofFn v v _ hpos]
  apply congrArg List.ofFn
  funext i
  simp only [List.getElem_reverse, List.length_map, h, List.getElem_map]
  have he := diag_reverse_index v i
  have he' : v*v - 1 - i.val * (v+1) = (v-1-i.val) + v*(v-1-i.val) := by
    simpa [Nat.mul_comm, Nat.add_comm] using he
  simp [matrixOfBits, reverseFin, finProdFinEquiv, he']

private theorem gathered_eq_pure (stride n : ℕ) (data : List BSym) :
    TensorDiagonalGather.gathered stride n data = gatheredPure stride n data := by
  induction n generalizing data with
  | zero => simp [TensorDiagonalGather.gathered, gatheredPure]
  | succ n ih => cases data <;> simp [TensorDiagonalGather.gathered, gatheredPure, ih]

/-- The executable stride gatherer outputs the diagonal of a square matrix, up to list reversal. -/
theorem diagonalGather_exec {v : ℕ} (bits : List Bool) (h : bits.length = v*v) (output : List BSym) :
    ∃ data' rows' work' steps,
      steps ≤ (9*v+9)*v+1 ∧
      TensorDiagonalGather.gatherProg.Exec
        (TensorDiagonalGather.store ((bits.map diagSymbol).reverse) (List.replicate v .one)
          (List.replicate v .one) [] [] output)
        (TensorDiagonalGather.store data' (List.replicate v .one) rows' work' []
          ((List.ofFn (fun i : Fin v ↦ diagSymbol (matrixOfBits bits h (reverseFin i) (reverseFin i)))).reverse ++ output)) steps := by
  obtain ⟨data', rows', work', steps, hb, he⟩ :=
    TensorDiagonalGather.gatherProg_total v v ((bits.map diagSymbol).reverse) output
  refine ⟨data', rows', work', steps, hb, ?_⟩
  rw [gathered_eq_pure, gathered_reversed_diagonal bits h] at he
  exact he


open CookPvsNP ProjSchedTW.Complexity

namespace TensorStackAllZero

def store (input status : List BSym) : Fin 2 → List BSym :=
  fun k ↦ if k = 0 then input else status

private def isZero (h : Fin 2 → Option BSym) : Bool := h 0 == some BSym.zero
private def isEmpty (h : Fin 2 → Option BSym) : Bool := h 0 == none

private def popInput (_h : Fin 2 → Option BSym) (k : Fin 2) : StackAct BSym :=
  if k = 0 then .pop else .keep

private def mark (b : BSym) (_h : Fin 2 → Option BSym) (k : Fin 2) : StackAct BSym :=
  if k = 1 then .push b else .keep

/-- Consume the leading zero symbols and accept exactly when the input is exhausted. -/
def allZeroProg : StackProg (Fin 2) BSym :=
  .seq (.loop isZero (.act popInput))
    (.branch isEmpty (.act (mark .one)) (.act (mark .zero)))

private lemma pop_step (tail status : List BSym) :
    StackProg.applyAct popInput (store (.zero :: tail) status) = store tail status := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, popInput, store, StackAct.apply]

private lemma mark_step (b : BSym) (input status : List BSym) :
    StackProg.applyAct (mark b) (store input status) = store input (b :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, mark, store, StackAct.apply]

/-- All-zero input is consumed and accepted in exactly 3n+4 source steps. -/
theorem allZeroProg_success (n : ℕ) (status : List BSym) :
    allZeroProg.Exec (store (List.replicate n .zero) status) (store [] (.one :: status)) (3*n+4) := by
  have hloop : ∀ n : ℕ, (StackProg.loop isZero (.act popInput)).Exec
      (store (List.replicate n .zero) status) (store [] status) (3*n+1) := by
    intro n
    induction n with
    | zero =>
      apply StackProg.Exec.loopFalse
      rfl
    | succ n ih =>
      have ht : isZero (fun k ↦ (store (.zero :: List.replicate n .zero) status k).head?) = true := rfl
      have ha : (StackProg.act popInput).Exec (store (.zero :: List.replicate n .zero) status)
          (store (List.replicate n .zero) status) 1 := by
        simpa only [pop_step] using
          (StackProg.Exec.act popInput (store (.zero :: List.replicate n .zero) status))
      have he := StackProg.Exec.loopTrue ht ha ih
      simpa [List.replicate_succ, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he
  have ha : (StackProg.act (mark .one)).Exec (store [] status) (store [] (.one :: status)) 1 := by
    simpa only [mark_step] using (StackProg.Exec.act (mark .one) (store [] status))
  have hb : (StackProg.branch isEmpty (.act (mark .one)) (.act (mark .zero))).Exec
      (store [] status) (store [] (.one :: status)) 2 := StackProg.Exec.branchTrue (by rfl) ha
  have he := StackProg.Exec.seq (hloop n) hb
  simpa [allZeroProg, Nat.add_assoc] using he


private theorem zeroLoop_spec (input status : List BSym) :
    ∃ rest n, n ≤ input.length ∧ input = List.replicate n .zero ++ rest ∧
      (rest = [] ∨ rest.head? ≠ some BSym.zero) ∧
      (StackProg.loop isZero (.act popInput)).Exec (store input status) (store rest status) (3*n+1) := by
  induction input with
  | nil =>
    refine ⟨[], 0, by simp, by simp, Or.inl rfl, ?_⟩
    apply StackProg.Exec.loopFalse
    rfl
  | cons a tail ih =>
    cases a with
    | zero =>
      obtain ⟨rest, n, hn, heq, hrest, hrun⟩ := ih
      have ht : isZero (fun k ↦ (store (.zero :: tail) status k).head?) = true := rfl
      have ha : (StackProg.act popInput).Exec (store (.zero :: tail) status) (store tail status) 1 := by
        simpa only [pop_step] using (StackProg.Exec.act popInput (store (.zero :: tail) status))
      have he := StackProg.Exec.loopTrue ht ha hrun
      refine ⟨rest, n+1, ?_, ?_, hrest, ?_⟩
      · simp only [List.length_cons]
        omega
      · simpa [List.replicate_succ] using congrArg (List.cons BSym.zero) heq
      · simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he
    | one =>
      refine ⟨.one :: tail, 0, by simp, by simp, Or.inr (by simp), ?_⟩
      exact StackProg.Exec.loopFalse (by rfl)
    | minus =>
      refine ⟨.minus :: tail, 0, by simp, by simp, Or.inr (by simp), ?_⟩
      exact StackProg.Exec.loopFalse (by rfl)
    | sep =>
      refine ⟨.sep :: tail, 0, by simp, by simp, Or.inr (by simp), ?_⟩
      exact StackProg.Exec.loopFalse (by rfl)

/-- The all-zero checker always halts linearly and its marker is correct. -/
theorem allZeroProg_total (input status : List BSym) :
    ∃ rest marker steps, steps ≤ 3 * input.length + 4 ∧
      (marker = .one ↔ ∀ a ∈ input, a = .zero) ∧
      allZeroProg.Exec (store input status) (store rest (marker :: status)) steps := by
  obtain ⟨rest, n, hn, heq, hrest, hrun⟩ := zeroLoop_spec input status
  cases rest with
  | nil =>
    have ha : (StackProg.act (mark .one)).Exec (store [] status) (store [] (.one :: status)) 1 := by
      simpa only [mark_step] using (StackProg.Exec.act (mark .one) (store [] status))
    have hb := StackProg.Exec.branchTrue (test := isEmpty) (q := .act (mark .zero)) (by rfl) ha
    refine ⟨[], .one, 3*n+4, by omega, ?_, ?_⟩
    · constructor
      · intro _ a ha
        rw [heq] at ha
        simp only [List.append_nil, List.mem_replicate] at ha
        exact ha.2
      · intro _
        rfl
    · have he := StackProg.Exec.seq hrun hb
      simpa [allZeroProg, Nat.add_assoc] using he
  | cons a rest =>
    have hne : a ≠ .zero := by
      rcases hrest with hnil | hhead
      · simp at hnil
      · simpa using hhead
    have ha : (StackProg.act (mark .zero)).Exec (store (a :: rest) status)
        (store (a :: rest) (.zero :: status)) 1 := by
      simpa only [mark_step] using (StackProg.Exec.act (mark .zero) (store (a :: rest) status))
    have hb := StackProg.Exec.branchFalse (test := isEmpty) (p := .act (mark .one)) (by rfl) ha
    refine ⟨a :: rest, .zero, 3*n+4, by omega, ?_, ?_⟩
    · constructor
      · intro h
        cases h
      · intro h
        have hm : a ∈ input := by rw [heq]; simp
        exact (hne (h a hm)).elim
    · have he := StackProg.Exec.seq hrun hb
      simpa [allZeroProg, Nat.add_assoc] using he

end TensorStackAllZero


namespace TensorDiagonalCheck

open StackProgPortLift

private def zeroPorts : Fin 2 ↪ Fin 6 := ⟨![5, 4], by decide⟩
private def zeroDecode : Fin 6 → Option (Fin 2) := ![none, none, none, none, some 1, some 0]

private theorem zeroDecode_correct (l : Fin 6) (k : Fin 2) :
    zeroDecode l = some k ↔ zeroPorts k = l := by
  fin_cases l <;> fin_cases k <;> decide

/-- Gather a stride-separated sequence, then test whether all gathered symbols are zero. -/
def diagonalCheckProg : StackProg (Fin 6) BSym :=
  .seq TensorDiagonalGather.gatherProg
    (liftProgC zeroPorts zeroDecode TensorStackAllZero.allZeroProg)

private theorem gathered_length_le (stride n : ℕ) (data : List BSym) :
    (TensorDiagonalGather.gathered stride n data).length ≤ n := by
  induction n generalizing data with
  | zero => simp [TensorDiagonalGather.gathered]
  | succ n ih =>
    cases data with
    | nil => simp [TensorDiagonalGather.gathered]
    | cons a data =>
      simp only [TensorDiagonalGather.gathered, List.length_cons]
      have h := ih (data.drop stride)
      omega

/-- On arbitrary input, the executable gather/check composition terminates in
    polynomially many source steps and its marker exactly checks the sampled list. -/
theorem diagonalCheckProg_total (stride n : ℕ) (data : List BSym) :
    ∃ data' rows' work' rest marker steps,
      steps ≤ (9 * stride + 12) * n + 6 ∧
      (marker = .one ↔ ∀ a ∈ TensorDiagonalGather.gathered stride n data, a = .zero) ∧
      diagonalCheckProg.Exec
        (TensorDiagonalGather.store data (List.replicate stride .one) (List.replicate n .one) [] [] [])
        (write zeroPorts (TensorStackAllZero.store rest [marker])
          (TensorDiagonalGather.store data' (List.replicate stride .one) rows' work' []
            (TensorDiagonalGather.gathered stride n data).reverse)) steps := by
  classical
  obtain ⟨data', rows', work', sg, hg, hrun⟩ :=
    TensorDiagonalGather.gatherProg_total stride n data []
  let gathered := TensorDiagonalGather.gathered stride n data
  let base := TensorDiagonalGather.store data' (List.replicate stride .one) rows' work' [] gathered.reverse
  have hproject : project zeroPorts base = TensorStackAllZero.store gathered.reverse [] := by
    funext k
    fin_cases k <;> simp [project, zeroPorts, base, TensorDiagonalGather.store, TensorStackAllZero.store]
  obtain ⟨rest, marker, sz, hz, hmarker, hzero⟩ := TensorStackAllZero.allZeroProg_total gathered.reverse []
  have hlift := lift_exec zeroPorts hzero base hproject
  have hlift' : (liftProgC zeroPorts zeroDecode TensorStackAllZero.allZeroProg).Exec base
      (write zeroPorts (TensorStackAllZero.store rest [marker]) base) sz := by
    rw [liftProgC_eq_liftProg zeroPorts zeroDecode zeroDecode_correct]
    exact hlift
  have hrun' : TensorDiagonalGather.gatherProg.Exec
      (TensorDiagonalGather.store data (List.replicate stride .one) (List.replicate n .one) [] [] [])
      base sg := by
    simpa only [base, gathered, List.append_nil] using hrun
  have hseq := StackProg.Exec.seq hrun' hlift'
  refine ⟨data', rows', work', rest, marker, sg + 1 + sz, ?_, ?_, ?_⟩
  · have hlen := gathered_length_le stride n data
    simp only [List.length_reverse] at hz
    simp only [Nat.add_mul] at hg ⊢
    dsimp [gathered] at hz
    nlinarith
  · simpa only [List.mem_reverse] using hmarker
  · simpa only [diagonalCheckProg, base, gathered, List.append_nil] using hseq


private lemma reverseFin_involutive {v : ℕ} (i : Fin v) : reverseFin (reverseFin i) = i := by
  apply Fin.ext
  simp only [reverseFin, Fin.val_mk]
  have hi := i.isLt
  omega

/-- The gathered symbols are all zero iff the reconstructed Boolean matrix has zero diagonal. -/
theorem gathered_zero_iff_diagonal {v : ℕ} (bits : List Bool) (h : bits.length = v * v) :
    (∀ a ∈ TensorDiagonalGather.gathered v v ((bits.map diagSymbol).reverse), a = .zero) ↔
      (∀ i : Fin v, matrixOfBits bits h i i = false) := by
  rw [gathered_eq_pure, gathered_reversed_diagonal bits h]
  constructor
  · intro hall i
    have hm : diagSymbol (matrixOfBits bits h i i) ∈
        List.ofFn (fun j : Fin v ↦ diagSymbol (matrixOfBits bits h (reverseFin j) (reverseFin j))) := by
      apply List.mem_ofFn.mpr
      refine ⟨reverseFin i, ?_⟩
      simp only [reverseFin_involutive]
    have hz := hall _ hm
    cases he : matrixOfBits bits h i i <;> simp [diagSymbol, he] at hz ⊢
  · intro hd a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    simp [diagSymbol, hd]

/-- The concrete composition decides zero diagonal and halts quadratically in v. -/
theorem diagonalCheck_matrix {v : ℕ} (bits : List Bool) (h : bits.length = v*v) :
    ∃ data' rows' work' rest marker steps,
      steps ≤ (9 * v + 12) * v + 6 ∧
      (marker = .one ↔ ∀ i : Fin v, matrixOfBits bits h i i = false) ∧
      diagonalCheckProg.Exec
        (TensorDiagonalGather.store ((bits.map diagSymbol).reverse) (List.replicate v .one)
          (List.replicate v .one) [] [] [])
        (write zeroPorts (TensorStackAllZero.store rest [marker])
          (TensorDiagonalGather.store data' (List.replicate v .one) rows' work' []
            (TensorDiagonalGather.gathered v v ((bits.map diagSymbol).reverse)).reverse)) steps := by
  obtain ⟨data', rows', work', rest, marker, steps, hb, hm, he⟩ :=
    diagonalCheckProg_total v v ((bits.map diagSymbol).reverse)
  exact ⟨data', rows', work', rest, marker, steps, hb, hm.trans (gathered_zero_iff_diagonal bits h), he⟩

end TensorDiagonalCheck

namespace TensorDiagonalFront

open StackProgPortLift

/-- Preserve all seven scanner ports and add four empty private work stacks. -/
def extend7 (s : Fin 7 → List BSym) : Fin 11 → List BSym :=
  fun k ↦ if h : k.val < 7 then s ⟨k.val, h⟩ else []

def diagonalPorts : Fin 6 ↪ Fin 11 := ⟨![7,2,8,9,10,0], by decide⟩
def diagonalInverse : Fin 11 → Option (Fin 6) :=
  ![some 5,none,some 1,none,none,none,none,some 0,some 2,some 3,some 4]

private theorem diagonalInverse_correct (l : Fin 11) (k : Fin 6) :
    diagonalInverse l = some k ↔ diagonalPorts k = l := by fin_cases l <;> fin_cases k <;> decide

/-- Preserve original matrix and dimension while preparing independent data
    and row counters, then gather and check the diagonal. -/
def diagonalFrontProg : StackProg (Fin 11) BSym :=
  .seq (copyProg 1 7 9)
    (.seq (copyProg 2 8 9)
      (liftProgC diagonalPorts diagonalInverse TensorDiagonalCheck.diagonalCheckProg))

/-- With a cleared input port and unary dimension, the diagonal front stage
    terminates on arbitrary matrix data; it preserves the master bit stream and
    status and writes the exact diagonal-check marker to private port 10. -/
theorem diagonalFront_total (s : Fin 7 → List BSym) (n : ℕ)
    (hinput : s 0 = []) (hdim : s 2 = List.replicate n .one) :
    ∃ out marker steps,
      diagonalFrontProg.Exec (extend7 s) out steps ∧
      steps ≤ 6*(s 1).length + 9*n*n + 18*n + 14 ∧
      out 1 = s 1 ∧ out 2 = s 2 ∧ out 6 = s 6 ∧ out 10 = [marker] ∧
      (marker = .one ↔ ∀ a ∈ TensorDiagonalGather.gathered n n (s 1), a = .zero) := by
  classical
  let b := extend7 s
  let c := Function.update b 7 (b 1 ++ b 7)
  let d := Function.update c 8 (c 2 ++ c 8)
  have hs : b 9 = [] := by simp [b, extend7]
  have hc : (copyProg (1 : Fin 11) 7 9).Exec b c (6*(s 1).length+3) := by
    have h := stack_copy (1 : Fin 11) 7 9 (by decide) (by decide) (by decide) b hs
    simpa [b, c, extend7] using h
  have hscratch : c 9 = [] := by simp [c, b, extend7, Function.update]
  have hd : (copyProg (2 : Fin 11) 8 9).Exec c d (6*n+3) := by
    have h := stack_copy (2 : Fin 11) 8 9 (by decide) (by decide) (by decide) c hscratch
    simpa [c, b, d, extend7, Function.update, hdim] using h
  have hproj : project diagonalPorts d = TensorDiagonalGather.store (s 1) (List.replicate n .one)
      (List.replicate n .one) [] [] [] := by
    funext k
    fin_cases k <;> simp [project, diagonalPorts, d, c, b, extend7, Function.update,
      TensorDiagonalGather.store, hinput, hdim]
  obtain ⟨data', rows', work', rest, marker, tsteps, htbound, hmarker, hrun⟩ :=
    TensorDiagonalCheck.diagonalCheckProg_total n n (s 1)
  let localOut := write TensorDiagonalCheck.zeroPorts (TensorStackAllZero.store rest [marker])
    (TensorDiagonalGather.store data' (List.replicate n .one) rows' work' []
      (TensorDiagonalGather.gathered n n (s 1)).reverse)
  let out := write diagonalPorts localOut d
  have hlift := lift_exec diagonalPorts hrun d hproj
  rw [← liftProgC_eq_liftProg diagonalPorts diagonalInverse diagonalInverse_correct
    TensorDiagonalCheck.diagonalCheckProg] at hlift
  have hseq := StackProg.Exec.seq hc (StackProg.Exec.seq hd hlift)
  have hout1 : out 1 = s 1 := by
    have ho : ∀ k : Fin 6, diagonalPorts k ≠ (1 : Fin 11) := by intro k; fin_cases k <;> decide
    rw [show out = write diagonalPorts localOut d by rfl, write_outside diagonalPorts localOut d ho]
    simp [d, c, b, extend7, Function.update]
  have hout2 : out 2 = s 2 := by
    change write diagonalPorts localOut d (diagonalPorts 1) = s 2
    rw [write_at]
    have ho : ∀ k : Fin 2, TensorDiagonalCheck.zeroPorts k ≠ (1 : Fin 6) := by
      intro k; fin_cases k <;> decide
    dsimp only [localOut]
    rw [write_outside TensorDiagonalCheck.zeroPorts _ _ ho]
    simpa [TensorDiagonalGather.store] using hdim.symm
  have hout6 : out 6 = s 6 := by
    have ho : ∀ k : Fin 6, diagonalPorts k ≠ (6 : Fin 11) := by intro k; fin_cases k <;> decide
    rw [show out = write diagonalPorts localOut d by rfl, write_outside diagonalPorts localOut d ho]
    simp [d, c, b, extend7, Function.update]
  have hout10 : out 10 = [marker] := by
    change write diagonalPorts localOut d (diagonalPorts 4) = [marker]
    rw [write_at]
    change write TensorDiagonalCheck.zeroPorts _ _ (TensorDiagonalCheck.zeroPorts 1) = [marker]
    rw [write_at]
    simp [TensorStackAllZero.store]
  refine ⟨out, marker, (6*(s 1).length+3)+1+((6*n+3)+1+tsteps), ?_, ?_, hout1, hout2, hout6, hout10, hmarker⟩
  · exact hseq
  · nlinarith

end TensorDiagonalFront


namespace TensorGraphDiagonal

open StackProgPortLift TensorPrefixDecode TensorDiagonalFront

def frontPorts : Fin 7 ↪ Fin 11 := ⟨![0,1,2,3,4,5,6], by decide⟩
def frontInverse : Fin 11 → Option (Fin 7) :=
  ![some 0,some 1,some 2,some 3,some 4,some 5,some 6,none,none,none,none]

private theorem frontInverse_correct (l : Fin 11) (k : Fin 7) :
    frontInverse l = some k ↔ frontPorts k = l := by fin_cases l <;> fin_cases k <;> decide

private def frontAccepted (h : Fin 11 → Option BSym) : Bool := h 6 == some BSym.one
private def diagonalAccepted (h : Fin 11 → Option BSym) : Bool := h 10 == some BSym.one
private def keepAct (_h : Fin 11 → Option BSym) (_k : Fin 11) : StackAct BSym := .keep
private def rejectAct (_h : Fin 11 → Option BSym) (k : Fin 11) : StackAct BSym :=
  if k = 6 then .push .zero else .keep
private def rejectStore (s : Fin 11 → List BSym) : Fin 11 → List BSym :=
  Function.update s 6 (.zero :: s 6)

/-- Execute canonical matrix scanning and then zero-diagonal checking, with
    an explicit status gate between the stages and propagated rejection. -/
def graphDiagonalProg : StackProg (Fin 11) BSym :=
  .seq (liftProgC frontPorts frontInverse cappedGraphScanProg)
    (.branch frontAccepted
      (.seq diagonalFrontProg (.branch diagonalAccepted (.act keepAct) (.act rejectAct)))
      (.act keepAct))

private theorem project_front (s : Fin 7 → List BSym) : project frontPorts (extend7 s) = s := by
  funext k
  fin_cases k <;> simp [project, frontPorts, extend7]

private theorem write_front (s t : Fin 7 → List BSym) : write frontPorts t (extend7 s) = extend7 t := by
  funext k
  fin_cases k
  · simpa [frontPorts, extend7] using
      (StackProgPortLift.write_at frontPorts t (extend7 s) (0 : Fin 7))
  · simpa [frontPorts, extend7] using
      (StackProgPortLift.write_at frontPorts t (extend7 s) (1 : Fin 7))
  · simpa [frontPorts, extend7] using
      (StackProgPortLift.write_at frontPorts t (extend7 s) (2 : Fin 7))
  · simpa [frontPorts, extend7] using
      (StackProgPortLift.write_at frontPorts t (extend7 s) (3 : Fin 7))
  · simpa [frontPorts, extend7] using
      (StackProgPortLift.write_at frontPorts t (extend7 s) (4 : Fin 7))
  · simpa [frontPorts, extend7] using
      (StackProgPortLift.write_at frontPorts t (extend7 s) (5 : Fin 7))
  · simpa [frontPorts, extend7] using
      (StackProgPortLift.write_at frontPorts t (extend7 s) (6 : Fin 7))
  · have ho : ∀ j : Fin 7, frontPorts j ≠ (7 : Fin 11) := by
      intro j; fin_cases j <;> decide
    simpa [extend7] using (StackProgPortLift.write_outside frontPorts t (extend7 s) ho)
  · have ho : ∀ j : Fin 7, frontPorts j ≠ (8 : Fin 11) := by
      intro j; fin_cases j <;> decide
    simpa [extend7] using (StackProgPortLift.write_outside frontPorts t (extend7 s) ho)
  · have ho : ∀ j : Fin 7, frontPorts j ≠ (9 : Fin 11) := by
      intro j; fin_cases j <;> decide
    simpa [extend7] using (StackProgPortLift.write_outside frontPorts t (extend7 s) ho)
  · have ho : ∀ j : Fin 7, frontPorts j ≠ (10 : Fin 11) := by
      intro j; fin_cases j <;> decide
    simpa [extend7] using (StackProgPortLift.write_outside frontPorts t (extend7 s) ho)

private theorem keep_exec (s : Fin 11 → List BSym) : (StackProg.act keepAct).Exec s s 1 := by
  have heq : StackProg.applyAct keepAct s = s := by
    funext k
    simp [StackProg.applyAct, keepAct, StackAct.apply]
  simpa only [heq] using StackProg.Exec.act keepAct s

private theorem reject_exec (s : Fin 11 → List BSym) :
    (StackProg.act rejectAct).Exec s (rejectStore s) 1 := by
  have heq : StackProg.applyAct rejectAct s = rejectStore s := by
    funext k
    fin_cases k <;> simp [StackProg.applyAct, rejectAct, rejectStore, StackAct.apply, Function.update]
  simpa only [heq] using StackProg.Exec.act rejectAct s

/-- Every input halts quadratically. Success identifies the exact canonical
    Boolean-matrix input and proves zero diagonal; all other paths propagate a
    non-success marker. Symmetry remains a separate subsequent validation. -/
theorem graphDiagonal_total (input status : List BSym) :
    ∃ out steps,
      graphDiagonalProg.Exec (extend7 (store7 input [] [] [] [] [] status)) out steps ∧
      steps ≤ 38*(input.length*input.length)+58*input.length+47 ∧
      ((∃ (n : ℕ) (bs : List Bool) (hlen : bs.length = n*n),
          input = encNat n ++ TensorAdjacencyScan.bitBlocks bs ∧ n ≤ input.length ∧
          (∀ i : Fin n, matrixOfBits bs hlen i i = false) ∧
          out 1 = (bs.map TensorAdjacencyScan.bitSym).reverse ∧
          out 2 = List.replicate n .one ∧ (out 6).head? = some .one) ∨
       (out 6).head? ≠ some .one) := by
  obtain ⟨front, psteps, hp, hpbound, hshape⟩ := cappedGraphScan_total_canonical input status
  have hfront := lift_exec frontPorts hp (extend7 (store7 input [] [] [] [] [] status))
    (project_front (store7 input [] [] [] [] [] status))
  rw [write_front] at hfront
  rw [← liftProgC_eq_liftProg frontPorts frontInverse frontInverse_correct cappedGraphScanProg] at hfront
  rcases hshape with ⟨n, bs, hnm, hlen, horig, hin, hbits, hvalue, hcount, hstatus⟩ | hbad
  · have haccept : frontAccepted (fun k ↦ (extend7 front k).head?) = true := by
      simpa [frontAccepted, extend7] using hstatus
    obtain ⟨out, marker, dsteps, hd, hdbound, hkeepbits, hkeepvalue, hkeepstatus, hmarker, hmarkerspec⟩ :=
      diagonalFront_total front n hin hvalue
    have hdiag : marker = .one ↔ ∀ i : Fin n, matrixOfBits bs hlen i i = false := by
      apply hmarkerspec.trans
      rw [hbits]
      have hsym : TensorAdjacencyScan.bitSym = diagSymbol := by
        funext b
        cases b <;> rfl
      rw [hsym]
      exact TensorDiagonalCheck.gathered_zero_iff_diagonal bs hlen
    have hlen' : (front 1).length = n*n := by
      rw [hbits]
      simpa using hlen
    have hds : dsteps ≤ 15*(n*n)+18*n+14 := by
      rw [hlen'] at hdbound
      nlinarith
    have hnm2 : n*n ≤ input.length*input.length := Nat.mul_le_mul hnm hnm
    by_cases hm : marker = .one
    · have hpost : diagonalAccepted (fun k ↦ (out k).head?) = true := by
        simp [diagonalAccepted, hmarker, hm]
      have hfinish := StackProg.Exec.branchTrue (q := .act rejectAct) hpost (keep_exec out)
      have hbody := StackProg.Exec.seq hd hfinish
      have hbranch := StackProg.Exec.branchTrue (q := .act keepAct) haccept hbody
      have he := StackProg.Exec.seq hfront hbranch
      refine ⟨out, psteps+1+(1+(dsteps+1+2)), he, ?_, Or.inl ⟨n, bs, hlen, horig, hnm, hdiag.mp hm, ?_, ?_, ?_⟩⟩
      · nlinarith
      · simpa [hbits] using hkeepbits
      · simpa [hvalue] using hkeepvalue
      · simpa [hkeepstatus] using hstatus
    · have hpost : diagonalAccepted (fun k ↦ (out k).head?) = false := by
        simp [diagonalAccepted, hmarker, hm]
      have hfinish := StackProg.Exec.branchFalse (p := .act keepAct) hpost (reject_exec out)
      have hbody := StackProg.Exec.seq hd hfinish
      have hbranch := StackProg.Exec.branchTrue (q := .act keepAct) haccept hbody
      have he := StackProg.Exec.seq hfront hbranch
      refine ⟨rejectStore out, psteps+1+(1+(dsteps+1+2)), he, ?_, Or.inr ?_⟩
      · nlinarith
      · simp [rejectStore, Function.update]
  · have haccept : frontAccepted (fun k ↦ (extend7 front k).head?) = false := by
      simp [frontAccepted, extend7, hbad]
    have hbranch := StackProg.Exec.branchFalse
      (p := .seq diagonalFrontProg (.branch diagonalAccepted (.act keepAct) (.act rejectAct)))
      haccept (keep_exec (extend7 front))
    have he := StackProg.Exec.seq hfront hbranch
    refine ⟨extend7 front, psteps+1+2, he, ?_, Or.inr ?_⟩
    · nlinarith
    · simpa [extend7] using hbad

end TensorGraphDiagonal

namespace TensorStackCompare

def store (left right status : List BSym) : Fin 3 → List BSym :=
  fun k ↦ if k = 0 then left else if k = 1 then right else status

private def sameHead (h : Fin 3 → Option BSym) : Bool :=
  (h 0 != none) && (h 0 == h 1)

private def bothEmpty (h : Fin 3 → Option BSym) : Bool :=
  (h 0 == none) && (h 1 == none)

private def popBoth (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 0 ∨ k = 1 then .pop else .keep

private def mark (b : BSym) (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 2 then .push b else .keep

/-- Destructively compare two copied symbol stacks and push one on equality, zero otherwise. -/
def compareProg : StackProg (Fin 3) BSym :=
  .seq (.loop sameHead (.act popBoth))
    (.branch bothEmpty (.act (mark .one)) (.act (mark .zero)))

private lemma pop_step (a : BSym) (left right status : List BSym) :
    StackProg.applyAct popBoth (store (a :: left) (a :: right) status) =
      store left right status := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, popBoth, store, StackAct.apply]

private lemma mark_step (b : BSym) (left right status : List BSym) :
    StackProg.applyAct (mark b) (store left right status) = store left right (b :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, mark, store, StackAct.apply]

/-- Equal symbol strings are fully consumed and accepted in exactly 3n+4 steps. -/
theorem compareProg_equal (xs status : List BSym) :
    compareProg.Exec (store xs xs status) (store [] [] (.one :: status)) (3 * xs.length + 4) := by
  have hloop : ∀ xs status, (StackProg.loop sameHead (.act popBoth)).Exec
      (store xs xs status) (store [] [] status) (3 * xs.length + 1) := by
    intro xs
    induction xs with
    | nil =>
      intro status
      apply StackProg.Exec.loopFalse
      rfl
    | cons a xs ih =>
      intro status
      have ht : sameHead (fun k ↦ (store (a :: xs) (a :: xs) status k).head?) = true := by
        cases a <;> rfl
      have ha : (StackProg.act popBoth).Exec
          (store (a :: xs) (a :: xs) status) (store xs xs status) 1 := by
        simpa only [pop_step] using (StackProg.Exec.act popBoth (store (a :: xs) (a :: xs) status))
      have he := StackProg.Exec.loopTrue ht ha (ih status)
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he
  have ha : (StackProg.act (mark .one)).Exec (store [] [] status) (store [] [] (.one :: status)) 1 := by
    simpa only [mark_step] using (StackProg.Exec.act (mark .one) (store [] [] status))
  have hb : (StackProg.branch bothEmpty (.act (mark .one)) (.act (mark .zero))).Exec
      (store [] [] status) (store [] [] (.one :: status)) 2 :=
    StackProg.Exec.branchTrue (by rfl) ha
  have he := StackProg.Exec.seq (hloop xs status) hb
  simpa [compareProg, Nat.add_assoc] using he


private lemma sameHead_eq (a b : BSym) (left right status : List BSym)
    (h : sameHead (fun k ↦ (store (a :: left) (b :: right) status k).head?) = true) : a = b := by
  cases a <;> cases b <;> simp [sameHead, store] at h ⊢

/-- The comparison loop always stops within 3 min(lengths)+1 steps, preserving equality. -/
private theorem compareLoop_total (left right status : List BSym) :
    ∃ left' right' steps,
      steps ≤ 3 * min left.length right.length + 1 ∧
      (left = right ↔ left' = right') ∧
      sameHead (fun k ↦ (store left' right' status k).head?) = false ∧
      (StackProg.loop sameHead (.act popBoth)).Exec
        (store left right status) (store left' right' status) steps := by
  induction left generalizing right with
  | nil =>
    refine ⟨[], right, 1, by simp, Iff.rfl, ?_, ?_⟩
    · simp [sameHead, store]
    · apply StackProg.Exec.loopFalse
      simp [sameHead, store]
  | cons a left ih =>
    cases right with
    | nil =>
      refine ⟨a :: left, [], 1, by simp, Iff.rfl, ?_, ?_⟩
      · simp [sameHead, store]
      · apply StackProg.Exec.loopFalse
        simp [sameHead, store]
    | cons b right =>
      cases ht : sameHead (fun k ↦ (store (a :: left) (b :: right) status k).head?) with
      | false =>
        exact ⟨a :: left, b :: right, 1, by omega, Iff.rfl, ht, StackProg.Exec.loopFalse ht⟩
      | true =>
        have hab : a = b := sameHead_eq a b left right status ht
        subst b
        obtain ⟨l, r, steps, hb, heq, hstop, hrun⟩ := ih right
        have ha : (StackProg.act popBoth).Exec
            (store (a :: left) (a :: right) status) (store left right status) 1 := by
          simpa only [pop_step] using
            (StackProg.Exec.act popBoth (store (a :: left) (a :: right) status))
        have he := StackProg.Exec.loopTrue ht ha hrun
        refine ⟨l, r, 1 + 1 + 1 + steps, ?_, ?_, hstop, he⟩
        · simp only [List.length_cons, Nat.succ_min_succ]
          omega
        · simpa using heq

private lemma stopped_eq_iff_bothEmpty (left right status : List BSym)
    (hstop : sameHead (fun k ↦ (store left right status k).head?) = false) :
    left = right ↔ bothEmpty (fun k ↦ (store left right status k).head?) = true := by
  cases left with
  | nil => cases right <;> simp [bothEmpty, store]
  | cons a left =>
    cases right with
    | nil => simp [bothEmpty, store]
    | cons b right =>
      have hne : a :: left ≠ b :: right := by
        intro heq
        cases heq
        cases a <;> simp [sameHead, store] at hstop
      simp [bothEmpty, store, hne]

/-- On all input stacks, comparison halts in linear time and its marker exactly reflects equality. -/
theorem compareProg_total (left right status : List BSym) :
    ∃ left' right' marker steps,
      steps ≤ 3 * min left.length right.length + 4 ∧
      (marker = .one ↔ left = right) ∧
      compareProg.Exec (store left right status) (store left' right' (marker :: status)) steps := by
  obtain ⟨left', right', steps, hsteps, heq, hstop, hrun⟩ := compareLoop_total left right status
  have hlast := stopped_eq_iff_bothEmpty left' right' status hstop
  cases ht : bothEmpty (fun k ↦ (store left' right' status k).head?) with
  | false =>
    have ha : (StackProg.act (mark .zero)).Exec (store left' right' status)
        (store left' right' (.zero :: status)) 1 := by
      simpa only [mark_step] using (StackProg.Exec.act (mark .zero) (store left' right' status))
    have hb := StackProg.Exec.branchFalse (p := .act (mark .one)) ht ha
    refine ⟨left', right', .zero, steps + 3, by omega, ?_, ?_⟩
    · constructor
      · intro h
        cases h
      · intro h
        have htrue := hlast.mp (heq.mp h)
        rw [ht] at htrue
        cases htrue
    · exact StackProg.Exec.seq hrun hb
  | true =>
    have ha : (StackProg.act (mark .one)).Exec (store left' right' status)
        (store left' right' (.one :: status)) 1 := by
      simpa only [mark_step] using (StackProg.Exec.act (mark .one) (store left' right' status))
    have hb := StackProg.Exec.branchTrue (q := .act (mark .zero)) ht ha
    refine ⟨left', right', .one, steps + 3, by omega, ?_, ?_⟩
    · constructor
      · intro _
        exact heq.mpr (hlast.mpr ht)
      · intro _
        rfl
    · exact StackProg.Exec.seq hrun hb

end TensorStackCompare

/-- Row-major symbol stream of a finite square matrix. -/
def matrixStream {v : ℕ} (m : Fin v → Fin v → BSym) : List BSym :=
  List.ofFn (fun k : Fin (v*v) ↦ m (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)

@[simp] theorem matrixStream_length {v : ℕ} (m : Fin v → Fin v → BSym) :
    (matrixStream m).length = v*v := by simp [matrixStream]

private lemma rowMajor_lt {v : ℕ} (i j : Fin v) : i.val * v + j.val < v*v := by
  have hi : i.val + 1 ≤ v := by omega
  have hm := Nat.mul_le_mul_right v hi
  have hj := j.isLt
  nlinarith

/-- Indexed positions in matrixStream agree with the input matrix. -/
theorem matrixStream_get {v : ℕ} (m : Fin v → Fin v → BSym) (i j : Fin v) :
    (matrixStream m)[i.val * v + j.val]'(by simpa using rowMajor_lt i j) = m i j := by
  have hi : (⟨i.val * v + j.val, rowMajor_lt i j⟩ : Fin (v*v)) = finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  simp only [matrixStream, List.getElem_ofFn]
  rw [hi, Equiv.symm_apply_apply]

/-- Sampling stride zero after the row offset reads an entire row. -/
theorem gathered_row {v : ℕ} (m : Fin v → Fin v → BSym) (i : Fin v) :
    gatheredPure 0 v ((matrixStream m).drop (i.val * v)) = List.ofFn (m i) := by
  have hpos : ∀ k, k < v → k * (0 + 1) < ((matrixStream m).drop (i.val * v)).length := by
    intro k hk
    have hb := rowMajor_lt i ⟨k, hk⟩
    change i.val * v + k < v*v at hb
    simp only [List.length_drop, matrixStream_length, Nat.zero_add, Nat.mul_one]
    omega
  rw [gatheredPure_eq_ofFn 0 v _ hpos]
  apply congrArg List.ofFn
  funext j
  simp only [List.getElem_drop, Nat.add_zero, Nat.mul_one]
  simpa only [Nat.zero_add, Nat.mul_one] using matrixStream_get m i j

/-- Sampling stride v−1 after the column offset reads an entire column. -/
theorem gathered_column {v : ℕ} (m : Fin v → Fin v → BSym) (i : Fin v) :
    gatheredPure (v-1) v ((matrixStream m).drop i.val) = List.ofFn (fun j ↦ m j i) := by
  have hv : 0 < v := by have := i.isLt; omega
  have hs : v-1+1 = v := Nat.sub_add_cancel (by omega)
  have hpos : ∀ k, k < v → k * (v-1+1) < ((matrixStream m).drop i.val).length := by
    intro k hk
    have hb := rowMajor_lt ⟨k, hk⟩ i
    change k * v + i.val < v*v at hb
    simp only [List.length_drop, matrixStream_length, hs]
    omega
  rw [gatheredPure_eq_ofFn (v-1) v _ hpos]
  apply congrArg List.ofFn
  funext j
  simp only [List.getElem_drop, hs]
  have hh := matrixStream_get m j i
  simpa only [Nat.add_comm] using hh


namespace TensorRowColumnCheck

open StackProgPortLift

private def rowPorts : Fin 6 ↪ Fin 13 := ⟨![0,1,2,3,4,5], by decide⟩
private def colPorts : Fin 6 ↪ Fin 13 := ⟨![6,7,8,9,10,11], by decide⟩
private def cmpPorts : Fin 3 ↪ Fin 13 := ⟨![5,11,12], by decide⟩
private def rowDecode : Fin 13 → Option (Fin 6) :=
  ![some 0,some 1,some 2,some 3,some 4,some 5,none,none,none,none,none,none,none]
private def colDecode : Fin 13 → Option (Fin 6) :=
  ![none,none,none,none,none,none,some 0,some 1,some 2,some 3,some 4,some 5,none]
private def cmpDecode : Fin 13 → Option (Fin 3) :=
  ![none,none,none,none,none,some 0,none,none,none,none,none,some 1,some 2]

private theorem rowDecode_correct (l : Fin 13) (k : Fin 6) :
    rowDecode l = some k ↔ rowPorts k = l := by fin_cases l <;> fin_cases k <;> decide
private theorem colDecode_correct (l : Fin 13) (k : Fin 6) :
    colDecode l = some k ↔ colPorts k = l := by fin_cases l <;> fin_cases k <;> decide
private theorem cmpDecode_correct (l : Fin 13) (k : Fin 3) :
    cmpDecode l = some k ↔ cmpPorts k = l := by fin_cases l <;> fin_cases k <;> decide

/-- Gather a row and column on disjoint copied inputs, then compare the resulting lists. -/
def rowColumnCheckProg : StackProg (Fin 13) BSym :=
  .seq (liftProgC rowPorts rowDecode TensorDiagonalGather.gatherProg)
    (.seq (liftProgC colPorts colDecode TensorDiagonalGather.gatherProg)
      (liftProgC cmpPorts cmpDecode TensorStackCompare.compareProg))

/-- The per-row checker halts for arbitrary input streams, and its marker exactly says
    whether the two sampled lists agree. Preparation of row/column offsets is separate. -/
theorem rowColumnCheck_total (n stride : ℕ) (rowData colData status : List BSym)
    (base : Fin 13 → List BSym)
    (hrow : project rowPorts base =
      TensorDiagonalGather.store rowData [] (List.replicate n .one) [] [] [])
    (hcol : project colPorts base =
      TensorDiagonalGather.store colData (List.replicate stride .one) (List.replicate n .one) [] [] [])
    (hstatus : base 12 = status) :
    ∃ final marker steps,
      steps ≤ (9 * stride + 21) * n + 8 ∧
      (marker = .one ↔ TensorDiagonalGather.gathered 0 n rowData =
        TensorDiagonalGather.gathered stride n colData) ∧
      final 12 = marker :: status ∧ rowColumnCheckProg.Exec base final steps := by
  classical
  obtain ⟨rd, rr, rw, sr, hsr, hr⟩ := TensorDiagonalGather.gatherProg_total 0 n rowData []
  obtain ⟨cd, cr, cw, sc, hsc, hc⟩ := TensorDiagonalGather.gatherProg_total stride n colData []
  let rowOut := (TensorDiagonalGather.gathered 0 n rowData).reverse
  let colOut := (TensorDiagonalGather.gathered stride n colData).reverse
  let rowEnd := TensorDiagonalGather.store rd [] rr rw [] rowOut
  let colEnd := TensorDiagonalGather.store cd (List.replicate stride .one) cr cw [] colOut
  let afterRow := write rowPorts rowEnd base
  let afterCol := write colPorts colEnd afterRow
  have hr' : TensorDiagonalGather.gatherProg.Exec
      (TensorDiagonalGather.store rowData [] (List.replicate n .one) [] [] []) rowEnd sr := by
    simpa only [rowEnd, rowOut, List.replicate_zero, List.append_nil] using hr
  have hc' : TensorDiagonalGather.gatherProg.Exec
      (TensorDiagonalGather.store colData (List.replicate stride .one) (List.replicate n .one) [] [] []) colEnd sc := by
    simpa only [colEnd, colOut, List.append_nil] using hc
  have hcol' : project colPorts afterRow =
      TensorDiagonalGather.store colData (List.replicate stride .one) (List.replicate n .one) [] [] [] := by
    rw [← hcol]
    funext k
    have hdisj : ∀ j : Fin 6, rowPorts j ≠ colPorts k := by
      intro j
      fin_cases j <;> fin_cases k <;> decide
    exact StackProgPortLift.write_outside rowPorts rowEnd base hdisj
  have hrowout : afterCol 5 = rowOut := by
    have hd : ∀ j : Fin 6, colPorts j ≠ (5 : Fin 13) := by intro j; fin_cases j <;> decide
    rw [show afterCol 5 = afterRow 5 from StackProgPortLift.write_outside colPorts colEnd afterRow hd]
    simpa [afterRow, rowPorts, rowEnd, TensorDiagonalGather.store] using
      (StackProgPortLift.write_at rowPorts rowEnd base (5 : Fin 6))
  have hcolout : afterCol 11 = colOut := by
    simpa [afterCol, colPorts, colEnd, TensorDiagonalGather.store] using
      (StackProgPortLift.write_at colPorts colEnd afterRow (5 : Fin 6))
  have hstatus' : afterCol 12 = status := by
    have hcdisj : ∀ j : Fin 6, colPorts j ≠ (12 : Fin 13) := by intro j; fin_cases j <;> decide
    have hrdisj : ∀ j : Fin 6, rowPorts j ≠ (12 : Fin 13) := by intro j; fin_cases j <;> decide
    rw [show afterCol 12 = afterRow 12 from StackProgPortLift.write_outside colPorts colEnd afterRow hcdisj]
    rw [show afterRow 12 = base 12 from StackProgPortLift.write_outside rowPorts rowEnd base hrdisj]
    exact hstatus
  have hcmp : project cmpPorts afterCol = TensorStackCompare.store rowOut colOut status := by
    funext k
    fin_cases k <;> simp [project, cmpPorts, TensorStackCompare.store, hrowout, hcolout, hstatus']
  obtain ⟨r, c, marker, sk, hsk, hmark, hrun⟩ := TensorStackCompare.compareProg_total rowOut colOut status
  have hrLift := lift_exec rowPorts hr' base hrow
  have hcLift := lift_exec colPorts hc' afterRow hcol'
  have hkLift := lift_exec cmpPorts hrun afterCol hcmp
  have he := StackProg.Exec.seq hrLift (StackProg.Exec.seq hcLift hkLift)
  let final := write cmpPorts (TensorStackCompare.store r c (marker :: status)) afterCol
  refine ⟨final, marker, sr + 1 + (sc + 1 + sk), ?_, ?_, ?_, ?_⟩
  · have hlen1 := TensorDiagonalCheck.gathered_length_le 0 n rowData
    have hlen2 := TensorDiagonalCheck.gathered_length_le stride n colData
    have hmin : min rowOut.length colOut.length ≤ n := by
      dsimp [rowOut, colOut]
      simp only [List.length_reverse]
      exact (Nat.min_le_left _ _).trans hlen1
    simp only [Nat.mul_zero, Nat.zero_add] at hsr
    simp only [Nat.add_mul] at hsr hsc ⊢
    nlinarith
  · simpa only [rowOut, colOut, List.reverse_inj] using hmark
  · simpa [final, cmpPorts, TensorStackCompare.store] using
      (StackProgPortLift.write_at cmpPorts (TensorStackCompare.store r c (marker :: status)) afterCol (2 : Fin 3))
  · simpa only [rowColumnCheckProg, liftProgC_eq_liftProg rowPorts rowDecode rowDecode_correct,
      liftProgC_eq_liftProg colPorts colDecode colDecode_correct,
      liftProgC_eq_liftProg cmpPorts cmpDecode cmpDecode_correct, afterRow, afterCol, final] using he


/-- With prepared row/column suffixes, the program marks whether row i equals column i. -/
theorem rowColumnCheck_matrix {v : ℕ} (m : Fin v → Fin v → BSym) (i : Fin v)
    (status : List BSym) (base : Fin 13 → List BSym)
    (hrow : project rowPorts base = TensorDiagonalGather.store
      ((matrixStream m).drop (i.val*v)) [] (List.replicate v .one) [] [] [])
    (hcol : project colPorts base = TensorDiagonalGather.store
      ((matrixStream m).drop i.val) (List.replicate (v-1) .one) (List.replicate v .one) [] [] [])
    (hstatus : base 12 = status) :
    ∃ final marker steps,
      steps ≤ (9 * (v-1) + 21) * v + 8 ∧
      (marker = .one ↔ ∀ j : Fin v, m i j = m j i) ∧
      final 12 = marker :: status ∧ rowColumnCheckProg.Exec base final steps := by
  obtain ⟨final, marker, steps, hb, hm, hf, he⟩ := rowColumnCheck_total v (v-1)
    ((matrixStream m).drop (i.val*v)) ((matrixStream m).drop i.val) status base hrow hcol hstatus
  refine ⟨final, marker, steps, hb, ?_, hf, he⟩
  rw [hm, gathered_eq_pure, gathered_eq_pure, gathered_row, gathered_column, List.ofFn_inj]
  exact funext_iff

end TensorRowColumnCheck
open CookPvsNP ProjSchedTW.Complexity

namespace TensorStackSelect

/-- Data, unary index, selected-symbol output, and status. -/
def store (data index output status : List BSym) : Fin 4 → List BSym :=
  fun k ↦ if k = 0 then data else if k = 1 then index else if k = 2 then output else status

private def canSkip (h : Fin 4 → Option BSym) : Bool :=
  (h 1 == some BSym.one) && (h 0 != none)

private def canRead (h : Fin 4 → Option BSym) : Bool :=
  (h 1 == none) && (h 0 != none)

private def skipAct (_h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 0 ∨ k = 1 then .pop else .keep

private def readAct (h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 2 then match h 0 with | some a => .push a | none => .keep
  else if k = 3 then .push .one else .keep

private def rejectAct (_h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 3 then .push .zero else .keep

/-- Read a symbol at a unary index by scanning; reject if the index is out of range. -/
def selectProg : StackProg (Fin 4) BSym :=
  .seq (.loop canSkip (.act skipAct))
    (.branch canRead (.act readAct) (.act rejectAct))

private lemma skip_step (a : BSym) (data index output status : List BSym) :
    StackProg.applyAct skipAct (store (a :: data) (.one :: index) output status) =
      store data index output status := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, skipAct, store, StackAct.apply]

private lemma read_step (a : BSym) (data output status : List BSym) :
    StackProg.applyAct readAct (store (a :: data) [] output status) =
      store (a :: data) [] (a :: output) (.one :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, readAct, store, StackAct.apply]

/-- Selecting after a pre consumes exactly that pre and writes the next symbol. -/
theorem selectProg_success (pre : List BSym) (a : BSym) (tail output status : List BSym) :
    selectProg.Exec
      (store (pre ++ a :: tail) (List.replicate pre.length .one) output status)
      (store (a :: tail) [] (a :: output) (.one :: status)) (3 * pre.length + 4) := by
  have hloop : ∀ (pre : List BSym),
      (StackProg.loop canSkip (.act skipAct)).Exec
        (store (pre ++ a :: tail) (List.replicate pre.length .one) output status)
        (store (a :: tail) [] output status) (3 * pre.length + 1) := by
    intro pre
    induction pre with
    | nil =>
      apply StackProg.Exec.loopFalse
      rfl
    | cons b pre ih =>
      have ht : canSkip (fun k ↦ (store (b :: (pre ++ a :: tail))
          (.one :: List.replicate pre.length .one) output status k).head?) = true := by
        cases b <;> rfl
      have ha : (StackProg.act skipAct).Exec
          (store (b :: (pre ++ a :: tail)) (.one :: List.replicate pre.length .one) output status)
          (store (pre ++ a :: tail) (List.replicate pre.length .one) output status) 1 := by
        simpa only [skip_step] using
          (StackProg.Exec.act skipAct (store (b :: (pre ++ a :: tail))
            (.one :: List.replicate pre.length .one) output status))
      have he := StackProg.Exec.loopTrue ht ha ih
      simpa [List.replicate_succ, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he
  have ha : (StackProg.act readAct).Exec (store (a :: tail) [] output status)
      (store (a :: tail) [] (a :: output) (.one :: status)) 1 := by
    simpa only [read_step] using (StackProg.Exec.act readAct (store (a :: tail) [] output status))
  have hb : (StackProg.branch canRead (.act readAct) (.act rejectAct)).Exec
      (store (a :: tail) [] output status)
      (store (a :: tail) [] (a :: output) (.one :: status)) 2 :=
    StackProg.Exec.branchTrue (by cases a <;> rfl) ha
  have he := StackProg.Exec.seq (hloop pre) hb
  simpa [selectProg, Nat.add_assoc] using he


private lemma reject_step (data index output status : List BSym) :
    StackProg.applyAct rejectAct (store data index output status) =
      store data index output (.zero :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, rejectAct, store, StackAct.apply]

private theorem selectLoop_total (n : ℕ) (data output status : List BSym) :
    ∃ data' index' steps,
      steps ≤ 3 * min n data.length + 1 ∧
      canSkip (fun k ↦ (store data' index' output status k).head?) = false ∧
      (StackProg.loop canSkip (.act skipAct)).Exec
        (store data (List.replicate n .one) output status) (store data' index' output status) steps := by
  induction n generalizing data with
  | zero =>
    refine ⟨data, [], 1, by simp, ?_, ?_⟩
    · simp [canSkip, store]
    · apply StackProg.Exec.loopFalse
      simp [canSkip, store]
  | succ n ih =>
    cases data with
    | nil =>
      refine ⟨[], .one :: List.replicate n .one, 1, by simp, ?_, ?_⟩
      · simp [canSkip, store]
      · apply StackProg.Exec.loopFalse
        simp [canSkip, store]
    | cons a data =>
      obtain ⟨data', index', steps, hs, hstop, hrun⟩ := ih data
      have ht : canSkip (fun k ↦
          (store (a :: data) (.one :: List.replicate n .one) output status k).head?) = true := by
        cases a <;> rfl
      have ha : (StackProg.act skipAct).Exec
          (store (a :: data) (.one :: List.replicate n .one) output status)
          (store data (List.replicate n .one) output status) 1 := by
        simpa only [skip_step] using
          (StackProg.Exec.act skipAct (store (a :: data) (.one :: List.replicate n .one) output status))
      have he := StackProg.Exec.loopTrue ht ha hrun
      refine ⟨data', index', 1 + 1 + 1 + steps, ?_, hstop, ?_⟩
      · simp only [List.length_cons, Nat.succ_min_succ]
        omega
      · simpa only [List.replicate_succ] using he

/-- The unary-index lookup program halts on every data list, even for out-of-range indices. -/
theorem selectProg_total (n : ℕ) (data output status : List BSym) :
    ∃ data' index' output' marker steps,
      steps ≤ 3 * min n data.length + 4 ∧
      selectProg.Exec (store data (List.replicate n .one) output status)
        (store data' index' output' (marker :: status)) steps := by
  obtain ⟨data', index', steps, hs, hstop, hrun⟩ := selectLoop_total n data output status
  cases ht : canRead (fun k ↦ (store data' index' output status k).head?) with
  | false =>
    have ha : (StackProg.act rejectAct).Exec (store data' index' output status)
        (store data' index' output (.zero :: status)) 1 := by
      simpa only [reject_step] using (StackProg.Exec.act rejectAct (store data' index' output status))
    have hb := StackProg.Exec.branchFalse (p := .act readAct) ht ha
    refine ⟨data', index', output, .zero, steps + 3, by omega, ?_⟩
    exact StackProg.Exec.seq hrun hb
  | true =>
    cases index' with
    | cons a rest => simp [canRead, store] at ht
    | nil =>
      cases data' with
      | nil => simp [canRead, store] at ht
      | cons a rest =>
        have ha : (StackProg.act readAct).Exec (store (a :: rest) [] output status)
            (store (a :: rest) [] (a :: output) (.one :: status)) 1 := by
          simpa only [read_step] using (StackProg.Exec.act readAct (store (a :: rest) [] output status))
        have hb := StackProg.Exec.branchTrue (q := .act rejectAct) ht ha
        refine ⟨a :: rest, [], a :: output, .one, steps + 3, by omega, ?_⟩
        exact StackProg.Exec.seq hrun hb

/-- An index with at least one token left after the data ends is rejected. -/
theorem selectProg_out_of_range (data remaining output status : List BSym) :
    selectProg.Exec
      (store data (List.replicate data.length .one ++ .one :: remaining) output status)
      (store [] (.one :: remaining) output (.zero :: status)) (3 * data.length + 4) := by
  have hloop : ∀ data : List BSym,
      (StackProg.loop canSkip (.act skipAct)).Exec
        (store data (List.replicate data.length .one ++ .one :: remaining) output status)
        (store [] (.one :: remaining) output status) (3 * data.length + 1) := by
    intro data
    induction data with
    | nil =>
      apply StackProg.Exec.loopFalse
      rfl
    | cons a data ih =>
      have ht : canSkip (fun k ↦
          (store (a :: data) (.one :: (List.replicate data.length .one ++ .one :: remaining))
            output status k).head?) = true := by cases a <;> rfl
      have ha : (StackProg.act skipAct).Exec
          (store (a :: data) (.one :: (List.replicate data.length .one ++ .one :: remaining)) output status)
          (store data (List.replicate data.length .one ++ .one :: remaining) output status) 1 := by
        simpa only [skip_step] using (StackProg.Exec.act skipAct
          (store (a :: data) (.one :: (List.replicate data.length .one ++ .one :: remaining)) output status))
      have he := StackProg.Exec.loopTrue ht ha ih
      simpa [List.replicate_succ, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he
  have ha : (StackProg.act rejectAct).Exec
      (store [] (.one :: remaining) output status) (store [] (.one :: remaining) output (.zero :: status)) 1 := by
    simpa only [reject_step] using
      (StackProg.Exec.act rejectAct (store [] (.one :: remaining) output status))
  have hb : (StackProg.branch canRead (.act readAct) (.act rejectAct)).Exec
      (store [] (.one :: remaining) output status) (store [] (.one :: remaining) output (.zero :: status)) 2 :=
    StackProg.Exec.branchFalse (by rfl) ha
  have he := StackProg.Exec.seq (hloop data) hb
  simpa [selectProg, Nat.add_assoc] using he


/-- An index exactly equal to the data length is also out of range and is rejected. -/
theorem selectProg_at_length (data output status : List BSym) :
    selectProg.Exec (store data (List.replicate data.length .one) output status)
      (store [] [] output (.zero :: status)) (3 * data.length + 4) := by
  have hloop : ∀ data : List BSym,
      (StackProg.loop canSkip (.act skipAct)).Exec
        (store data (List.replicate data.length .one) output status)
        (store [] [] output status) (3 * data.length + 1) := by
    intro data
    induction data with
    | nil =>
      apply StackProg.Exec.loopFalse
      rfl
    | cons a data ih =>
      have ht : canSkip (fun k ↦
          (store (a :: data) (.one :: List.replicate data.length .one) output status k).head?) = true := by
        cases a <;> rfl
      have ha : (StackProg.act skipAct).Exec
          (store (a :: data) (.one :: List.replicate data.length .one) output status)
          (store data (List.replicate data.length .one) output status) 1 := by
        simpa only [skip_step] using (StackProg.Exec.act skipAct
          (store (a :: data) (.one :: List.replicate data.length .one) output status))
      have he := StackProg.Exec.loopTrue ht ha ih
      simpa [List.replicate_succ, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he
  have ha : (StackProg.act rejectAct).Exec (store [] [] output status)
      (store [] [] output (.zero :: status)) 1 := by
    simpa only [reject_step] using (StackProg.Exec.act rejectAct (store [] [] output status))
  have hb : (StackProg.branch canRead (.act readAct) (.act rejectAct)).Exec
      (store [] [] output status) (store [] [] output (.zero :: status)) 2 :=
    StackProg.Exec.branchFalse (by rfl) ha
  have he := StackProg.Exec.seq (hloop data) hb
  simpa [selectProg, Nat.add_assoc] using he


/-- The selector implements ordinary list indexing with a linear unary-index cost. -/
theorem selectProg_getElem (xs : List BSym) (k : ℕ) (hk : k < xs.length)
    (output status : List BSym) :
    selectProg.Exec (store xs (List.replicate k .one) output status)
      (store (xs[k] :: xs.drop (k + 1)) [] (xs[k] :: output) (.one :: status)) (3 * k + 4) := by
  have heq : xs.take k ++ xs[k] :: xs.drop (k + 1) = xs := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have ht : (xs.take k).length = k := by simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have he := selectProg_success (xs.take k) xs[k] (xs.drop (k + 1)) output status
  simpa only [heq, ht] using he



/-- Drop up to n symbols, consuming one unary token per symbol, with exact cost. -/
theorem skipLoop_exact (n : ℕ) (data output status : List BSym) :
    (StackProg.loop canSkip (.act skipAct)).Exec
      (store data (List.replicate n .one) output status)
      (store (data.drop n) (List.replicate (n - data.length) .one) output status)
      (3 * min n data.length + 1) := by
  induction n generalizing data with
  | zero =>
    simp only [List.replicate_zero, List.drop_zero, Nat.zero_sub, Nat.zero_min, Nat.mul_zero, Nat.zero_add]
    apply StackProg.Exec.loopFalse
    simp [canSkip, store]
  | succ n ih =>
    cases data with
    | nil =>
      apply StackProg.Exec.loopFalse
      simp [canSkip, store]
    | cons a data =>
      have ht : canSkip (fun k ↦
          (store (a :: data) (.one :: List.replicate n .one) output status k).head?) = true := by
        cases a <;> rfl
      have ha : (StackProg.act skipAct).Exec
          (store (a :: data) (.one :: List.replicate n .one) output status)
          (store data (List.replicate n .one) output status) 1 := by
        simpa only [skip_step] using
          (StackProg.Exec.act skipAct (store (a :: data) (.one :: List.replicate n .one) output status))
      have he := StackProg.Exec.loopTrue ht ha (ih data)
      simpa [List.replicate_succ, Nat.succ_min_succ, Nat.succ_sub_succ,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

end TensorStackSelect

namespace TensorOffsetPrepare
open CookPvsNP ProjSchedTW.Complexity StackProgPortLift TensorStackSelect

/-- Source, row copy, column copy, row offset, column offset, scratch, status. -/
def store (src row col ri ci scratch status : List BSym) : Fin 7 → List BSym :=
  fun k ↦ if k=0 then src else if k=1 then row else if k=2 then col
    else if k=3 then ri else if k=4 then ci else if k=5 then scratch else status

private def rowPorts : Fin 4 ↪ Fin 7 := ⟨![1,3,5,6], by decide⟩
private def colPorts : Fin 4 ↪ Fin 7 := ⟨![2,4,5,6], by decide⟩
private def rowDecode : Fin 7 → Option (Fin 4) := ![none, some 0, none, some 1, none, some 2, some 3]
private def colDecode : Fin 7 → Option (Fin 4) := ![none, none, some 0, none, some 1, some 2, some 3]
private theorem rowDecode_correct (l : Fin 7) (k : Fin 4) :
    rowDecode l = some k ↔ rowPorts k = l := by fin_cases l <;> fin_cases k <;> decide
private theorem colDecode_correct (l : Fin 7) (k : Fin 4) :
    colDecode l = some k ↔ colPorts k = l := by fin_cases l <;> fin_cases k <;> decide

private theorem rowWrite (t : Fin 4 → List BSym) (s : Fin 7 → List BSym) :
    write rowPorts t s = fun k ↦ if k=1 then t 0 else if k=3 then t 1
      else if k=5 then t 2 else if k=6 then t 3 else s k := by
  funext k
  fin_cases k
  · simpa using (write_outside rowPorts t s (l := 0) (by intro j; fin_cases j <;> decide))
  · simpa [rowPorts] using (write_at rowPorts t s 0)
  · simpa using (write_outside rowPorts t s (l := 2) (by intro j; fin_cases j <;> decide))
  · simpa [rowPorts] using (write_at rowPorts t s 1)
  · simpa using (write_outside rowPorts t s (l := 4) (by intro j; fin_cases j <;> decide))
  · simpa [rowPorts] using (write_at rowPorts t s 2)
  · simpa [rowPorts] using (write_at rowPorts t s 3)

private theorem colWrite (t : Fin 4 → List BSym) (s : Fin 7 → List BSym) :
    write colPorts t s = fun k ↦ if k=2 then t 0 else if k=4 then t 1
      else if k=5 then t 2 else if k=6 then t 3 else s k := by
  funext k
  fin_cases k
  · simpa using (write_outside colPorts t s (l := 0) (by intro j; fin_cases j <;> decide))
  · simpa using (write_outside colPorts t s (l := 1) (by intro j; fin_cases j <;> decide))
  · simpa [colPorts] using (write_at colPorts t s 0)
  · simpa using (write_outside colPorts t s (l := 3) (by intro j; fin_cases j <;> decide))
  · simpa [colPorts] using (write_at colPorts t s 1)
  · simpa [colPorts] using (write_at colPorts t s 2)
  · simpa [colPorts] using (write_at colPorts t s 3)

/-- Produce two independent suffixes of a preserved source stream. -/
def prepareProg : StackProg (Fin 7) BSym :=
  .seq (copyProg 0 1 5) (.seq (copyProg 0 2 5)
    (.seq (liftProgC rowPorts rowDecode (.loop TensorStackSelect.canSkip (.act TensorStackSelect.skipAct)))
      (liftProgC colPorts colDecode (.loop TensorStackSelect.canSkip (.act TensorStackSelect.skipAct)))))

/-- This program performs both drops even when an offset exceeds the source length. -/
theorem prepareProg_exec (data status : List BSym) (a b : ℕ) :
    prepareProg.Exec
      (store data [] [] (List.replicate a .one) (List.replicate b .one) [] status)
      (store data (data.drop a) (data.drop b)
        (List.replicate (a-data.length) .one) (List.replicate (b-data.length) .one) [] status)
      ((6*data.length+3)+1+((6*data.length+3)+1+
        ((3*min a data.length+1)+1+(3*min b data.length+1)))) := by
  classical
  let s := store data [] [] (List.replicate a .one) (List.replicate b .one) [] status
  let t := store data data [] (List.replicate a .one) (List.replicate b .one) [] status
  let u := store data data data (List.replicate a .one) (List.replicate b .one) [] status
  let v := store data (data.drop a) data (List.replicate (a-data.length) .one) (List.replicate b .one) [] status
  let w := store data (data.drop a) (data.drop b) (List.replicate (a-data.length) .one) (List.replicate (b-data.length) .one) [] status
  have hc1 : (copyProg (0 : Fin 7) 1 5).Exec s t (6*data.length+3) := by
    have he : s 5 = [] := by simp [s, store]
    have h := stack_copy (0 : Fin 7) 1 5 (by decide) (by decide) (by decide) s he
    have ht : Function.update s 1 (s 0 ++ s 1) = t := by
      funext k; fin_cases k <;> simp [s, t, store, Function.update]
    rw [ht] at h
    simpa [s, store] using h
  have hc2 : (copyProg (0 : Fin 7) 2 5).Exec t u (6*data.length+3) := by
    have he : t 5 = [] := by simp [t, store]
    have h := stack_copy (0 : Fin 7) 2 5 (by decide) (by decide) (by decide) t he
    have hu : Function.update t 2 (t 0 ++ t 2) = u := by
      funext k; fin_cases k <;> simp [t, u, store, Function.update]
    rw [hu] at h
    simpa [t, store] using h
  have hp : project rowPorts u = TensorStackSelect.store data (List.replicate a .one) [] status := by
    funext k; fin_cases k <;> simp [project, rowPorts, u, store, TensorStackSelect.store]
  have hv : write rowPorts (TensorStackSelect.store (data.drop a)
      (List.replicate (a-data.length) .one) [] status) u = v := by
    funext k
    fin_cases k <;> simp [rowWrite, v, u, store, TensorStackSelect.store]
  have hr := lift_exec rowPorts (TensorStackSelect.skipLoop_exact a data [] status) u hp
  rw [hv] at hr
  have hp' : project colPorts v = TensorStackSelect.store data (List.replicate b .one) [] status := by
    funext k; fin_cases k <;> simp [project, colPorts, v, store, TensorStackSelect.store]
  have hw : write colPorts (TensorStackSelect.store (data.drop b)
      (List.replicate (b-data.length) .one) [] status) v = w := by
    funext k
    fin_cases k <;> simp [colWrite, w, v, store, TensorStackSelect.store]
  have hs := lift_exec colPorts (TensorStackSelect.skipLoop_exact b data [] status) v hp'
  rw [hw] at hs
  have he := StackProg.Exec.seq hc1 (StackProg.Exec.seq hc2 (StackProg.Exec.seq hr hs))
  simpa only [prepareProg, liftProgC_eq_liftProg rowPorts rowDecode rowDecode_correct,
    liftProgC_eq_liftProg colPorts colDecode colDecode_correct, s, w] using he

/-- If both offsets are in range, their unary work stacks are exhausted. -/
theorem prepareProg_in_bounds (data status : List BSym) (a b : ℕ)
    (ha : a ≤ data.length) (hb : b ≤ data.length) :
    prepareProg.Exec
      (store data [] [] (List.replicate a .one) (List.replicate b .one) [] status)
      (store data (data.drop a) (data.drop b) [] [] [] status)
      ((6*data.length+3)+1+((6*data.length+3)+1+
        ((3*a+1)+1+(3*b+1)))) := by
  simpa [Nat.sub_eq_zero_of_le ha, Nat.sub_eq_zero_of_le hb,
    Nat.min_eq_left ha, Nat.min_eq_left hb] using prepareProg_exec data status a b

/-- In particular, prepare row i and column i suffixes of a square matrix stream. -/
theorem prepareProg_matrix {v : ℕ} (i : Fin v) (data status : List BSym)
    (hlen : data.length = v*v) :
    prepareProg.Exec
      (store data [] [] (List.replicate (i.val*v) .one) (List.replicate i.val .one) [] status)
      (store data (data.drop (i.val*v)) (data.drop i.val) [] [] [] status)
      ((6*(v*v)+3)+1+((6*(v*v)+3)+1+
        ((3*(i.val*v)+1)+1+(3*i.val+1)))) := by
  have hi := i.isLt
  have hv : 1 ≤ v := by omega
  have ha : i.val * v ≤ data.length := by
    rw [hlen]
    exact Nat.mul_le_mul_right v (Nat.le_of_lt hi)
  have hb : i.val ≤ data.length := by
    rw [hlen]
    nlinarith
  simpa only [hlen] using prepareProg_in_bounds data status (i.val*v) i.val ha hb

end TensorOffsetPrepare

open CookPvsNP ProjSchedTW.Complexity

namespace TensorUnaryMultiply

/-- Source multiplicand, product, work counter, scratch, preserved multiplier. -/
def store (src dst count scratch multiplier : List BSym) : Fin 5 → List BSym :=
  fun k ↦ if k=0 then src else if k=1 then dst else if k=2 then count
    else if k=3 then scratch else multiplier

private def ports : Fin 4 ↪ Fin 5 := ⟨![0,1,2,3], by decide⟩

/-- Copy the multiplier to a loop counter, then repeatedly copy the multiplicand. -/
def multiplyProg : StackProg (Fin 5) BSym :=
  .seq (copyProg 4 2 3) (repeatCopyProg ports)

/-- The unary multiplication program preserves both operands and computes a product. -/
theorem multiplyProg_exec (a b : ℕ) :
    multiplyProg.Exec (store (List.replicate a .one) [] [] [] (List.replicate b .one))
      (store (List.replicate a .one) (List.replicate (b*a) .one) [] [] (List.replicate b .one))
      ((6*b+3)+1+((6*a+7)*b+1)) := by
  classical
  let s := store (List.replicate a .one) [] [] [] (List.replicate b .one)
  let t := store (List.replicate a .one) [] (List.replicate b .one) [] (List.replicate b .one)
  have he : s 3 = [] := by simp [s, store]
  have hmid : Function.update s 2 (s 4 ++ s 2) = t := by
    funext k
    fin_cases k <;> simp [s, t, store, Function.update]
  have hc : (copyProg (4 : Fin 5) 2 3).Exec s t (6*b+3) := by
    have h := stack_copy (4 : Fin 5) 2 3 (by decide) (by decide) (by decide) s he
    rw [hmid] at h
    simpa [s, store] using h
  have hem : t (ports 3) = [] := by simp [t, store, ports]
  have hend : Function.update (Function.update t (ports 2) []) (ports 1)
      ((List.replicate (t (ports 2)).length (t (ports 0))).flatten ++ t (ports 1)) =
      store (List.replicate a .one) (List.replicate (b*a) .one) [] [] (List.replicate b .one) := by
    funext k
    fin_cases k <;> simp [t, store, ports, Function.update]
  have hr : (repeatCopyProg ports).Exec t
      (store (List.replicate a .one) (List.replicate (b*a) .one) [] [] (List.replicate b .one))
      ((6*a+7)*b+1) := by
    have h := stack_repeat_copy ports t hem
    rw [hend] at h
    simpa [t, store, ports] using h
  have hs := StackProg.Exec.seq hc hr
  simpa [multiplyProg, s] using hs

end TensorUnaryMultiply

namespace TensorRowOffsets
open CookPvsNP ProjSchedTW.Complexity StackProgPortLift

/-- Source, row copy, column copy, column offset, status, dimension, index,
    row offset, and two scratch ports. -/
def store (src row col ci status dim idx ri scratch₁ scratch₂ : List BSym) : Fin 10 → List BSym :=
  fun k ↦ if k=0 then src else if k=1 then row else if k=2 then col else if k=3 then ci
    else if k=4 then status else if k=5 then dim else if k=6 then idx else if k=7 then ri
    else if k=8 then scratch₁ else scratch₂

private def mulPorts : Fin 5 ↪ Fin 10 := ⟨![5,7,8,9,6], by decide⟩
private def prepPorts : Fin 7 ↪ Fin 10 := ⟨![0,1,2,7,3,8,4], by decide⟩
private def mulDecode : Fin 10 → Option (Fin 5) :=
  ![none, none, none, none, none, some 0, some 4, some 1, some 2, some 3]
private def prepDecode : Fin 10 → Option (Fin 7) :=
  ![some 0, some 1, some 2, some 4, some 6, none, none, some 3, some 5, none]
private theorem mulDecode_correct (l : Fin 10) (k : Fin 5) :
    mulDecode l = some k ↔ mulPorts k = l := by fin_cases l <;> fin_cases k <;> decide
private theorem prepDecode_correct (l : Fin 10) (k : Fin 7) :
    prepDecode l = some k ↔ prepPorts k = l := by fin_cases l <;> fin_cases k <;> decide

private theorem mulWrite (t : Fin 5 → List BSym) (s : Fin 10 → List BSym) :
    write mulPorts t s = fun k ↦ if k=5 then t 0 else if k=7 then t 1 else if k=8 then t 2 else if k=9 then t 3 else if k=6 then t 4 else s k := by
  funext k
  fin_cases k
  · simpa using (write_outside mulPorts t s (l := 0) (by intro j; fin_cases j <;> decide))
  · simpa using (write_outside mulPorts t s (l := 1) (by intro j; fin_cases j <;> decide))
  · simpa using (write_outside mulPorts t s (l := 2) (by intro j; fin_cases j <;> decide))
  · simpa using (write_outside mulPorts t s (l := 3) (by intro j; fin_cases j <;> decide))
  · simpa using (write_outside mulPorts t s (l := 4) (by intro j; fin_cases j <;> decide))
  · simpa [mulPorts] using (write_at mulPorts t s 0)
  · simpa [mulPorts] using (write_at mulPorts t s 4)
  · simpa [mulPorts] using (write_at mulPorts t s 1)
  · simpa [mulPorts] using (write_at mulPorts t s 2)
  · simpa [mulPorts] using (write_at mulPorts t s 3)

private theorem prepWrite (t : Fin 7 → List BSym) (s : Fin 10 → List BSym) :
    write prepPorts t s = fun k ↦ if k=0 then t 0 else if k=1 then t 1 else if k=2 then t 2 else if k=7 then t 3 else if k=3 then t 4 else if k=8 then t 5 else if k=4 then t 6 else s k := by
  funext k
  fin_cases k
  · simpa [prepPorts] using (write_at prepPorts t s 0)
  · simpa [prepPorts] using (write_at prepPorts t s 1)
  · simpa [prepPorts] using (write_at prepPorts t s 2)
  · simpa [prepPorts] using (write_at prepPorts t s 4)
  · simpa [prepPorts] using (write_at prepPorts t s 6)
  · simpa using (write_outside prepPorts t s (l := 5) (by intro j; fin_cases j <;> decide))
  · simpa using (write_outside prepPorts t s (l := 6) (by intro j; fin_cases j <;> decide))
  · simpa [prepPorts] using (write_at prepPorts t s 3)
  · simpa [prepPorts] using (write_at prepPorts t s 5)
  · simpa using (write_outside prepPorts t s (l := 9) (by intro j; fin_cases j <;> decide))

/-- Compute i*v, copy i, and prepare the two independent source suffixes. -/
def rowOffsetsProg : StackProg (Fin 10) BSym :=
  .seq (liftProgC mulPorts mulDecode TensorUnaryMultiply.multiplyProg)
    (.seq (copyProg 6 3 8) (liftProgC prepPorts prepDecode TensorOffsetPrepare.prepareProg))

/-- The preprocessing program is total even if the requested offsets exceed the stream. -/
theorem rowOffsetsProg_exec (data status : List BSym) (v i : ℕ) :
    rowOffsetsProg.Exec
      (store data [] [] [] status (List.replicate v .one) (List.replicate i .one) [] [] [])
      (store data (data.drop (i*v)) (data.drop i) (List.replicate (i-data.length) .one) status
        (List.replicate v .one) (List.replicate i .one)
        (List.replicate (i*v-data.length) .one) [] [])
      (((6*i+3)+1+((6*v+7)*i+1))+1+((6*i+3)+1+
        ((6*data.length+3)+1+((6*data.length+3)+1+
          ((3*min (i*v) data.length+1)+1+(3*min i data.length+1)))))) := by
  classical
  let s := store data [] [] [] status (List.replicate v .one) (List.replicate i .one) [] [] []
  let t := store data [] [] [] status (List.replicate v .one) (List.replicate i .one) (List.replicate (i*v) .one) [] []
  let u := store data [] [] (List.replicate i .one) status (List.replicate v .one) (List.replicate i .one) (List.replicate (i*v) .one) [] []
  let w := store data (data.drop (i*v)) (data.drop i) (List.replicate (i-data.length) .one) status
      (List.replicate v .one) (List.replicate i .one) (List.replicate (i*v-data.length) .one) [] []
  have hp : project mulPorts s = TensorUnaryMultiply.store (List.replicate v .one) [] [] [] (List.replicate i .one) := by
    funext k; fin_cases k <;> simp [project, mulPorts, s, store, TensorUnaryMultiply.store]
  have ht : write mulPorts (TensorUnaryMultiply.store (List.replicate v .one)
      (List.replicate (i*v) .one) [] [] (List.replicate i .one)) s = t := by
    funext k; fin_cases k <;> simp [mulWrite, s, t, store, TensorUnaryMultiply.store]
  have hm := lift_exec mulPorts (TensorUnaryMultiply.multiplyProg_exec v i) s hp
  rw [ht] at hm
  have hc : (copyProg (6 : Fin 10) 3 8).Exec t u (6*i+3) := by
    have he : t 8 = [] := by simp [t, store]
    have h := stack_copy (6 : Fin 10) 3 8 (by decide) (by decide) (by decide) t he
    have hu : Function.update t 3 (t 6 ++ t 3) = u := by
      funext k; fin_cases k <;> simp [t, u, store, Function.update]
    rw [hu] at h
    simpa [t, store] using h
  have hpr : project prepPorts u = TensorOffsetPrepare.store data [] []
      (List.replicate (i*v) .one) (List.replicate i .one) [] status := by
    funext k; fin_cases k <;> simp [project, prepPorts, u, store, TensorOffsetPrepare.store]
  have hw : write prepPorts (TensorOffsetPrepare.store data (data.drop (i*v)) (data.drop i)
      (List.replicate (i*v-data.length) .one) (List.replicate (i-data.length) .one) [] status) u = w := by
    funext k; fin_cases k <;> simp [prepWrite, u, w, store, TensorOffsetPrepare.store]
  have hprep := lift_exec prepPorts (TensorOffsetPrepare.prepareProg_exec data status (i*v) i) u hpr
  rw [hw] at hprep
  have he := StackProg.Exec.seq hm (StackProg.Exec.seq hc hprep)
  simpa only [rowOffsetsProg, liftProgC_eq_liftProg mulPorts mulDecode mulDecode_correct,
    liftProgC_eq_liftProg prepPorts prepDecode prepDecode_correct, s, w] using he

/-- For a square stream and a valid row, both offset counters are exhausted. -/
theorem rowOffsetsProg_matrix {v : ℕ} (i : Fin v) (data status : List BSym)
    (hlen : data.length = v*v) :
    rowOffsetsProg.Exec
      (store data [] [] [] status (List.replicate v .one) (List.replicate i.val .one) [] [] [])
      (store data (data.drop (i.val*v)) (data.drop i.val) [] status
        (List.replicate v .one) (List.replicate i.val .one) [] [] [])
      (((6*i.val+3)+1+((6*v+7)*i.val+1))+1+((6*i.val+3)+1+
        ((6*(v*v)+3)+1+((6*(v*v)+3)+1+
          ((3*(i.val*v)+1)+1+(3*i.val+1)))))) := by
  have hi := i.isLt
  have hv : 1 ≤ v := by omega
  have ha : i.val*v ≤ data.length := by
    rw [hlen]
    exact Nat.mul_le_mul_right v (Nat.le_of_lt hi)
  have hb : i.val ≤ data.length := by rw [hlen]; nlinarith
  have ha' : i.val*v ≤ v*v := by simpa only [hlen] using ha
  have hb' : i.val ≤ v*v := by simpa only [hlen] using hb
  simpa [hlen, Nat.sub_eq_zero_of_le ha', Nat.sub_eq_zero_of_le hb',
    Nat.min_eq_left ha', Nat.min_eq_left hb'] using rowOffsetsProg_exec data status v i.val

end TensorRowOffsets

open CookPvsNP ProjSchedTW.Complexity
namespace TensorTripleCopy

def store (src a b c scratch : List BSym) : Fin 5 → List BSym :=
  fun k ↦ if k=0 then src else if k=1 then a else if k=2 then b else if k=3 then c else scratch

/-- Preserve the source while making three copies in distinct empty ports. -/
def tripleCopyProg : StackProg (Fin 5) BSym :=
  .seq (copyProg 0 1 4) (.seq (copyProg 0 2 4) (copyProg 0 3 4))

theorem tripleCopyProg_exec (xs : List BSym) :
    tripleCopyProg.Exec (store xs [] [] [] []) (store xs xs xs xs [])
      ((6*xs.length+3)+1+((6*xs.length+3)+1+(6*xs.length+3))) := by
  classical
  let s := store xs [] [] [] []
  let t := store xs xs [] [] []
  let u := store xs xs xs [] []
  let v := store xs xs xs xs []
  have h1 : (copyProg (0 : Fin 5) 1 4).Exec s t (6*xs.length+3) := by
    have he : s 4 = [] := by simp [s, store]
    have h := stack_copy (0 : Fin 5) 1 4 (by decide) (by decide) (by decide) s he
    have ht : Function.update s 1 (s 0 ++ s 1) = t := by
      funext k; fin_cases k <;> simp [s, t, store, Function.update]
    rw [ht] at h
    simpa [s, store] using h
  have h2 : (copyProg (0 : Fin 5) 2 4).Exec t u (6*xs.length+3) := by
    have he : t 4 = [] := by simp [t, store]
    have h := stack_copy (0 : Fin 5) 2 4 (by decide) (by decide) (by decide) t he
    have hu : Function.update t 2 (t 0 ++ t 2) = u := by
      funext k; fin_cases k <;> simp [t, u, store, Function.update]
    rw [hu] at h
    simpa [t, store] using h
  have h3 : (copyProg (0 : Fin 5) 3 4).Exec u v (6*xs.length+3) := by
    have he : u 4 = [] := by simp [u, store]
    have h := stack_copy (0 : Fin 5) 3 4 (by decide) (by decide) (by decide) u he
    have hv : Function.update u 3 (u 0 ++ u 3) = v := by
      funext k; fin_cases k <;> simp [u, v, store, Function.update]
    rw [hv] at h
    simpa [u, store] using h
  simpa [tripleCopyProg, s, v] using StackProg.Exec.seq h1 (StackProg.Exec.seq h2 h3)

/-- Make two counts of v and one stride of v−1 for a nonempty square matrix. -/
def dimensionCopiesProg : StackProg (Fin 5) BSym :=
  .seq tripleCopyProg (.act (fun _ k ↦ if k=3 then .pop else .keep))

theorem dimensionCopiesProg_exec (v : ℕ) :
    dimensionCopiesProg.Exec (store (List.replicate (v+1) .one) [] [] [] [])
      (store (List.replicate (v+1) .one) (List.replicate (v+1) .one)
        (List.replicate (v+1) .one) (List.replicate v .one) [])
      (((6*(v+1)+3)+1+((6*(v+1)+3)+1+(6*(v+1)+3)))+1+1) := by
  let xs := List.replicate (v+1) BSym.one
  have ha : (StackProg.act (fun _ (k : Fin 5) ↦ if k=3 then .pop else .keep)).Exec
      (store xs xs xs xs [])
      (store xs xs xs (List.replicate v .one) []) 1 := by
    have he : StackProg.applyAct (fun _ (k : Fin 5) ↦ if k=3 then .pop else .keep)
        (store xs xs xs xs []) = (store xs xs xs (List.replicate v .one) []) := by
      funext k
      fin_cases k <;> simp [xs, store, StackProg.applyAct, StackAct.apply, List.replicate_succ]
    simpa only [he] using StackProg.Exec.act (fun _ (k : Fin 5) ↦ if k=3 then .pop else .keep)
      (store xs xs xs xs [])
  have h := StackProg.Exec.seq (tripleCopyProg_exec xs) ha
  simpa [dimensionCopiesProg, xs] using h

end TensorTripleCopy

namespace TensorRowCheckIntegrated
open CookPvsNP ProjSchedTW.Complexity StackProgPortLift

def store (src dim idx rd rs rn rw rk ro cd cs cn cw ck co status : List BSym) : Fin 16 → List BSym :=
  fun k ↦ if k=0 then src else if k=1 then dim else if k=2 then idx else if k=3 then rd
    else if k=4 then rs else if k=5 then rn else if k=6 then rw else if k=7 then rk
    else if k=8 then ro else if k=9 then cd else if k=10 then cs else if k=11 then cn
    else if k=12 then cw else if k=13 then ck else if k=14 then co else status

private def offsetPorts : Fin 10 ↪ Fin 16 := ⟨![0,3,9,6,15,1,2,7,8,14], by decide⟩
private def dimPorts : Fin 5 ↪ Fin 16 := ⟨![1,5,11,10,8], by decide⟩
private def checkPorts : Fin 13 ↪ Fin 16 := ⟨![3,4,5,6,7,8,9,10,11,12,13,14,15], by decide⟩
private def offsetDecode : Fin 16 → Option (Fin 10) :=
  ![some 0,some 5,some 6,some 1,none,none,some 3,some 7,some 8,some 2,none,none,none,none,some 9,some 4]
private def dimDecode : Fin 16 → Option (Fin 5) :=
  ![none,some 0,none,none,none,some 1,none,none,some 4,none,some 3,some 2,none,none,none,none]
private def checkDecode : Fin 16 → Option (Fin 13) :=
  ![none,none,none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12]
private theorem offsetDecode_correct (l : Fin 16) (k : Fin 10) :
    offsetDecode l = some k ↔ offsetPorts k = l := by fin_cases l <;> fin_cases k <;> decide
private theorem dimDecode_correct (l : Fin 16) (k : Fin 5) :
    dimDecode l = some k ↔ dimPorts k = l := by fin_cases l <;> fin_cases k <;> decide
private theorem checkDecode_correct (l : Fin 16) (k : Fin 13) :
    checkDecode l = some k ↔ checkPorts k = l := by fin_cases l <;> fin_cases k <;> decide

private theorem offsetWrite (t : Fin 10 → List BSym) (s : Fin 16 → List BSym) :
    write offsetPorts t s = fun k ↦ if k=0 then t 0 else if k=3 then t 1 else if k=9 then t 2 else if k=6 then t 3 else if k=15 then t 4 else if k=1 then t 5 else if k=2 then t 6 else if k=7 then t 7 else if k=8 then t 8 else if k=14 then t 9 else s k := by
  funext k
  fin_cases k
  · simpa [offsetPorts] using (write_at offsetPorts t s 0)
  · simpa [offsetPorts] using (write_at offsetPorts t s 5)
  · simpa [offsetPorts] using (write_at offsetPorts t s 6)
  · simpa [offsetPorts] using (write_at offsetPorts t s 1)
  · simpa using (write_outside offsetPorts t s (l := 4) (by intro j; fin_cases j <;> decide))
  · simpa using (write_outside offsetPorts t s (l := 5) (by intro j; fin_cases j <;> decide))
  · simpa [offsetPorts] using (write_at offsetPorts t s 3)
  · simpa [offsetPorts] using (write_at offsetPorts t s 7)
  · simpa [offsetPorts] using (write_at offsetPorts t s 8)
  · simpa [offsetPorts] using (write_at offsetPorts t s 2)
  · simpa using (write_outside offsetPorts t s (l := 10) (by intro j; fin_cases j <;> decide))
  · simpa using (write_outside offsetPorts t s (l := 11) (by intro j; fin_cases j <;> decide))
  · simpa using (write_outside offsetPorts t s (l := 12) (by intro j; fin_cases j <;> decide))
  · simpa using (write_outside offsetPorts t s (l := 13) (by intro j; fin_cases j <;> decide))
  · simpa [offsetPorts] using (write_at offsetPorts t s 9)
  · simpa [offsetPorts] using (write_at offsetPorts t s 4)

private theorem dimWrite (t : Fin 5 → List BSym) (s : Fin 16 → List BSym) :
    write dimPorts t s = fun k ↦ if k=1 then t 0 else if k=5 then t 1 else if k=11 then t 2 else if k=10 then t 3 else if k=8 then t 4 else s k := by
  funext k
  fin_cases k
  · simpa using (write_outside dimPorts t s (l := 0) (by intro j; fin_cases j <;> decide))
  · simpa [dimPorts] using (write_at dimPorts t s 0)
  · simpa using (write_outside dimPorts t s (l := 2) (by intro j; fin_cases j <;> decide))
  · simpa using (write_outside dimPorts t s (l := 3) (by intro j; fin_cases j <;> decide))
  · simpa using (write_outside dimPorts t s (l := 4) (by intro j; fin_cases j <;> decide))
  · simpa [dimPorts] using (write_at dimPorts t s 1)
  · simpa using (write_outside dimPorts t s (l := 6) (by intro j; fin_cases j <;> decide))
  · simpa using (write_outside dimPorts t s (l := 7) (by intro j; fin_cases j <;> decide))
  · simpa [dimPorts] using (write_at dimPorts t s 4)
  · simpa using (write_outside dimPorts t s (l := 9) (by intro j; fin_cases j <;> decide))
  · simpa [dimPorts] using (write_at dimPorts t s 3)
  · simpa [dimPorts] using (write_at dimPorts t s 2)
  · simpa using (write_outside dimPorts t s (l := 12) (by intro j; fin_cases j <;> decide))
  · simpa using (write_outside dimPorts t s (l := 13) (by intro j; fin_cases j <;> decide))
  · simpa using (write_outside dimPorts t s (l := 14) (by intro j; fin_cases j <;> decide))
  · simpa using (write_outside dimPorts t s (l := 15) (by intro j; fin_cases j <;> decide))

/-- Prepare row/column suffixes, counts, and stride, then compare the samples. -/
def rowCheckProg : StackProg (Fin 16) BSym :=
  .seq (liftProgC offsetPorts offsetDecode TensorRowOffsets.rowOffsetsProg)
    (.seq (liftProgC dimPorts dimDecode TensorTripleCopy.dimensionCopiesProg)
      (liftProgC checkPorts checkDecode TensorRowColumnCheck.rowColumnCheckProg))

/-- One concrete row-versus-column test for an arbitrary square matrix.
    The original matrix stream, dimension, and row index are preserved. -/
theorem rowCheckProg_matrix {n : ℕ} (m : Fin (n+1) → Fin (n+1) → BSym)
    (i : Fin (n+1)) (status : List BSym) :
    ∃ final marker steps,
      steps ≤ (((6*i.val+3)+1+((6*(n+1)+7)*i.val+1))+1+((6*i.val+3)+1+
        ((6*((n+1)*(n+1))+3)+1+((6*((n+1)*(n+1))+3)+1+
          ((3*(i.val*(n+1))+1)+1+(3*i.val+1)))))) + 1 +
        (((6*(n+1)+3)+1+((6*(n+1)+3)+1+(6*(n+1)+3)))+1+1) + 1 +
        ((9*n+21)*(n+1)+8) ∧
      (marker = .one ↔ ∀ j, m i j = m j i) ∧
      final 0 = matrixStream m ∧ final 1 = List.replicate (n+1) .one ∧
      final 2 = List.replicate i.val .one ∧ final 15 = marker :: status ∧
      rowCheckProg.Exec
        (store (matrixStream m) (List.replicate (n+1) .one) (List.replicate i.val .one)
          [] [] [] [] [] [] [] [] [] [] [] [] status) final steps := by
  classical
  let data := matrixStream m
  let dim := List.replicate (n+1) BSym.one
  let idx := List.replicate i.val BSym.one
  let s := store data dim idx [] [] [] [] [] [] [] [] [] [] [] [] status
  let t := store data dim idx (data.drop (i.val*(n+1))) [] [] [] [] []
    (data.drop i.val) [] [] [] [] [] status
  let u := store data dim idx (data.drop (i.val*(n+1))) [] dim [] [] []
    (data.drop i.val) (List.replicate n .one) dim [] [] [] status
  have ho : project offsetPorts s = TensorRowOffsets.store data [] [] [] status dim idx [] [] [] := by
    funext k; fin_cases k <;> simp [project, offsetPorts, s, store, TensorRowOffsets.store]
  have ht : write offsetPorts (TensorRowOffsets.store data (data.drop (i.val*(n+1)))
      (data.drop i.val) [] status dim idx [] [] []) s = t := by
    funext k; fin_cases k <;> simp [offsetWrite, s, t, store, TensorRowOffsets.store]
  have hlen : data.length = (n+1)*(n+1) := matrixStream_length m
  have hrun := lift_exec offsetPorts (TensorRowOffsets.rowOffsetsProg_matrix i data status hlen) s ho
  rw [ht] at hrun
  have hd : project dimPorts t = TensorTripleCopy.store dim [] [] [] [] := by
    funext k; fin_cases k <;> simp [project, dimPorts, t, store, TensorTripleCopy.store]
  have hu : write dimPorts (TensorTripleCopy.store dim dim dim (List.replicate n .one) []) t = u := by
    funext k; fin_cases k <;> simp [dimWrite, t, u, store, TensorTripleCopy.store]
  have hdim := lift_exec dimPorts (TensorTripleCopy.dimensionCopiesProg_exec n) t hd
  rw [hu] at hdim
  let q := project checkPorts u
  have hrow : project TensorRowColumnCheck.rowPorts q = TensorDiagonalGather.store
      (data.drop (i.val*(n+1))) [] (List.replicate (n+1) .one) [] [] [] := by
    funext k; fin_cases k <;> simp [q, project, checkPorts, TensorRowColumnCheck.rowPorts,
      u, store, TensorDiagonalGather.store, dim]
  have hcol : project TensorRowColumnCheck.colPorts q = TensorDiagonalGather.store
      (data.drop i.val) (List.replicate ((n+1)-1) .one) (List.replicate (n+1) .one) [] [] [] := by
    funext k; fin_cases k <;> simp [q, project, checkPorts, TensorRowColumnCheck.colPorts,
      u, store, TensorDiagonalGather.store, dim]
  have hstatus : q 12 = status := by simp [q, project, checkPorts, u, store]
  obtain ⟨z, marker, c, hc, hm, hz, hcheck⟩ :=
    TensorRowColumnCheck.rowColumnCheck_matrix m i status q hrow hcol hstatus
  let final := write checkPorts z u
  have hf0 : final 0 = data := by
    have hh : ∀ j : Fin 13, checkPorts j ≠ (0 : Fin 16) := by intro j; fin_cases j <;> decide
    simpa [final, u, store] using write_outside checkPorts z u hh
  have hf1 : final 1 = dim := by
    have hh : ∀ j : Fin 13, checkPorts j ≠ (1 : Fin 16) := by intro j; fin_cases j <;> decide
    simpa [final, u, store] using write_outside checkPorts z u hh
  have hf2 : final 2 = idx := by
    have hh : ∀ j : Fin 13, checkPorts j ≠ (2 : Fin 16) := by intro j; fin_cases j <;> decide
    simpa [final, u, store] using write_outside checkPorts z u hh
  have hf15 : final 15 = marker :: status := by
    simpa [final, checkPorts, hz] using write_at checkPorts z u 12
  have hcheck' := lift_exec checkPorts hcheck u rfl
  have he := StackProg.Exec.seq hrun (StackProg.Exec.seq hdim hcheck')
  let stepCount := (((6*i.val+3)+1+((6*(n+1)+7)*i.val+1))+1+((6*i.val+3)+1+
        ((6*((n+1)*(n+1))+3)+1+((6*((n+1)*(n+1))+3)+1+
          ((3*(i.val*(n+1))+1)+1+(3*i.val+1)))))) + 1 +
        ((((6*(n+1)+3)+1+((6*(n+1)+3)+1+(6*(n+1)+3)))+1+1) + 1 + c)
  refine ⟨final, marker, stepCount, ?_, hm, ?_, ?_, ?_, hf15, ?_⟩
  · have hc' : c ≤ (9*n+21)*(n+1)+8 := by simpa using hc
    dsimp only [stepCount]
    omega
  · simpa [data] using hf0
  · simpa [dim] using hf1
  · simpa [idx] using hf2
  · simpa only [rowCheckProg, liftProgC_eq_liftProg offsetPorts offsetDecode offsetDecode_correct,
      liftProgC_eq_liftProg dimPorts dimDecode dimDecode_correct,
      liftProgC_eq_liftProg checkPorts checkDecode checkDecode_correct, s, final, data, dim, idx, stepCount] using he

end TensorRowCheckIntegrated

open CookPvsNP

/-- A single atomic stack action can increase any one stack by at most one. -/
private theorem stack_applyAct_length_le {K A : Type} (f : (K → Option A) → K → StackAct A)
    (s : K → List A) (k : K) :
    ((StackProg.applyAct f s) k).length ≤ (s k).length + 1 := by
  simp only [StackProg.applyAct]
  cases h : f (fun j ↦ (s j).head?) k with
  | keep => simp [StackAct.apply]
  | push a => simp [StackAct.apply]
  | pop =>
    cases hs : s k with
    | nil => simp [StackAct.apply, hs]
    | cons a tail => simp [StackAct.apply, hs] <;> omega

/-- Every individual stack in a structured execution grows by at most the
    total source-step count, irrespective of the program or input alphabet. -/
theorem stack_exec_length_le {K A : Type} {p : StackProg K A} {s t : K → List A} {n : ℕ}
    (h : p.Exec s t n) : ∀ k, (t k).length ≤ (s k).length + n := by
  induction h with
  | act f s => exact stack_applyAct_length_le f s
  | seq hp hq ihp ihq =>
    intro k
    have h1 := ihp k
    have h2 := ihq k
    omega
  | branchTrue ht hp ih =>
    intro k
    have h1 := ih k
    omega
  | branchFalse ht hp ih =>
    intro k
    have h1 := ih k
    omega
  | loopFalse ht =>
    intro k
    omega
  | loopTrue ht hp hl ihp ihl =>
    intro k
    have h1 := ihp k
    have h2 := ihl k
    omega

open CookPvsNP ProjSchedTW.Complexity
namespace TensorStackClear

private def hasTop {n : ℕ} (p : Fin n) (h : Fin n → Option BSym) : Bool :=
  (h p).isSome
private def popTop {n : ℕ} (p : Fin n) (_ : Fin n → Option BSym) (q : Fin n) : StackAct BSym :=
  if q = p then .pop else .keep

/-- Remove all symbols on one port and preserve all other ports. -/
def clearProg {n : ℕ} (p : Fin n) : StackProg (Fin n) BSym :=
  .loop (hasTop p) (.act (popTop p))

/-- Clearing an arbitrary port has exact linear cost and preserves every other port. -/
theorem clearProg_exec {n : ℕ} (p : Fin n) (base : Fin n → List BSym) (xs : List BSym) :
    (clearProg p).Exec (Function.update base p xs) (Function.update base p []) (3*xs.length+1) := by
  induction xs with
  | nil =>
    apply StackProg.Exec.loopFalse
    simp [hasTop]
  | cons a xs ih =>
    have ht : hasTop p (fun q ↦ (Function.update base p (a :: xs) q).head?) = true := by
      simp [hasTop]
    have ha : (StackProg.act (popTop p)).Exec (Function.update base p (a :: xs))
        (Function.update base p xs) 1 := by
      have he : StackProg.applyAct (popTop p) (Function.update base p (a :: xs)) =
          Function.update base p xs := by
        funext q
        by_cases h : q = p
        · subst q; simp [StackProg.applyAct, popTop, StackAct.apply]
        · simp [StackProg.applyAct, popTop, StackAct.apply, h]
      simpa only [he] using StackProg.Exec.act (popTop p) (Function.update base p (a :: xs))
    have hs := StackProg.Exec.loopTrue ht ha ih
    simpa [clearProg, List.length_cons, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

end TensorStackClear

namespace TensorStackClear

/-- Clear each port in a fixed finite list. -/
def clearAllProg {n : ℕ} : List (Fin n) → StackProg (Fin n) BSym
  | [] => .act (fun _ _ ↦ .keep)
  | p :: ps => .seq (clearProg p) (clearAllProg ps)

def clearedState {n : ℕ} : List (Fin n) → (Fin n → List BSym) → (Fin n → List BSym)
  | [], s => s
  | p :: ps, s => clearedState ps (Function.update s p [])

def clearAllCost {n : ℕ} : List (Fin n) → (Fin n → List BSym) → ℕ
  | [], _ => 1
  | p :: ps, s => 3 * (s p).length + 1 + 1 + clearAllCost ps (Function.update s p [])

/-- Sequential clearing has the explicitly computed cost. -/
theorem clearAllProg_exec {n : ℕ} (ps : List (Fin n)) (s : Fin n → List BSym) :
    (clearAllProg ps).Exec s (clearedState ps s) (clearAllCost ps s) := by
  induction ps generalizing s with
  | nil =>
    have he : StackProg.applyAct (fun _ _ ↦ .keep) s = s := by
      funext q
      simp [StackProg.applyAct, StackAct.apply]
    simpa only [clearAllProg, clearedState, clearAllCost, he]
      using StackProg.Exec.act (fun _ _ ↦ .keep) s
  | cons p ps ih =>
    have hs : Function.update s p (s p) = s := Function.update_eq_self p s
    have h1 := clearProg_exec p s (s p)
    rw [hs] at h1
    have h2 := ih (Function.update s p [])
    simpa only [clearAllProg, clearedState, clearAllCost] using StackProg.Exec.seq h1 h2

/-- Empty ports stay empty throughout clearing. -/
theorem clearedState_preserves_empty {n : ℕ} (ps : List (Fin n)) (s : Fin n → List BSym)
    (q : Fin n) (hq : s q = []) : clearedState ps s q = [] := by
  induction ps generalizing s with
  | nil => exact hq
  | cons p ps ih =>
    apply ih
    by_cases h : q = p
    · subst q; simp
    · simpa [Function.update, h, Ne.symm h] using hq

/-- Every listed port is empty afterwards, even if it appears more than once. -/
theorem clearedState_empty_of_mem {n : ℕ} (ps : List (Fin n)) (s : Fin n → List BSym)
    (q : Fin n) (hq : q ∈ ps) : clearedState ps s q = [] := by
  induction ps generalizing s with
  | nil => simp at hq
  | cons p ps ih =>
    rcases List.mem_cons.mp hq with h | h
    · subst p
      change clearedState ps (Function.update s q []) q = []
      exact clearedState_preserves_empty ps (Function.update s q []) q (by simp)
    · exact ih (Function.update s p []) h

/-- Ports outside the list retain their original contents. -/
theorem clearedState_eq_of_not_mem {n : ℕ} (ps : List (Fin n)) (s : Fin n → List BSym)
    (q : Fin n) (hq : q ∉ ps) : clearedState ps s q = s q := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    have hqp : q ≠ p := by intro h; apply hq; simp [h]
    have hqs : q ∉ ps := by intro h; apply hq; simp [h]
    rw [clearedState, ih (Function.update s p []) hqs]
    simp [Function.update, hqp, Ne.symm hqp]

/-- A uniform initial length bound gives a linear bound in the port-list length. -/
theorem clearAllCost_bound {n : ℕ} (ps : List (Fin n)) (s : Fin n → List BSym)
    (B : ℕ) (hB : ∀ q, (s q).length ≤ B) :
    clearAllCost ps s ≤ ps.length * (3*B+2) + 1 := by
  induction ps generalizing s with
  | nil => simp [clearAllCost]
  | cons p ps ih =>
    have hB' : ∀ q, ((Function.update s p []) q).length ≤ B := by
      intro q
      by_cases h : q = p
      · subst q; simp
      · simpa [Function.update, h, Ne.symm h] using hB q
    have h := ih (Function.update s p []) hB'
    simp only [clearAllCost, List.length_cons, Nat.succ_mul] at *
    have hp := hB p
    omega

end TensorStackClear

namespace TensorRowCheckClean
open CookPvsNP ProjSchedTW.Complexity

/-- The twelve row/column scratch ports; ports 0, 1, 2, 15 are the frame. -/
def scratchPorts : List (Fin 16) := [3,4,5,6,7,8,9,10,11,12,13,14]

def rowCheckCleanProg : StackProg (Fin 16) BSym :=
  .seq TensorRowCheckIntegrated.rowCheckProg (TensorStackClear.clearAllProg scratchPorts)

/-- After a row comparison, clear every scratch port while preserving the input
    and the newly produced comparison marker. -/
theorem rowCheckCleanProg_matrix {n : ℕ} (m : Fin (n+1) → Fin (n+1) → BSym)
    (i : Fin (n+1)) (status : List BSym) :
    ∃ final marker steps,
      (marker = .one ↔ ∀ j, m i j = m j i) ∧
      final 0 = matrixStream m ∧ final 1 = List.replicate (n+1) .one ∧
      final 2 = List.replicate i.val .one ∧ final 15 = marker :: status ∧
      (∀ q ∈ scratchPorts, final q = []) ∧
      rowCheckCleanProg.Exec
        (TensorRowCheckIntegrated.store (matrixStream m) (List.replicate (n+1) .one)
          (List.replicate i.val .one) [] [] [] [] [] [] [] [] [] [] [] [] status) final steps ∧
      steps ≤
        let C := (((6*i.val+3)+1+((6*(n+1)+7)*i.val+1))+1+((6*i.val+3)+1+
          ((6*((n+1)*(n+1))+3)+1+((6*((n+1)*(n+1))+3)+1+
            ((3*(i.val*(n+1))+1)+1+(3*i.val+1)))))) + 1 +
          (((6*(n+1)+3)+1+((6*(n+1)+3)+1+(6*(n+1)+3)))+1+1) + 1 +
          ((9*n+21)*(n+1)+8)
        C+1+12*(3*((n+1)*(n+1)+(n+1)+i.val+status.length+C)+2)+1 := by
  classical
  let start := TensorRowCheckIntegrated.store (matrixStream m) (List.replicate (n+1) .one)
    (List.replicate i.val .one) [] [] [] [] [] [] [] [] [] [] [] [] status
  obtain ⟨mid, marker, c, hc, hm, h0, h1, h2, h15, hrun⟩ :=
    TensorRowCheckIntegrated.rowCheckProg_matrix m i status
  let B := (n+1)*(n+1)+(n+1)+i.val+status.length+c
  have hb : ∀ q, (mid q).length ≤ B := by
    intro q
    have h := stack_exec_length_le hrun q
    have hin : (start q).length ≤ (n+1)*(n+1)+(n+1)+i.val+status.length := by
      fin_cases q <;> simp [start, TensorRowCheckIntegrated.store, matrixStream_length] <;> omega
    dsimp only [B]
    change (mid q).length ≤ _
    change (mid q).length ≤ (start q).length+c at h
    omega
  let final := TensorStackClear.clearedState scratchPorts mid
  have hclean := TensorStackClear.clearAllProg_exec scratchPorts mid
  have hcost := TensorStackClear.clearAllCost_bound scratchPorts mid B hb
  have he := StackProg.Exec.seq hrun hclean
  have hnot0 : (0 : Fin 16) ∉ scratchPorts := by decide
  have hnot1 : (1 : Fin 16) ∉ scratchPorts := by decide
  have hnot2 : (2 : Fin 16) ∉ scratchPorts := by decide
  have hnot15 : (15 : Fin 16) ∉ scratchPorts := by decide
  have hf0 : final 0 = matrixStream m := by
    rw [show final 0 = mid 0 from TensorStackClear.clearedState_eq_of_not_mem scratchPorts mid 0 hnot0, h0]
  have hf1 : final 1 = List.replicate (n+1) .one := by
    rw [show final 1 = mid 1 from TensorStackClear.clearedState_eq_of_not_mem scratchPorts mid 1 hnot1, h1]
  have hf2 : final 2 = List.replicate i.val .one := by
    rw [show final 2 = mid 2 from TensorStackClear.clearedState_eq_of_not_mem scratchPorts mid 2 hnot2, h2]
  have hf15 : final 15 = marker :: status := by
    rw [show final 15 = mid 15 from TensorStackClear.clearedState_eq_of_not_mem scratchPorts mid 15 hnot15, h15]
  refine ⟨final, marker, c+1+TensorStackClear.clearAllCost scratchPorts mid,
    hm, hf0, hf1, hf2, hf15, ?_, ?_, ?_⟩
  · intro q hq
    exact TensorStackClear.clearedState_empty_of_mem scratchPorts mid q hq
  · simpa only [rowCheckCleanProg, start, final] using he
  · dsimp only
    have hlenScratch : scratchPorts.length = 12 := by decide
    rw [hlenScratch] at hcost
    dsimp only [B] at hcost
    omega

end TensorRowCheckClean

namespace TensorSymmetryIter
open CookPvsNP ProjSchedTW.Complexity StackProgPortLift

/-- Master matrix, dimension, processed-row index, marker stack, countdown. -/
def store (data dim idx status count : List BSym) : Fin 17 → List BSym :=
  fun k ↦ if k=0 then data else if k=1 then dim else if k=2 then idx
    else if k=15 then status else if k=16 then count else []

private def ports : Fin 16 ↪ Fin 17 := ⟨Fin.castSucc, Fin.castSucc_injective _⟩
private def decode (k : Fin 17) : Option (Fin 16) :=
  if h : k.val < 16 then some ⟨k.val, h⟩ else none
private theorem decode_correct (l : Fin 17) (k : Fin 16) :
    decode l = some k ↔ ports k = l := by fin_cases l <;> fin_cases k <;> decide
private def more (h : Fin 17 → Option BSym) : Bool := h 16 == some .one
private def nextAct (_ : Fin 17 → Option BSym) (k : Fin 17) : StackAct BSym :=
  if k=2 then .push .one else if k=16 then .pop else .keep

/-- Compare one row, reset its scratch ports, increment the row index, and
    consume one countdown token. -/
def iterationProg : StackProg (Fin 17) BSym :=
  .seq (liftProgC ports decode TensorRowCheckClean.rowCheckCleanProg) (.act nextAct)

/-- Repeat the iteration while a unary countdown token remains. -/
def symmetryLoop : StackProg (Fin 17) BSym := .loop more iterationProg

/-- Polynomial bound for one cleaned row comparison. -/
def rowCostBound (n i statusLength : ℕ) : ℕ :=
  let C := (((6*i+3)+1+((6*(n+1)+7)*i+1))+1+((6*i+3)+1+
    ((6*((n+1)*(n+1))+3)+1+((6*((n+1)*(n+1))+3)+1+
      ((3*(i*(n+1))+1)+1+(3*i+1)))))) + 1 +
    (((6*(n+1)+3)+1+((6*(n+1)+3)+1+(6*(n+1)+3)))+1+1) + 1 +
    ((9*n+21)*(n+1)+8)
  C+1+12*(3*((n+1)*(n+1)+(n+1)+i+statusLength+C)+2)+1

theorem rowCostBound_mono (n : ℕ) {i j a b : ℕ} (hij : i ≤ j) (hab : a ≤ b) :
    rowCostBound n i a ≤ rowCostBound n j b := by
  dsimp [rowCostBound]
  gcongr

private theorem writeFrame (t : Fin 16 → List BSym) (s : Fin 17 → List BSym) :
    write ports t s = fun k ↦ if h : k.val < 16 then t ⟨k.val, h⟩ else s k := by
  funext k
  fin_cases k
  · simpa [ports] using (write_at ports t s 0)
  · simpa [ports] using (write_at ports t s 1)
  · simpa [ports] using (write_at ports t s 2)
  · simpa [ports] using (write_at ports t s 3)
  · simpa [ports] using (write_at ports t s 4)
  · simpa [ports] using (write_at ports t s 5)
  · simpa [ports] using (write_at ports t s 6)
  · simpa [ports] using (write_at ports t s 7)
  · simpa [ports] using (write_at ports t s 8)
  · simpa [ports] using (write_at ports t s 9)
  · simpa [ports] using (write_at ports t s 10)
  · simpa [ports] using (write_at ports t s 11)
  · simpa [ports] using (write_at ports t s 12)
  · simpa [ports] using (write_at ports t s 13)
  · simpa [ports] using (write_at ports t s 14)
  · simpa [ports] using (write_at ports t s 15)
  · simpa using (write_outside ports t s (l := 16) (by intro j; fin_cases j <;> decide))

/-- A single successful indexed iteration, retaining the exact comparison
    marker on the status stack and resetting all local scratch. -/
theorem iterationProg_matrix {n : ℕ} (m : Fin (n+1) → Fin (n+1) → BSym)
    (i : Fin (n+1)) (status count : List BSym) :
    ∃ marker c,
      c ≤ rowCostBound n i.val status.length + 2 ∧
      (marker = .one ↔ ∀ j, m i j = m j i) ∧
      iterationProg.Exec
        (store (matrixStream m) (List.replicate (n+1) .one)
          (List.replicate i.val .one) status (.one :: count))
        (store (matrixStream m) (List.replicate (n+1) .one)
          (List.replicate (i.val+1) .one) (marker :: status) count) c := by
  classical
  let data := matrixStream m
  let dim := List.replicate (n+1) BSym.one
  let idx := List.replicate i.val BSym.one
  let s := store data dim idx status (.one :: count)
  let base := TensorRowCheckIntegrated.store data dim idx [] [] [] [] [] [] [] [] [] [] [] [] status
  have hp : project ports s = base := by
    funext k; fin_cases k <;> simp [project, ports, s, store, base, TensorRowCheckIntegrated.store]
  obtain ⟨t, marker, c, hm, h0, h1, h2, h15, hscratch, he, hbound⟩ :=
    TensorRowCheckClean.rowCheckCleanProg_matrix m i status
  have hs3 : t 3 = [] := hscratch 3 (by decide)
  have hs4 : t 4 = [] := hscratch 4 (by decide)
  have hs5 : t 5 = [] := hscratch 5 (by decide)
  have hs6 : t 6 = [] := hscratch 6 (by decide)
  have hs7 : t 7 = [] := hscratch 7 (by decide)
  have hs8 : t 8 = [] := hscratch 8 (by decide)
  have hs9 : t 9 = [] := hscratch 9 (by decide)
  have hs10 : t 10 = [] := hscratch 10 (by decide)
  have hs11 : t 11 = [] := hscratch 11 (by decide)
  have hs12 : t 12 = [] := hscratch 12 (by decide)
  have hs13 : t 13 = [] := hscratch 13 (by decide)
  have hs14 : t 14 = [] := hscratch 14 (by decide)
  let u := store data dim idx (marker :: status) (.one :: count)
  have hu : write ports t s = u := by
    funext k
    fin_cases k <;> simp [writeFrame, s, u, store, h0, h1, h2, h15,
      hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, data, dim, idx]
  have hlift := lift_exec ports he s hp
  rw [hu] at hlift
  have ha : (StackProg.act nextAct).Exec u
      (store data dim (List.replicate (i.val+1) .one) (marker :: status) count) 1 := by
    have hh : StackProg.applyAct nextAct u =
        store data dim (List.replicate (i.val+1) .one) (marker :: status) count := by
      funext k; fin_cases k <;>
        simp [StackProg.applyAct, nextAct, StackAct.apply, u, store, idx, List.replicate_succ]
    simpa only [hh] using StackProg.Exec.act nextAct u
  have h := StackProg.Exec.seq hlift ha
  refine ⟨marker, c+2, ?_, hm, ?_⟩
  · change c ≤ rowCostBound n i.val status.length at hbound
    omega
  · simpa only [iterationProg, liftProgC_eq_liftProg ports decode decode_correct,
      s, data, dim, idx, Nat.add_assoc] using h

end TensorSymmetryIter

open CookPvsNP
namespace TensorCountedLoop

/-- A finite loop with a decreasing invariant and uniformly bounded body has
    an explicit overall bound. The invariant may also record accumulated data. -/
theorem countedLoop_exec {K A : Type} (test : (K → Option A) → Bool)
    (body : StackProg K A) (inv : ℕ → (K → List A) → Prop) (C : ℕ)
    (hstop : ∀ s, inv 0 s → test (fun k ↦ (s k).head?) = false)
    (hstep : ∀ k s, inv (k+1) s →
      test (fun j ↦ (s j).head?) = true ∧
      ∃ t c, c ≤ C ∧ body.Exec s t c ∧ inv k t)
    (n : ℕ) (s : K → List A) (hs : inv n s) :
    ∃ t steps, steps ≤ (C+2)*n+1 ∧ inv 0 t ∧
      (StackProg.loop test body).Exec s t steps := by
  induction n generalizing s with
  | zero => exact ⟨s, 1, by simp, hs, StackProg.Exec.loopFalse (hstop s hs)⟩
  | succ n ih =>
    obtain ⟨ht, u, c, hc, he, hu⟩ := hstep n s hs
    obtain ⟨t, d, hd, hf, hr⟩ := ih u hu
    refine ⟨t, 1+c+1+d, ?_, hf, StackProg.Exec.loopTrue ht he hr⟩
    simp only [Nat.mul_succ]
    omega

end TensorCountedLoop

open ProjSchedTW.Complexity

/-- Push one correct result marker onto an accumulator for rows below k. -/
theorem markers_prefix_step {v k : ℕ} (hk : k < v) (P : Fin v → Prop)
    (status : List BSym) (marker : BSym)
    (hold : (∀ b ∈ status, b = .one) ↔ ∀ i : Fin v, i.val < k → P i)
    (hmarker : marker = .one ↔ P ⟨k, hk⟩) :
    (∀ b ∈ marker :: status, b = .one) ↔ ∀ i : Fin v, i.val < k+1 → P i := by
  constructor
  · intro hall i hi
    by_cases h : i.val = k
    · have heq : i = ⟨k, hk⟩ := Fin.ext h
      subst i
      exact hmarker.mp (hall marker (by simp))
    · have hlt : i.val < k := by omega
      have hstatus : ∀ b ∈ status, b = .one := by
        intro b hb
        exact hall b (by simp [hb])
      exact (hold.mp hstatus) i hlt
  · intro hp b hb
    rcases List.mem_cons.mp hb with h | h
    · subst b
      exact hmarker.mpr (hp ⟨k, hk⟩ (by simp))
    · have hstatus : ∀ b ∈ status, b = .one := hold.mpr (by
        intro i hi
        apply hp i
        omega)
      exact hstatus b h

namespace TensorSymmetryLoop
open CookPvsNP ProjSchedTW.Complexity TensorSymmetryIter

/-- Iterate over every row of a nonempty square matrix, retaining one marker
    per row. The final markers are all one exactly for symmetric matrices. -/
theorem symmetryLoop_matrix {n : ℕ} (m : Fin (n+1) → Fin (n+1) → BSym) :
    ∃ markers steps,
      markers.length = n+1 ∧
      ((∀ b ∈ markers, b = .one) ↔ ∀ i j, m i j = m j i) ∧
      steps ≤ (rowCostBound n (n+1) (n+1)+4)*(n+1)+1 ∧
      symmetryLoop.Exec
        (store (matrixStream m) (List.replicate (n+1) .one) [] [] (List.replicate (n+1) .one))
        (store (matrixStream m) (List.replicate (n+1) .one) (List.replicate (n+1) .one) markers []) steps := by
  classical
  let P : Fin (n+1) → Prop := fun i ↦ ∀ j, m i j = m j i
  let inv : ℕ → (Fin 17 → List BSym) → Prop := fun remaining s ↦
    ∃ k status, k+remaining=n+1 ∧ status.length=k ∧
      ((∀ b ∈ status, b=.one) ↔ ∀ i : Fin (n+1), i.val<k → P i) ∧
      s = store (matrixStream m) (List.replicate (n+1) .one)
        (List.replicate k .one) status (List.replicate remaining .one)
  have hstop : ∀ s, inv 0 s → TensorSymmetryIter.more (fun k ↦ (s k).head?) = false := by
    intro s hs
    obtain ⟨k, status, hk, hlen, hp, rfl⟩ := hs
    simp [TensorSymmetryIter.more, TensorSymmetryIter.store]
  have hstep : ∀ r s, inv (r+1) s →
      TensorSymmetryIter.more (fun j ↦ (s j).head?) = true ∧
      ∃ t c, c ≤ rowCostBound n (n+1) (n+1)+2 ∧ iterationProg.Exec s t c ∧ inv r t := by
    intro r s hs
    obtain ⟨k, status, hk, hlen, hp, rfl⟩ := hs
    have hkv : k < n+1 := by omega
    let i : Fin (n+1) := ⟨k,hkv⟩
    constructor
    · simp [TensorSymmetryIter.more, TensorSymmetryIter.store, List.replicate_succ]
    · obtain ⟨marker, c, hc, hm, he⟩ :=
        iterationProg_matrix m i status (List.replicate r .one)
      have hi : i.val ≤ n+1 := by simp [i]; omega
      have hslen : status.length ≤ n+1 := by omega
      have hmono := rowCostBound_mono n hi hslen
      have hnew : (∀ b ∈ marker :: status, b=.one) ↔
          ∀ j : Fin (n+1), j.val<k+1 → P j := by
        exact markers_prefix_step hkv P status marker hp (by simpa [P, i] using hm)
      refine ⟨store (matrixStream m) (List.replicate (n+1) .one)
          (List.replicate (k+1) .one) (marker :: status) (List.replicate r .one), c, ?_, ?_, ?_⟩
      · omega
      · simpa [i, List.replicate_succ] using he
      · refine ⟨k+1, marker :: status, by omega, ?_, hnew, rfl⟩
        simp [hlen]
  let start := store (matrixStream m) (List.replicate (n+1) .one) [] [] (List.replicate (n+1) .one)
  have hstart : inv (n+1) start := by
    refine ⟨0, [], by omega, by simp, ?_, ?_⟩
    · simp
    · simp [start]
  obtain ⟨t, steps, hcost, hfinal, hrun⟩ := TensorCountedLoop.countedLoop_exec
    TensorSymmetryIter.more iterationProg inv (rowCostBound n (n+1) (n+1)+2) hstop hstep (n+1) start hstart
  obtain ⟨k, status, hk, hlen, hp, ht⟩ := hfinal
  have hk' : k=n+1 := by omega
  rw [hk'] at hlen hp ht
  refine ⟨status, steps, hlen, ?_, ?_, ?_⟩
  · constructor
    · intro hall i j
      exact (hp.mp hall i i.isLt) j
    · intro h
      apply hp.mpr
      intro i _ j
      exact h i j
  · simpa [Nat.add_assoc] using hcost
  · rw [ht] at hrun
    simpa [symmetryLoop, start] using hrun

/-- The empty matrix takes the zero-iteration branch and has no markers. -/
theorem symmetryLoop_empty (m : Fin 0 → Fin 0 → BSym) :
    symmetryLoop.Exec (store (matrixStream m) [] [] [] [])
      (store (matrixStream m) [] [] [] []) 1 := by
  apply StackProg.Exec.loopFalse
  simp [symmetryLoop, TensorSymmetryIter.more, TensorSymmetryIter.store]

end TensorSymmetryLoop

open CookPvsNP ProjSchedTW.Complexity
namespace TensorStackAllEqual

def store (input status : List BSym) : Fin 2 → List BSym := fun k ↦ if k=0 then input else status
private def isValue (b : BSym) (h : Fin 2 → Option BSym) : Bool := h 0 == some b
private def isEmpty (h : Fin 2 → Option BSym) : Bool := h 0 == none
private def popInput (_ : Fin 2 → Option BSym) (k : Fin 2) : StackAct BSym := if k=0 then .pop else .keep
private def mark (b : BSym) (_ : Fin 2 → Option BSym) (k : Fin 2) : StackAct BSym := if k=1 then .push b else .keep

def allEqualProg (b : BSym) : StackProg (Fin 2) BSym :=
  .seq (.loop (isValue b) (.act popInput))
    (.branch isEmpty (.act (mark .one)) (.act (mark .zero)))

private lemma pop_step (a : BSym) (tail status : List BSym) :
    StackProg.applyAct popInput (store (a :: tail) status) = store tail status := by
  funext k; fin_cases k <;> simp [StackProg.applyAct, popInput, store, StackAct.apply]
private lemma mark_step (b : BSym) (input status : List BSym) :
    StackProg.applyAct (mark b) (store input status) = store input (b :: status) := by
  funext k; fin_cases k <;> simp [StackProg.applyAct, mark, store, StackAct.apply]

private theorem valueLoop_spec (b : BSym) (input status : List BSym) :
    ∃ rest n, n ≤ input.length ∧ input = List.replicate n b ++ rest ∧
      (rest = [] ∨ rest.head? ≠ some b) ∧
      (StackProg.loop (isValue b) (.act popInput)).Exec (store input status) (store rest status) (3*n+1) := by
  induction input with
  | nil =>
    refine ⟨[], 0, by simp, by simp, Or.inl rfl, ?_⟩
    apply StackProg.Exec.loopFalse
    simp [isValue, store]
  | cons a tail ih =>
    by_cases hab : a = b
    · subst a
      obtain ⟨rest, n, hn, heq, hrest, hrun⟩ := ih
      have ht : isValue b (fun k ↦ (store (b :: tail) status k).head?) = true := by simp [isValue, store]
      have ha : (StackProg.act popInput).Exec (store (b :: tail) status) (store tail status) 1 := by
        simpa only [pop_step] using StackProg.Exec.act popInput (store (b :: tail) status)
      have he := StackProg.Exec.loopTrue ht ha hrun
      refine ⟨rest, n+1, ?_, ?_, hrest, ?_⟩
      · simp only [List.length_cons]; omega
      · simpa [List.replicate_succ] using congrArg (List.cons b) heq
      · simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he
    · refine ⟨a :: tail, 0, by simp, by simp, Or.inr (by simpa using hab), ?_⟩
      apply StackProg.Exec.loopFalse
      simp [isValue, store, hab]

/-- Any input halts in linear time, marking one exactly if every symbol equals b. -/
theorem allEqualProg_total (b : BSym) (input status : List BSym) :
    ∃ rest marker steps, steps ≤ 3*input.length+4 ∧
      (marker = .one ↔ ∀ a ∈ input, a = b) ∧
      (allEqualProg b).Exec (store input status) (store rest (marker :: status)) steps := by
  obtain ⟨rest, n, hn, heq, hrest, hrun⟩ := valueLoop_spec b input status
  cases rest with
  | nil =>
    have ha : (StackProg.act (mark .one)).Exec (store [] status) (store [] (.one :: status)) 1 := by
      simpa only [mark_step] using StackProg.Exec.act (mark .one) (store [] status)
    have hb := StackProg.Exec.branchTrue (test := isEmpty) (q := .act (mark .zero)) (by rfl) ha
    refine ⟨[], .one, 3*n+4, by omega, ?_, ?_⟩
    · constructor
      · intro _ a ha
        rw [heq] at ha
        simp only [List.append_nil, List.mem_replicate] at ha
        exact ha.2
      · intro _; rfl
    · have he := StackProg.Exec.seq hrun hb
      simpa [allEqualProg, Nat.add_assoc] using he
  | cons a rest =>
    have hne : a ≠ b := by
      rcases hrest with hnil | hhead
      · simp at hnil
      · simpa using hhead
    have ha : (StackProg.act (mark .zero)).Exec (store (a :: rest) status)
        (store (a :: rest) (.zero :: status)) 1 := by
      simpa only [mark_step] using StackProg.Exec.act (mark .zero) (store (a :: rest) status)
    have hb := StackProg.Exec.branchFalse (test := isEmpty) (p := .act (mark .one)) (by rfl) ha
    refine ⟨a :: rest, .zero, 3*n+4, by omega, ?_, ?_⟩
    · constructor
      · intro h; cases h
      · intro h
        have hm : a ∈ input := by rw [heq]; simp
        exact (hne (h a hm)).elim
    · have he := StackProg.Exec.seq hrun hb
      simpa [allEqualProg, Nat.add_assoc] using he

end TensorStackAllEqual

namespace TensorSymmetryDecision
open CookPvsNP ProjSchedTW.Complexity StackProgPortLift TensorSymmetryIter

private def loopPorts : Fin 17 ↪ Fin 18 := ⟨Fin.castSucc, Fin.castSucc_injective _⟩
private def loopDecode (k : Fin 18) : Option (Fin 17) :=
  if h : k.val < 17 then some ⟨k.val, h⟩ else none
private theorem loopDecode_correct (l : Fin 18) (k : Fin 17) :
    loopDecode l = some k ↔ loopPorts k = l := by fin_cases l <;> fin_cases k <;> decide
private def markerPorts : Fin 2 ↪ Fin 18 := ⟨![15,17], by decide⟩
private def markerDecode (k : Fin 18) : Option (Fin 2) :=
  if k=15 then some 0 else if k=17 then some 1 else none
private theorem markerDecode_correct (l : Fin 18) (k : Fin 2) :
    markerDecode l = some k ↔ markerPorts k = l := by fin_cases l <;> fin_cases k <;> decide

def frame (localState : Fin 17 → List BSym) : Fin 18 → List BSym :=
  fun k ↦ if h : k.val < 17 then localState ⟨k.val, h⟩ else []

/-- Test all rows and accept exactly when every row-comparison marker is one. -/
def symmetryDecisionProg : StackProg (Fin 18) BSym :=
  .seq (liftProgC loopPorts loopDecode symmetryLoop)
    (liftProgC markerPorts markerDecode (TensorStackAllEqual.allEqualProg .one))

/-- On every nonempty square matrix, compute a correct symmetry flag within
    an explicit polynomial bound, preserving the original matrix stack. -/
theorem symmetryDecision_matrix {n : ℕ} (m : Fin (n+1) → Fin (n+1) → BSym) :
    ∃ final marker steps,
      (marker = .one ↔ ∀ i j, m i j = m j i) ∧
      final 0 = matrixStream m ∧ final 1 = List.replicate (n+1) .one ∧ final 17 = [marker] ∧
      steps ≤ (rowCostBound n (n+1) (n+1)+4)*(n+1)+1+1+(3*(n+1)+4) ∧
      symmetryDecisionProg.Exec
        (frame (store (matrixStream m) (List.replicate (n+1) .one) [] []
          (List.replicate (n+1) .one))) final steps := by
  classical
  obtain ⟨markers, c, hlen, hm, hc, hloop⟩ := TensorSymmetryLoop.symmetryLoop_matrix m
  let localStart := store (matrixStream m) (List.replicate (n+1) .one) [] [] (List.replicate (n+1) .one)
  let localEnd := store (matrixStream m) (List.replicate (n+1) .one) (List.replicate (n+1) .one) markers []
  let s := frame localStart
  let t := write loopPorts localEnd s
  have hp : project loopPorts s = localStart := by
    funext k; simp [project, loopPorts, s, frame]
  have he := lift_exec loopPorts hloop s hp
  have ht15 : t 15 = markers := by
    simpa [t, loopPorts, localEnd, TensorSymmetryIter.store] using write_at loopPorts localEnd s 15
  have ht17 : t 17 = [] := by
    have hh : ∀ k : Fin 17, loopPorts k ≠ (17 : Fin 18) := by intro k; fin_cases k <;> decide
    simpa [t, s, frame] using write_outside loopPorts localEnd s hh
  have ht0 : t 0 = matrixStream m := by
    simpa [t, loopPorts, localEnd, TensorSymmetryIter.store] using write_at loopPorts localEnd s 0
  have ht1 : t 1 = List.replicate (n+1) .one := by
    simpa [t, loopPorts, localEnd, TensorSymmetryIter.store] using write_at loopPorts localEnd s 1
  have hq : project markerPorts t = TensorStackAllEqual.store markers [] := by
    funext k; fin_cases k <;> simp [project, markerPorts, TensorStackAllEqual.store, ht15, ht17]
  obtain ⟨rest, marker, d, hd, hmarker, hcheck⟩ :=
    TensorStackAllEqual.allEqualProg_total .one markers []
  let final := write markerPorts (TensorStackAllEqual.store rest [marker]) t
  have hf17 : final 17 = [marker] := by
    simpa [final, markerPorts, TensorStackAllEqual.store] using
      write_at markerPorts (TensorStackAllEqual.store rest [marker]) t 1
  have hf0 : final 0 = matrixStream m := by
    have hh : ∀ k : Fin 2, markerPorts k ≠ (0 : Fin 18) := by intro k; fin_cases k <;> decide
    rw [show final 0 = t 0 from write_outside markerPorts (TensorStackAllEqual.store rest [marker]) t hh]
    exact ht0
  have hf1 : final 1 = List.replicate (n+1) .one := by
    have hh : ∀ k : Fin 2, markerPorts k ≠ (1 : Fin 18) := by intro k; fin_cases k <;> decide
    rw [show final 1 = t 1 from write_outside markerPorts (TensorStackAllEqual.store rest [marker]) t hh]
    exact ht1
  have hf := lift_exec markerPorts hcheck t hq
  have hseq := StackProg.Exec.seq he hf
  refine ⟨final, marker, c+1+d, ?_, hf0, hf1, hf17, ?_, ?_⟩
  · exact hmarker.trans hm
  · rw [hlen] at hd
    omega
  · simpa only [symmetryDecisionProg, liftProgC_eq_liftProg loopPorts loopDecode loopDecode_correct,
      liftProgC_eq_liftProg markerPorts markerDecode markerDecode_correct, s, t, final, localStart, localEnd] using hseq

/-- The empty matrix is accepted without testing any rows. -/
theorem symmetryDecision_empty (m : Fin 0 → Fin 0 → BSym) :
    ∃ final steps, steps ≤ 6 ∧ final 0 = matrixStream m ∧ final 1 = [] ∧ final 17 = [.one] ∧
      symmetryDecisionProg.Exec (frame (store (matrixStream m) [] [] [] [])) final steps := by
  classical
  let localState := store (matrixStream m) [] [] [] []
  let s := frame localState
  let t := write loopPorts localState s
  have hp : project loopPorts s = localState := by
    funext k; simp [project, loopPorts, s, frame]
  have he := lift_exec loopPorts (TensorSymmetryLoop.symmetryLoop_empty m) s hp
  have ht15 : t 15 = [] := by
    simpa [t, loopPorts, localState, TensorSymmetryIter.store] using write_at loopPorts localState s 15
  have ht17 : t 17 = [] := by
    have hh : ∀ k : Fin 17, loopPorts k ≠ (17 : Fin 18) := by intro k; fin_cases k <;> decide
    simpa [t, s, frame] using write_outside loopPorts localState s hh
  have ht0 : t 0 = matrixStream m := by
    simpa [t, loopPorts, localState, TensorSymmetryIter.store] using write_at loopPorts localState s 0
  have ht1 : t 1 = [] := by
    simpa [t, loopPorts, localState, TensorSymmetryIter.store] using write_at loopPorts localState s 1
  have hq : project markerPorts t = TensorStackAllEqual.store [] [] := by
    funext k; fin_cases k <;> simp [project, markerPorts, TensorStackAllEqual.store, ht15, ht17]
  obtain ⟨rest, marker, d, hd, hmarker, hcheck⟩ :=
    TensorStackAllEqual.allEqualProg_total .one [] []
  have hm : marker = .one := hmarker.mpr (by simp)
  subst marker
  let final := write markerPorts (TensorStackAllEqual.store rest [.one]) t
  have hf17 : final 17 = [.one] := by
    simpa [final, markerPorts, TensorStackAllEqual.store] using
      write_at markerPorts (TensorStackAllEqual.store rest [.one]) t 1
  have hf0 : final 0 = matrixStream m := by
    have hh : ∀ k : Fin 2, markerPorts k ≠ (0 : Fin 18) := by intro k; fin_cases k <;> decide
    rw [show final 0 = t 0 from write_outside markerPorts (TensorStackAllEqual.store rest [.one]) t hh]
    exact ht0
  have hf1 : final 1 = [] := by
    have hh : ∀ k : Fin 2, markerPorts k ≠ (1 : Fin 18) := by intro k; fin_cases k <;> decide
    rw [show final 1 = t 1 from write_outside markerPorts (TensorStackAllEqual.store rest [.one]) t hh]
    exact ht1
  have hf := lift_exec markerPorts hcheck t hq
  have hseq := StackProg.Exec.seq he hf
  refine ⟨final, 1+1+d, ?_, hf0, hf1, hf17, ?_⟩
  · simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at hd
    omega
  · simpa only [symmetryDecisionProg, liftProgC_eq_liftProg loopPorts loopDecode loopDecode_correct,
      liftProgC_eq_liftProg markerPorts markerDecode markerDecode_correct, s, t, final, localState] using hseq

end TensorSymmetryDecision


namespace TensorSymmetryPrep

/-- Preserve an 11-stack front-end state and add 17 empty private ports. -/
def extend11 (s : Fin 11 → List BSym) : Fin 28 → List BSym :=
  fun k ↦ if h : k.val < 11 then s ⟨k.val, h⟩ else []

/-- Map the symmetry checker's data, dimension, index, scratch, markers,
    countdown and final flag onto the shared 28-stack store. -/
def symmetryPorts : Fin 18 ↪ Fin 28 :=
  ⟨![11,2,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27], by decide⟩

/-- Computable inverse for the shared 18-port embedding. -/
def symmetryInverse : Fin 28 → Option (Fin 18) := ![none, none, some 1, none, none, none, none, none, none, none, none, some 0, some 2, some 3, some 4, some 5, some 6, some 7, some 8, some 9, some 10, some 11, some 12, some 13, some 14, some 15, some 16, some 17]

theorem symmetryInverse_correct (l : Fin 28) (k : Fin 18) :
    symmetryInverse l = some k ↔ symmetryPorts k = l := by
  fin_cases l <;> fin_cases k <;> decide

def project18 (s : Fin 28 → List BSym) : Fin 18 → List BSym := fun k ↦ s (symmetryPorts k)

/-- Local symmetry-checker input: row-major bits, unary dimension, a unary
    countdown, and all other ports empty. -/
def prepared (bits : List BSym) (n : ℕ) : Fin 18 → List BSym :=
  fun k ↦ if k = 0 then bits.reverse else if k = 1 ∨ k = 16 then List.replicate n .one else []

/-- Copy the front end's reversed adjacency stream and reverse its copy, then
    copy the unary dimension into the symmetry checker's countdown stack. -/
def symmetryPrepProg : StackProg (Fin 28) BSym :=
  .seq (copyProg 1 12 13)
    (.seq (transferProg 12 (fun k ↦ decide (k = 11))) (copyProg 2 26 13))

/-- The actual preparation program preserves all original front-end ports,
    places the row-major stream and countdown in the exact checker layout, and
    runs in linear time in the stream and unary dimension. -/
theorem symmetryPrep_exec (s : Fin 11 → List BSym) (n : ℕ)
    (hdim : s 2 = List.replicate n .one) :
    ∃ out,
      symmetryPrepProg.Exec (extend11 s) out (9*(s 1).length+6*n+9) ∧
      (∀ k : Fin 11, out ⟨k.val, by omega⟩ = s k) ∧
      project18 out = prepared (s 1) n := by
  classical
  let b := extend11 s
  let c := Function.update b 12 (b 1 ++ b 12)
  let d := transferStore (12 : Fin 28) (fun k ↦ decide (k = 11)) c
  let e := Function.update d 26 (d 2 ++ d 26)
  have hs : b 13 = [] := by simp [b, extend11]
  have hc : (copyProg (1 : Fin 28) 12 13).Exec b c (6*(s 1).length+3) := by
    have h := stack_copy (1 : Fin 28) 12 13 (by decide) (by decide) (by decide) b hs
    simpa [b, c, extend11] using h
  have ht : (transferProg (12 : Fin 28) (fun k ↦ decide (k = 11))).Exec c d
      (3*(s 1).length+1) := by
    have h := stack_transfer (12 : Fin 28) (fun k ↦ decide (k = 11)) c
    simpa [d, c, b, extend11, Function.update] using h
  have hd13 : d 13 = [] := by simp [d, c, b, extend11, transferStore, Function.update]
  have hd2 : d 2 = List.replicate n .one := by
    simpa [d, c, b, extend11, transferStore, Function.update] using hdim
  have he : (copyProg (2 : Fin 28) 26 13).Exec d e (6*n+3) := by
    have h := stack_copy (2 : Fin 28) 26 13 (by decide) (by decide) (by decide) d hd13
    simpa [e, hd2] using h
  have hseq := StackProg.Exec.seq hc (StackProg.Exec.seq ht he)
  have htime : (6*(s 1).length+3)+1+((3*(s 1).length+1)+1+(6*n+3)) =
      9*(s 1).length+6*n+9 := by omega
  refine ⟨e, ?_, ?_, ?_⟩
  · rw [← htime]
    exact hseq
  · intro k
    fin_cases k <;> simp [e, d, c, b, extend11, transferStore, Function.update]
  · funext k
    fin_cases k <;> simp [project18, prepared, symmetryPorts, e, d, c, b, extend11,
      transferStore, Function.update, hdim]

end TensorSymmetryPrep


namespace TensorSymmetryBridge

def bitSym (b : Bool) : BSym := if b then .one else .zero

def matrixStream {v : ℕ} (m : Fin v → Fin v → BSym) : List BSym :=
  List.ofFn (fun k : Fin (v*v) ↦ m (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)

/-- Reconstructing a Boolean matrix and flattening its symbols yields the
    exact original row-major symbol stream, including at dimension zero. -/
theorem matrixStream_matrixOfBits {v : ℕ} (bits : List Bool) (h : bits.length = v*v) :
    matrixStream (fun i j ↦ bitSym (matrixOfBits bits h i j)) = bits.map bitSym := by
  have hfn : (List.ofFn fun k : Fin (v*v) ↦ bits.get (Fin.cast h.symm k)) = bits := by
    apply List.ext_getElem
    · simp [h]
    · intro i h1 h2
      simp [List.get_ofFn]
  calc
    _ = (List.ofFn (fun k : Fin (v*v) ↦ bits.get (Fin.cast h.symm k))).map bitSym := by
      simp only [matrixStream, List.map_ofFn]
      apply congrArg List.ofFn
      funext k
      simp [matrixOfBits, Nat.mod_add_div]
    _ = _ := by rw [hfn]

/-- Symbol equality is equivalent to equality of the represented Boolean bits. -/
theorem bitSym_injective : Function.Injective bitSym := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitSym]

end TensorSymmetryBridge


namespace TensorGraphSymmetry

open StackProgPortLift TensorPrefixDecode TensorDiagonalFront TensorGraphDiagonal TensorSymmetryPrep

def diagonalPorts : Fin 11 ↪ Fin 28 := ⟨![0,1,2,3,4,5,6,7,8,9,10], by decide⟩
def diagonalInverse : Fin 28 → Option (Fin 11) :=
  ![some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,
    none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
private theorem diagonalInverse_correct (l : Fin 28) (k : Fin 11) :
    diagonalInverse l = some k ↔ diagonalPorts k = l := by fin_cases l <;> fin_cases k <;> decide

private def frontGood (h : Fin 28 → Option BSym) : Bool := h 6 == some BSym.one
private def symmetryGood (h : Fin 28 → Option BSym) : Bool := h 27 == some BSym.one
private def keepAct (_h : Fin 28 → Option BSym) (_k : Fin 28) : StackAct BSym := .keep
private def rejectAct (_h : Fin 28 → Option BSym) (k : Fin 28) : StackAct BSym :=
  if k = 6 then .push .zero else .keep
private def rejectStore (s : Fin 28 → List BSym) : Fin 28 → List BSym :=
  Function.update s 6 (.zero :: s 6)

/-- Execute the canonical/diagonal frontend, then prepare and run symmetry;
    errors at either stage are propagated on the shared status stack. -/
def graphSymmetryProg : StackProg (Fin 28) BSym :=
  .seq (liftProgC diagonalPorts diagonalInverse graphDiagonalProg)
    (.branch frontGood
      (.seq symmetryPrepProg
        (.seq (liftProgC symmetryPorts symmetryInverse TensorSymmetryDecision.symmetryDecisionProg)
          (.branch symmetryGood (.act keepAct) (.act rejectAct))))
      (.act keepAct))

private theorem project_diagonal (s : Fin 11 → List BSym) : project diagonalPorts (extend11 s) = s := by
  funext k
  fin_cases k <;> simp [project, diagonalPorts, extend11]

private theorem write_diagonal (s t : Fin 11 → List BSym) : write diagonalPorts t (extend11 s) = extend11 t := by
  funext k
  fin_cases k
  · simpa [diagonalPorts, extend11] using
      (StackProgPortLift.write_at diagonalPorts t (extend11 s) (0 : Fin 11))
  · simpa [diagonalPorts, extend11] using
      (StackProgPortLift.write_at diagonalPorts t (extend11 s) (1 : Fin 11))
  · simpa [diagonalPorts, extend11] using
      (StackProgPortLift.write_at diagonalPorts t (extend11 s) (2 : Fin 11))
  · simpa [diagonalPorts, extend11] using
      (StackProgPortLift.write_at diagonalPorts t (extend11 s) (3 : Fin 11))
  · simpa [diagonalPorts, extend11] using
      (StackProgPortLift.write_at diagonalPorts t (extend11 s) (4 : Fin 11))
  · simpa [diagonalPorts, extend11] using
      (StackProgPortLift.write_at diagonalPorts t (extend11 s) (5 : Fin 11))
  · simpa [diagonalPorts, extend11] using
      (StackProgPortLift.write_at diagonalPorts t (extend11 s) (6 : Fin 11))
  · simpa [diagonalPorts, extend11] using
      (StackProgPortLift.write_at diagonalPorts t (extend11 s) (7 : Fin 11))
  · simpa [diagonalPorts, extend11] using
      (StackProgPortLift.write_at diagonalPorts t (extend11 s) (8 : Fin 11))
  · simpa [diagonalPorts, extend11] using
      (StackProgPortLift.write_at diagonalPorts t (extend11 s) (9 : Fin 11))
  · simpa [diagonalPorts, extend11] using
      (StackProgPortLift.write_at diagonalPorts t (extend11 s) (10 : Fin 11))
  · have ho : ∀ j : Fin 11, diagonalPorts j ≠ (11 : Fin 28) := by
      intro j; fin_cases j <;> decide
    simpa [extend11] using (StackProgPortLift.write_outside diagonalPorts t (extend11 s) ho)
  · have ho : ∀ j : Fin 11, diagonalPorts j ≠ (12 : Fin 28) := by
      intro j; fin_cases j <;> decide
    simpa [extend11] using (StackProgPortLift.write_outside diagonalPorts t (extend11 s) ho)
  · have ho : ∀ j : Fin 11, diagonalPorts j ≠ (13 : Fin 28) := by
      intro j; fin_cases j <;> decide
    simpa [extend11] using (StackProgPortLift.write_outside diagonalPorts t (extend11 s) ho)
  · have ho : ∀ j : Fin 11, diagonalPorts j ≠ (14 : Fin 28) := by
      intro j; fin_cases j <;> decide
    simpa [extend11] using (StackProgPortLift.write_outside diagonalPorts t (extend11 s) ho)
  · have ho : ∀ j : Fin 11, diagonalPorts j ≠ (15 : Fin 28) := by
      intro j; fin_cases j <;> decide
    simpa [extend11] using (StackProgPortLift.write_outside diagonalPorts t (extend11 s) ho)
  · have ho : ∀ j : Fin 11, diagonalPorts j ≠ (16 : Fin 28) := by
      intro j; fin_cases j <;> decide
    simpa [extend11] using (StackProgPortLift.write_outside diagonalPorts t (extend11 s) ho)
  · have ho : ∀ j : Fin 11, diagonalPorts j ≠ (17 : Fin 28) := by
      intro j; fin_cases j <;> decide
    simpa [extend11] using (StackProgPortLift.write_outside diagonalPorts t (extend11 s) ho)
  · have ho : ∀ j : Fin 11, diagonalPorts j ≠ (18 : Fin 28) := by
      intro j; fin_cases j <;> decide
    simpa [extend11] using (StackProgPortLift.write_outside diagonalPorts t (extend11 s) ho)
  · have ho : ∀ j : Fin 11, diagonalPorts j ≠ (19 : Fin 28) := by
      intro j; fin_cases j <;> decide
    simpa [extend11] using (StackProgPortLift.write_outside diagonalPorts t (extend11 s) ho)
  · have ho : ∀ j : Fin 11, diagonalPorts j ≠ (20 : Fin 28) := by
      intro j; fin_cases j <;> decide
    simpa [extend11] using (StackProgPortLift.write_outside diagonalPorts t (extend11 s) ho)
  · have ho : ∀ j : Fin 11, diagonalPorts j ≠ (21 : Fin 28) := by
      intro j; fin_cases j <;> decide
    simpa [extend11] using (StackProgPortLift.write_outside diagonalPorts t (extend11 s) ho)
  · have ho : ∀ j : Fin 11, diagonalPorts j ≠ (22 : Fin 28) := by
      intro j; fin_cases j <;> decide
    simpa [extend11] using (StackProgPortLift.write_outside diagonalPorts t (extend11 s) ho)
  · have ho : ∀ j : Fin 11, diagonalPorts j ≠ (23 : Fin 28) := by
      intro j; fin_cases j <;> decide
    simpa [extend11] using (StackProgPortLift.write_outside diagonalPorts t (extend11 s) ho)
  · have ho : ∀ j : Fin 11, diagonalPorts j ≠ (24 : Fin 28) := by
      intro j; fin_cases j <;> decide
    simpa [extend11] using (StackProgPortLift.write_outside diagonalPorts t (extend11 s) ho)
  · have ho : ∀ j : Fin 11, diagonalPorts j ≠ (25 : Fin 28) := by
      intro j; fin_cases j <;> decide
    simpa [extend11] using (StackProgPortLift.write_outside diagonalPorts t (extend11 s) ho)
  · have ho : ∀ j : Fin 11, diagonalPorts j ≠ (26 : Fin 28) := by
      intro j; fin_cases j <;> decide
    simpa [extend11] using (StackProgPortLift.write_outside diagonalPorts t (extend11 s) ho)
  · have ho : ∀ j : Fin 11, diagonalPorts j ≠ (27 : Fin 28) := by
      intro j; fin_cases j <;> decide
    simpa [extend11] using (StackProgPortLift.write_outside diagonalPorts t (extend11 s) ho)

private theorem keep_exec (s : Fin 28 → List BSym) : (StackProg.act keepAct).Exec s s 1 := by
  have heq : StackProg.applyAct keepAct s = s := by
    funext k
    simp [StackProg.applyAct, keepAct, StackAct.apply]
  simpa only [heq] using StackProg.Exec.act keepAct s

private theorem reject_exec (s : Fin 28 → List BSym) :
    (StackProg.act rejectAct).Exec s (rejectStore s) 1 := by
  have heq : StackProg.applyAct rejectAct s = rejectStore s := by
    funext k
    fin_cases k <;> simp [StackProg.applyAct, rejectAct, rejectStore, StackAct.apply, Function.update]
  simpa only [heq] using StackProg.Exec.act rejectAct s

end TensorGraphSymmetry


/-- Arithmetic copy of the checked row-cost expression. -/
def symmetryRowCost (n i statusLength : ℕ) : ℕ :=
  let C := (((6*i+3)+1+((6*(n+1)+7)*i+1))+1+((6*i+3)+1+
    ((6*((n+1)*(n+1))+3)+1+((6*((n+1)*(n+1))+3)+1+
      ((3*(i*(n+1))+1)+1+(3*i+1)))))) + 1 +
    (((6*(n+1)+3)+1+((6*(n+1)+3)+1+(6*(n+1)+3)))+1+1) + 1 +
    ((9*n+21)*(n+1)+8)
  C+1+12*(3*((n+1)*(n+1)+(n+1)+i+statusLength+C)+2)+1

/-- The complete symmetry stage has cubic cost in the matrix dimension. -/
theorem symmetryCost_cubic (n : ℕ) :
    (symmetryRowCost n (n+1) (n+1)+4)*(n+1)+1+1+(3*(n+1)+4) ≤
      20000*(n+1)^3 := by
  unfold symmetryRowCost
  nlinarith [Nat.zero_le (n*n), Nat.zero_le (n*n*n)]

namespace TensorGraphSymmetry

open TensorSymmetryDecision TensorSymmetryIter TensorSymmetryPrep

/-- The checked symmetry decision in one interface valid at every dimension,
    with a uniform cubic runtime and preservation of matrix and dimension. -/
theorem symmetryDecision_uniform (n : ℕ) (m : Fin n → Fin n → BSym) :
    ∃ final marker steps,
      (marker = .one ↔ ∀ i j, m i j = m j i) ∧
      final 0 = matrixStream m ∧ final 1 = List.replicate n .one ∧ final 17 = [marker] ∧
      steps ≤ 20000*(n+1)^3 ∧
      symmetryDecisionProg.Exec (prepared (matrixStream m).reverse n) final steps := by
  cases n with
  | zero =>
    obtain ⟨final, steps, hbound, hdata, hdim, hmark, hrun⟩ := symmetryDecision_empty m
    refine ⟨final, .one, steps, ?_, hdata, ?_, hmark, ?_, ?_⟩
    · simp
    · simpa using hdim
    · norm_num at hbound ⊢
      omega
    · have hinit : prepared (matrixStream m).reverse 0 =
          frame (store (matrixStream m) [] [] [] []) := by
        funext k
        fin_cases k <;> simp [prepared, frame, store]
      simpa only [hinit] using hrun
  | succ n =>
    obtain ⟨final, marker, steps, hmark, hdata, hdim, hflag, hbound, hrun⟩ := symmetryDecision_matrix m
    refine ⟨final, marker, steps, hmark, hdata, hdim, hflag, ?_, ?_⟩
    · have hc := symmetryCost_cubic n
      change (rowCostBound n (n+1) (n+1)+4)*(n+1)+1+1+(3*(n+1)+4) ≤
        20000*(n+1)^3 at hc
      have hlarge : 20000*(n+1)^3 ≤ 20000*((n+1)+1)^3 := by gcongr <;> omega
      exact le_trans hbound (le_trans hc hlarge)
    · have hinit : prepared (matrixStream m).reverse (n+1) =
          frame (store (matrixStream m) (List.replicate (n+1) .one) [] [] (List.replicate (n+1) .one)) := by
        funext k
        fin_cases k <;> simp [prepared, frame, store]
      simpa only [hinit] using hrun

end TensorGraphSymmetry

/-- A well-sized bit stream whose reconstructed matrix is symmetric and has
    zero diagonal is exactly the canonical code of a simple graph. -/
theorem canonical_bool_matrix_is_graph {v : ℕ} (bits : List Bool) (h : bits.length = v*v)
    (hsym : ∀ i j, matrixOfBits bits h i j = matrixOfBits bits h j i)
    (hdiag : ∀ i, matrixOfBits bits h i i = false) :
    TensorNP.Eigen.graphCode (graphOfMatrix (matrixOfBits bits h) hsym hdiag) =
      encNat v ++ encNats (bits.map (fun b ↦ if b then 1 else 0)) := by
  have hmap :
      (List.ofFn fun i : Fin v ↦ List.ofFn fun j : Fin v ↦
        if matrixOfBits bits h i j then (1 : ℕ) else 0).flatten =
      bits.map (fun b ↦ if b then 1 else 0) := by
    calc
      _ = ((List.ofFn fun i : Fin v ↦ List.ofFn fun j : Fin v ↦
          matrixOfBits bits h i j).flatten).map (fun b ↦ if b then 1 else 0) := by
            simp [List.map_flatten, List.map_ofFn, Function.comp_def]
      _ = _ := by rw [matrixOfBits_flatten]
  rw [graphOfMatrix_code]
  unfold matrixCode
  rw [hmap]
  rfl


namespace TensorGraphSymmetry

open StackProgPortLift TensorPrefixDecode TensorDiagonalFront TensorGraphDiagonal
  TensorSymmetryDecision TensorSymmetryIter TensorSymmetryPrep TensorSymmetryBridge

/-- The composed executable recognizes only canonical simple-graph codes,
    propagates rejection from all stages, and halts on all inputs in an
    explicit cubic bound. It includes the zero-vertex case. -/
theorem graphSymmetry_total_sound (input status : List BSym) :
    ∃ out steps,
      graphSymmetryProg.Exec (extend11 (extend7 (store7 input [] [] [] [] [] status))) out steps ∧
      steps ≤ 20000*(input.length+1)^3 + 47*(input.length*input.length) + 64*input.length + 62 ∧
      ((∃ (n : ℕ) (G : SimpleGraph (Fin n)), input = TensorNP.Eigen.graphCode G ∧
          out 2 = List.replicate n .one ∧ (out 6).head? = some .one) ∨
       (out 6).head? ≠ some .one) := by
  obtain ⟨front, psteps, hp, hpbound, hclass⟩ := TensorGraphDiagonal.graphDiagonal_total input status
  let initial := extend7 (store7 input [] [] [] [] [] status)
  have hfront := lift_exec diagonalPorts hp (extend11 initial) (project_diagonal initial)
  rw [write_diagonal] at hfront
  rw [← liftProgC_eq_liftProg diagonalPorts diagonalInverse diagonalInverse_correct graphDiagonalProg] at hfront
  rcases hclass with ⟨n, bs, hlen, horig, hnm, hdiag, hbits, hvalue, hstatus⟩ | hbad
  · have hgood : frontGood (fun k ↦ (extend11 front k).head?) = true := by
      simpa [frontGood, extend11] using hstatus
    obtain ⟨prep, hprep, hpreserve, hprepared⟩ := symmetryPrep_exec front n hvalue
    let mat : Fin n → Fin n → BSym := fun i j ↦ TensorSymmetryBridge.bitSym (matrixOfBits bs hlen i j)
    have hsym : TensorAdjacencyScan.bitSym = TensorSymmetryBridge.bitSym := by
      funext b; cases b <;> rfl
    have hstream : _root_.TensorGraphRecognizerInternal.matrixStream mat = (front 1).reverse := by
      have h := TensorSymmetryBridge.matrixStream_matrixOfBits bs hlen
      change _root_.TensorGraphRecognizerInternal.matrixStream mat = bs.map TensorSymmetryBridge.bitSym at h
      rw [hbits, List.reverse_reverse, hsym]
      exact h
    obtain ⟨localOut, marker, symSteps, hmarker, hdata, hdim, hflag, hsymBound, hsymRun⟩ :=
      symmetryDecision_uniform n mat
    have hproject : project symmetryPorts prep = prepared (_root_.TensorGraphRecognizerInternal.matrixStream mat).reverse n := by
      change project18 prep = _
      rw [hprepared, hstream, List.reverse_reverse]
    have hlift := lift_exec symmetryPorts hsymRun prep hproject
    rw [← liftProgC_eq_liftProg symmetryPorts symmetryInverse symmetryInverse_correct
      TensorSymmetryDecision.symmetryDecisionProg] at hlift
    let symOut := write symmetryPorts localOut prep
    have hstatusPrep : prep 6 = front 6 := by simpa using hpreserve (6 : Fin 11)
    have hstatusOut : symOut 6 = front 6 := by
      have ho : ∀ k : Fin 18, symmetryPorts k ≠ (6 : Fin 28) := by
        intro k; fin_cases k <;> decide
      rw [show symOut 6 = prep 6 from write_outside symmetryPorts localOut prep ho]
      exact hstatusPrep
    have hdimOut : symOut 2 = List.replicate n .one := by
      change write symmetryPorts localOut prep (symmetryPorts 1) = _
      rw [write_at]
      exact hdim
    have hflagOut : symOut 27 = [marker] := by
      change write symmetryPorts localOut prep (symmetryPorts 17) = _
      rw [write_at]
      exact hflag
    have hsized : (front 1).length = n*n := by
      rw [hbits]
      simpa using hlen
    have hquad : n*n ≤ input.length*input.length := Nat.mul_le_mul hnm hnm
    have hcube : (n+1)^3 ≤ (input.length+1)^3 := by gcongr
    have hsymLarge : symSteps ≤ 20000*(input.length+1)^3 :=
      le_trans hsymBound (Nat.mul_le_mul_left 20000 hcube)
    by_cases hm : marker = .one
    · have hsymbool : ∀ i j, matrixOfBits bs hlen i j = matrixOfBits bs hlen j i := by
        intro i j
        apply TensorSymmetryBridge.bitSym_injective
        exact (hmarker.mp hm) i j
      let G := graphOfMatrix (matrixOfBits bs hlen) hsymbool hdiag
      have hcode : TensorNP.Eigen.graphCode G =
          encNat n ++ encNats (bs.map (fun b ↦ if b then 1 else 0)) :=
        canonical_bool_matrix_is_graph bs hlen hsymbool hdiag
      have hinput : input = TensorNP.Eigen.graphCode G := by
        calc
          input = encNat n ++ TensorAdjacencyScan.bitBlocks bs := horig
          _ = encNat n ++ encNats (bs.map (fun b ↦ if b then 1 else 0)) := by
            rw [TensorAdjacencyScan.bitBlocks_eq_encNats]
          _ = TensorNP.Eigen.graphCode G := hcode.symm
      have hpost : symmetryGood (fun k ↦ (symOut k).head?) = true := by
        simp [symmetryGood, hflagOut, hm]
      have hfinish := StackProg.Exec.branchTrue (q := .act rejectAct) hpost (keep_exec symOut)
      have hsymSeq := StackProg.Exec.seq hlift hfinish
      have hbody := StackProg.Exec.seq hprep hsymSeq
      have hbranch := StackProg.Exec.branchTrue (q := .act keepAct) hgood hbody
      have he := StackProg.Exec.seq hfront hbranch
      refine ⟨symOut, psteps+1+(1+((9*(front 1).length+6*n+9)+1+(symSteps+1+2))),
        he, ?_, Or.inl ⟨n, G, hinput, hdimOut, ?_⟩⟩
      · rw [hsized]
        nlinarith
      · simpa [hstatusOut] using hstatus
    · have hpost : symmetryGood (fun k ↦ (symOut k).head?) = false := by
        simp [symmetryGood, hflagOut, hm]
      have hfinish := StackProg.Exec.branchFalse (p := .act keepAct) hpost (reject_exec symOut)
      have hsymSeq := StackProg.Exec.seq hlift hfinish
      have hbody := StackProg.Exec.seq hprep hsymSeq
      have hbranch := StackProg.Exec.branchTrue (q := .act keepAct) hgood hbody
      have he := StackProg.Exec.seq hfront hbranch
      refine ⟨rejectStore symOut, psteps+1+(1+((9*(front 1).length+6*n+9)+1+(symSteps+1+2))),
        he, ?_, Or.inr ?_⟩
      · rw [hsized]
        nlinarith
      · simp [rejectStore, Function.update]
  · have hbad' : frontGood (fun k ↦ (extend11 front k).head?) = false := by
      simp [frontGood, extend11, hbad]
    have hbranch := StackProg.Exec.branchFalse
      (p := .seq symmetryPrepProg
        (.seq (liftProgC symmetryPorts symmetryInverse TensorSymmetryDecision.symmetryDecisionProg)
          (.branch symmetryGood (.act keepAct) (.act rejectAct))))
      hbad' (keep_exec (extend11 front))
    have he := StackProg.Exec.seq hfront hbranch
    refine ⟨extend11 front, psteps+1+2, he, ?_, Or.inr ?_⟩
    · nlinarith [Nat.zero_le (20000*(input.length+1)^3), Nat.zero_le (input.length*input.length)]
    · simpa [extend11] using hbad

end TensorGraphSymmetry

theorem tensor_encNats_length_ge (xs : List ℕ) : xs.length ≤ (encNats xs).length := by
  induction xs with
  | nil => simp [encNats]
  | cons a xs ih =>
    have ha : 1 ≤ (encNat a).length := by simp [encNat]
    simp only [encNats, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    omega

/-- The canonical graph input has at least one symbol per adjacency-matrix
    entry, plus the encoded vertex count. This rules out an exponential output
    size hidden behind a small binary vertex count. -/
theorem tensor_graphCode_length_lower {v : ℕ} (G : SimpleGraph (Fin v)) :
    1 + v * v ≤ (TensorNP.Eigen.graphCode G).length := by
  classical
  have h := tensor_encNats_length_ge
    ([v] ++ (List.ofFn fun i : Fin v ↦ List.ofFn fun j : Fin v ↦
      if G.Adj i j then 1 else 0).flatten)
  simp only [List.length_append, List.length_singleton, List.length_flatten, List.map_ofFn,
    Function.comp_def, List.length_ofFn, List.ofFn_const, List.sum_replicate_nat] at h
  change 1 + v * v ≤ (encNats _).length
  omega

namespace TensorAdjacencyScan

/-- Row-major adjacency bits of a finite graph. -/
def graphBits {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj] : List Bool :=
  (List.ofFn fun i : Fin v ↦ List.ofFn fun j : Fin v ↦ decide (G.Adj i j)).flatten

/-- Graph codes contain the vertex-count block followed by the row-major bit blocks. -/
theorem graphCode_eq_bitBlocks {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj] :
    TensorNP.Eigen.graphCode G = encNat v ++ bitBlocks (graphBits G) := by
  simp [TensorNP.Eigen.graphCode, graphBits, bitBlocks_eq_encNats, encNats,
    List.map_flatten, List.map_ofFn, Function.comp_def]
  apply congrArg (List.flatMap encNat)
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  by_cases h : G.Adj i j <;> simp [h]

/-- The row-major adjacency-bit stream has exactly v² entries. -/
theorem graphBits_length {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj] :
    (graphBits G).length = v * v := by
  simp [graphBits, List.length_flatten, List.map_ofFn, Function.comp_def, List.ofFn_const]


end TensorAdjacencyScan

namespace TensorPrefixDecode

open StackProgPortLift TensorSquareScan TensorAdjacencyScan

/-- Every actual graph code follows the successful path of the combined
    executable; it leaves the graph dimension unary, the row-major adjacency
    bits on the bit stack, exhausted input, and a success marker. -/
theorem cappedGraphScan_graphCode {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (status : List BSym) :
    ∃ out steps,
      cappedGraphScanProg.Exec (store7 (TensorNP.Eigen.graphCode G) [] [] [] [] [] status) out steps ∧
      out 0 = [] ∧ out 1 = ((graphBits G).map bitSym).reverse ∧
      out 2 = List.replicate v .one ∧
      out 6 = .one :: .one :: .one :: status ∧
      out 4 = List.replicate ((TensorNP.Eigen.graphCode G).length-v) .one := by
  let inp := TensorNP.Eigen.graphCode G
  let data := bitBlocks (graphBits G)
  let fuel := inp.length-v
  have hcode : inp = encNat v ++ data := graphCode_eq_bitBlocks G
  have hle : v ≤ inp.length := by
    have h := tensor_graphCode_length_lower G
    have hs : v ≤ v*v := Nat.le_mul_self v
    change 1 + v*v ≤ inp.length at h
    omega
  have hcap : v ≤ (encNat v ++ data).length := by rw [← hcode]; exact hle
  obtain ⟨ps, hp, hpb⟩ := cappedPrefix_encNat v data status hcap
  have hp' : cappedPrefixProg.Exec (store7 inp [] [] [] [] [] status)
      (store7 data [] (List.replicate v .one) [] (List.replicate fuel .one) [] (.one :: .one :: status)) ps := by
    simpa only [← hcode, fuel] using hp
  obtain ⟨gs, hgb, hg⟩ := squareScan_success v (graphBits G) (.one :: status) (graphBits_length G)
  let s0 := TensorSquareScan.store6 data (List.replicate v .one) [] [] [] (.one :: .one :: status)
  let sg := write TensorSquareScan.scanPorts
    (TensorAdjacencyScan.store [] [] (((graphBits G).map bitSym).reverse) (.one :: .one :: .one :: status))
    (write TensorSquareScan.squarePorts
      (TensorUnarySquare.store4 (List.replicate v .one) (List.replicate (v*v) .one) [] []) s0)
  let base := store7 data [] (List.replicate v .one) [] (List.replicate fuel .one) [] (.one :: .one :: status)
  have hproj : project graphPorts base = s0 := by
    funext k
    fin_cases k <;> simp [project, graphPorts, base, s0, store7, TensorSquareScan.store6]
  have hgs : squareScanProg.Exec s0 sg (((6*v+3)+1+((6*v+7)*v+1))+1+gs) := by
    simpa only [s0, sg, data] using hg
  have hlift := lift_exec graphPorts hgs base hproj
  rw [← liftProgC_eq_liftProg graphPorts graphInverse graphInverse_correct squareScanProg] at hlift
  have ht : accepted (fun k ↦ (base k).head?) = true := by simp [accepted, base, store7]
  have hb := StackProg.Exec.branchTrue (q := .act keepAct) ht hlift
  have he := StackProg.Exec.seq hp' hb
  let out := write graphPorts sg base
  have hin : out 0 = [] := by
    change write graphPorts sg base (graphPorts 0) = []
    rw [StackProgPortLift.write_at]
    change write TensorSquareScan.scanPorts _ _ (TensorSquareScan.scanPorts 0) = []
    rw [StackProgPortLift.write_at]
    simp [TensorAdjacencyScan.store]
  have hbits : out 1 = ((graphBits G).map bitSym).reverse := by
    change write graphPorts sg base (graphPorts 3) = _
    rw [StackProgPortLift.write_at]
    change write TensorSquareScan.scanPorts _ _ (TensorSquareScan.scanPorts 2) = _
    rw [StackProgPortLift.write_at]
    simp [TensorAdjacencyScan.store]
  have hstatus : out 6 = .one :: .one :: .one :: status := by
    change write graphPorts sg base (graphPorts 5) = _
    rw [StackProgPortLift.write_at]
    change write TensorSquareScan.scanPorts _ _ (TensorSquareScan.scanPorts 3) = _
    rw [StackProgPortLift.write_at]
    simp [TensorAdjacencyScan.store]
  have hvalue : out 2 = List.replicate v .one := by
    change write graphPorts sg base (graphPorts 1) = _
    rw [StackProgPortLift.write_at]
    have ho : ∀ k : Fin 4, TensorSquareScan.scanPorts k ≠ (1 : Fin 6) := by
      intro k; fin_cases k <;> decide
    dsimp only [sg]
    rw [StackProgPortLift.write_outside TensorSquareScan.scanPorts _ _ ho]
    change write TensorSquareScan.squarePorts _ _ (TensorSquareScan.squarePorts 0) = _
    rw [StackProgPortLift.write_at]
    simp [TensorUnarySquare.store4]
  have hfuel : out 4 = List.replicate (inp.length-v) .one := by
    have ho : ∀ k : Fin 6, graphPorts k ≠ (4 : Fin 7) := by
      intro k; fin_cases k <;> decide
    simpa [out, base, store7, fuel] using StackProgPortLift.write_outside graphPorts sg base ho
  refine ⟨out, ps+1+(1+(((6*v+3)+1+((6*v+7)*v+1))+1+gs)), ?_, hin, hbits, hvalue, hstatus, ?_⟩
  · exact he
  · exact hfuel

end TensorPrefixDecode


theorem tensor_matrix_flatten_injective {α : Type} {r c : ℕ}
    (f g : Fin r → Fin c → α)
    (h : (List.ofFn fun i ↦ List.ofFn (f i)).flatten =
      (List.ofFn fun i ↦ List.ofFn (g i)).flatten) : f = g := by
  induction r with
  | zero =>
    funext i
    exact Fin.elim0 i
  | succ r ih =>
    have h' : List.ofFn (f 0) ++ (List.ofFn fun i : Fin r ↦ List.ofFn (f i.succ)).flatten =
        List.ofFn (g 0) ++ (List.ofFn fun i : Fin r ↦ List.ofFn (g i.succ)).flatten := by
      simpa [List.ofFn_succ] using h
    have hrow : f 0 = g 0 := List.ofFn_injective (List.append_inj_left h' (by simp))
    have htail := List.append_inj_right h' (by simp)
    have hs : (fun i : Fin r ↦ f i.succ) = (fun i : Fin r ↦ g i.succ) := ih _ _ htail
    funext i
    refine Fin.cases ?_ ?_ i
    · exact hrow
    · intro j
      exact congrFun hs j



namespace TensorGraphDiagonal

open StackProgPortLift TensorPrefixDecode TensorDiagonalFront TensorAdjacencyScan

private theorem graph_matrix_diagonal {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (i : Fin v) : matrixOfBits (graphBits G) (graphBits_length G) i i = false := by
  have hmat : matrixOfBits (graphBits G) (graphBits_length G) =
      (fun i j ↦ decide (G.Adj i j)) := by
    apply tensor_matrix_flatten_injective
    simpa [graphBits] using matrixOfBits_flatten (graphBits G) (graphBits_length G)
  rw [hmat]
  simp

/-- Every genuine graph follows the successful diagonal-validation path,
    including the empty graph, with the same all-input quadratic time bound. -/
theorem graphDiagonal_graphCode {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (status : List BSym) :
    ∃ out steps,
      graphDiagonalProg.Exec (extend7 (store7 (TensorNP.Eigen.graphCode G) [] [] [] [] [] status)) out steps ∧
      steps ≤ 38*((TensorNP.Eigen.graphCode G).length*(TensorNP.Eigen.graphCode G).length) +
        58*(TensorNP.Eigen.graphCode G).length+47 ∧
      out 1 = ((graphBits G).map bitSym).reverse ∧ out 2 = List.replicate v .one ∧
      (out 6).head? = some .one := by
  let input := TensorNP.Eigen.graphCode G
  obtain ⟨front, psteps, hp, hpbound, _⟩ := cappedGraphScan_total_canonical input status
  obtain ⟨good, goodSteps, hgood, hin, hbits, hvalue, hstatus, _⟩ := cappedGraphScan_graphCode G status
  have heq : front = good := TensorAdjacencyScan.exec_det hp hgood
  rw [heq] at hp
  have hfront := lift_exec frontPorts hp (extend7 (store7 input [] [] [] [] [] status))
    (project_front (store7 input [] [] [] [] [] status))
  rw [write_front] at hfront
  rw [← liftProgC_eq_liftProg frontPorts frontInverse frontInverse_correct cappedGraphScanProg] at hfront
  have haccept : frontAccepted (fun k ↦ (extend7 good k).head?) = true := by
    simp [frontAccepted, extend7, hstatus]
  obtain ⟨out, marker, dsteps, hd, hdbound, hkeepbits, hkeepvalue, hkeepstatus, hmarker, hmarkerspec⟩ :=
    diagonalFront_total good v hin hvalue
  have hdiag : ∀ i : Fin v, matrixOfBits (graphBits G) (graphBits_length G) i i = false := graph_matrix_diagonal G
  have hzero : ∀ a ∈ TensorDiagonalGather.gathered v v (good 1), a = .zero := by
    rw [hbits]
    have hsym : TensorAdjacencyScan.bitSym = diagSymbol := by
      funext b
      cases b <;> rfl
    rw [hsym]
    apply (TensorDiagonalCheck.gathered_zero_iff_diagonal (graphBits G) (graphBits_length G)).mpr
    exact hdiag
  have hm : marker = .one := hmarkerspec.mpr hzero
  have hpost : diagonalAccepted (fun k ↦ (out k).head?) = true := by
    simp [diagonalAccepted, hmarker, hm]
  have hfinish := StackProg.Exec.branchTrue (q := .act rejectAct) hpost (keep_exec out)
  have hbody := StackProg.Exec.seq hd hfinish
  have hbranch := StackProg.Exec.branchTrue (q := .act keepAct) haccept hbody
  have he := StackProg.Exec.seq hfront hbranch
  have hlen : (good 1).length = v*v := by rw [hbits]; simpa using graphBits_length G
  have hle : v ≤ input.length := by
    have hl := tensor_graphCode_length_lower G
    have hv := Nat.le_mul_self v
    change 1+v*v ≤ input.length at hl
    omega
  have hle2 : v*v ≤ input.length*input.length := Nat.mul_le_mul hle hle
  rw [hlen] at hdbound
  refine ⟨out, psteps+1+(1+(dsteps+1+2)), he, ?_, ?_, ?_, ?_⟩
  · dsimp [input] at *
    nlinarith
  · simpa [hbits] using hkeepbits
  · simpa [hvalue] using hkeepvalue
  · simpa [hkeepstatus, hstatus] 

end TensorGraphDiagonal


/-- The matrix reconstructed from a graph's row-major bit stream is exactly
    the Boolean adjacency matrix, including at dimension zero. -/
theorem matrixOfBits_graphBits {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj] :
    matrixOfBits (TensorAdjacencyScan.graphBits G) (TensorAdjacencyScan.graphBits_length G) =
      (fun i j ↦ decide (G.Adj i j)) := by
  apply tensor_matrix_flatten_injective
  simpa [TensorAdjacencyScan.graphBits] using
    matrixOfBits_flatten (TensorAdjacencyScan.graphBits G) (TensorAdjacencyScan.graphBits_length G)

/-- The Boolean matrix reconstructed from an actual graph is symmetric. -/
theorem matrixOfBits_graphBits_symmetric {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj] :
    ∀ i j, matrixOfBits (TensorAdjacencyScan.graphBits G) (TensorAdjacencyScan.graphBits_length G) i j =
      matrixOfBits (TensorAdjacencyScan.graphBits G) (TensorAdjacencyScan.graphBits_length G) j i := by
  intro i j
  rw [matrixOfBits_graphBits]
  simp [G.adj_comm]


namespace TensorGraphSymmetry

open StackProgPortLift TensorPrefixDecode TensorDiagonalFront TensorGraphDiagonal
  TensorSymmetryDecision TensorSymmetryIter TensorSymmetryPrep TensorSymmetryBridge TensorAdjacencyScan

/-- Every canonical graph code follows the successful path of the complete
    executable recognizer, including the zero-vertex graph, within the same
    all-input cubic bound. -/
theorem graphSymmetry_graphCode {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (status : List BSym) :
    ∃ out steps,
      graphSymmetryProg.Exec
        (extend11 (extend7 (store7 (TensorNP.Eigen.graphCode G) [] [] [] [] [] status))) out steps ∧
      steps ≤ 20000*((TensorNP.Eigen.graphCode G).length+1)^3 +
        47*((TensorNP.Eigen.graphCode G).length*(TensorNP.Eigen.graphCode G).length) +
        64*(TensorNP.Eigen.graphCode G).length + 62 ∧
      out 1 = ((graphBits G).map TensorAdjacencyScan.bitSym).reverse ∧
      out 2 = List.replicate v .one ∧ (out 6).head? = some .one := by
  let input := TensorNP.Eigen.graphCode G
  obtain ⟨front, psteps, hp, hpbound, hbits, hvalue, hstatus⟩ := graphDiagonal_graphCode G status
  let initial := extend7 (store7 input [] [] [] [] [] status)
  have hfront := lift_exec diagonalPorts hp (extend11 initial) (project_diagonal initial)
  rw [write_diagonal] at hfront
  rw [← liftProgC_eq_liftProg diagonalPorts diagonalInverse diagonalInverse_correct graphDiagonalProg] at hfront
  have hgood : frontGood (fun k ↦ (extend11 front k).head?) = true := by
    simpa [frontGood, extend11] using hstatus
  obtain ⟨prep, hprep, hpreserve, hprepared⟩ := symmetryPrep_exec front v hvalue
  let mat : Fin v → Fin v → BSym := fun i j ↦ TensorSymmetryBridge.bitSym
    (matrixOfBits (graphBits G) (graphBits_length G) i j)
  have hsym : TensorAdjacencyScan.bitSym = TensorSymmetryBridge.bitSym := by
    funext b; cases b <;> rfl
  have hstream : _root_.TensorGraphRecognizerInternal.matrixStream mat = (front 1).reverse := by
    have h := TensorSymmetryBridge.matrixStream_matrixOfBits (graphBits G) (graphBits_length G)
    change _root_.TensorGraphRecognizerInternal.matrixStream mat = (graphBits G).map TensorSymmetryBridge.bitSym at h
    rw [hbits, List.reverse_reverse, hsym]
    exact h
  obtain ⟨localOut, marker, symSteps, hmarker, hdata, hdim, hflag, hsymBound, hsymRun⟩ :=
    symmetryDecision_uniform v mat
  have hproject : project symmetryPorts prep = prepared (_root_.TensorGraphRecognizerInternal.matrixStream mat).reverse v := by
    change project18 prep = _
    rw [hprepared, hstream, List.reverse_reverse]
  have hlift := lift_exec symmetryPorts hsymRun prep hproject
  rw [← liftProgC_eq_liftProg symmetryPorts symmetryInverse symmetryInverse_correct
    TensorSymmetryDecision.symmetryDecisionProg] at hlift
  let symOut := write symmetryPorts localOut prep
  have hstatusPrep : prep 6 = front 6 := by simpa using hpreserve (6 : Fin 11)
  have hbitsPrep : prep 1 = front 1 := by simpa using hpreserve (1 : Fin 11)
  have hstatusOut : symOut 6 = front 6 := by
    have ho : ∀ k : Fin 18, symmetryPorts k ≠ (6 : Fin 28) := by
      intro k; fin_cases k <;> decide
    rw [show symOut 6 = prep 6 from write_outside symmetryPorts localOut prep ho]
    exact hstatusPrep
  have hbitsOut : symOut 1 = ((graphBits G).map TensorAdjacencyScan.bitSym).reverse := by
    have ho : ∀ k : Fin 18, symmetryPorts k ≠ (1 : Fin 28) := by
      intro k; fin_cases k <;> decide
    rw [show symOut 1 = prep 1 from write_outside symmetryPorts localOut prep ho, hbitsPrep]
    exact hbits
  have hdimOut : symOut 2 = List.replicate v .one := by
    change write symmetryPorts localOut prep (symmetryPorts 1) = _
    rw [write_at]
    exact hdim
  have hflagOut : symOut 27 = [marker] := by
    change write symmetryPorts localOut prep (symmetryPorts 17) = _
    rw [write_at]
    exact hflag
  have hmatSym : ∀ i j, mat i j = mat j i := by
    intro i j
    apply congrArg TensorSymmetryBridge.bitSym
    exact matrixOfBits_graphBits_symmetric G i j
  have hm : marker = .one := hmarker.mpr hmatSym
  have hpost : symmetryGood (fun k ↦ (symOut k).head?) = true := by
    simp [symmetryGood, hflagOut, hm]
  have hfinish := StackProg.Exec.branchTrue (q := .act rejectAct) hpost (keep_exec symOut)
  have hsymSeq := StackProg.Exec.seq hlift hfinish
  have hbody := StackProg.Exec.seq hprep hsymSeq
  have hbranch := StackProg.Exec.branchTrue (q := .act keepAct) hgood hbody
  have he := StackProg.Exec.seq hfront hbranch
  have hsized : (front 1).length = v*v := by rw [hbits]; simpa using graphBits_length G
  have hle : v ≤ input.length := by
    have h := tensor_graphCode_length_lower G
    have hv := Nat.le_mul_self v
    change 1+v*v ≤ input.length at h
    omega
  have hquad : v*v ≤ input.length*input.length := Nat.mul_le_mul hle hle
  have hcube : (v+1)^3 ≤ (input.length+1)^3 := by gcongr
  have hsymLarge : symSteps ≤ 20000*(input.length+1)^3 :=
    le_trans hsymBound (Nat.mul_le_mul_left 20000 hcube)
  refine ⟨symOut, psteps+1+(1+((9*(front 1).length+6*v+9)+1+(symSteps+1+2))),
    he, ?_, hbitsOut, hdimOut, ?_⟩
  · rw [hsized]
    dsimp [input] at *
    nlinarith
  · simpa [hstatusOut] using hstatus

end TensorGraphSymmetry

namespace TensorGraphSymmetry

open TensorPrefixDecode TensorDiagonalFront TensorSymmetryPrep

/-- The concrete 28-stack front end decides canonical graph-code membership
    on every input. Its top status is one exactly for a valid code, and its
    all-input source cost has the previously established cubic bound. -/
theorem graphSymmetry_decides (input : List BSym) :
    ∃ out steps,
      graphSymmetryProg.Exec (extend11 (extend7 (store7 input [] [] [] [] [] []))) out steps ∧
      steps ≤ 20000*(input.length+1)^3 + 47*(input.length*input.length) + 64*input.length + 62 ∧
      ((out 6).head? = some .one ↔
        ∃ (v : ℕ) (G : SimpleGraph (Fin v)), input = TensorNP.Eigen.graphCode G) := by
  classical
  obtain ⟨out, steps, hrun, hbound, hclass⟩ := graphSymmetry_total_sound input []
  refine ⟨out, steps, hrun, hbound, ?_⟩
  constructor
  · intro hs
    rcases hclass with ⟨n, G, hin, _, _⟩ | hbad
    · exact ⟨n, G, hin⟩
    · exact (hbad hs).elim
  · rintro ⟨n, G, hin⟩
    obtain ⟨good, cost, hgood, _, _, _, hsuccess⟩ := graphSymmetry_graphCode G []
    have heq : out = good := TensorAdjacencyScan.exec_det (by simpa only [hin] using hrun) hgood
    simpa only [heq] using hsuccess

end TensorGraphSymmetry

namespace TensorGraphRecognizer

open StackProgPortLift TensorGraphSymmetry TensorSymmetryPrep TensorDiagonalFront TensorPrefixDecode

/-- A fresh output stack is added after the 28-stack graph recognizer. -/
def graphPorts : Fin 28 ↪ Fin 29 := ⟨Fin.castSucc, Fin.castSucc_injective _⟩
def graphInverse (l : Fin 29) : Option (Fin 28) :=
  if h : l.val < 28 then some ⟨l.val, h⟩ else none

private theorem graphInverse_correct (l : Fin 29) (k : Fin 28) :
    graphInverse l = some k ↔ graphPorts k = l := by
  constructor
  · intro h
    unfold graphInverse at h
    split at h
    · rename_i hl
      have hk := Option.some.inj h
      apply Fin.ext
      exact (congrArg Fin.val hk).symm
    · cases h
  · intro h
    subst l
    simp [graphInverse, graphPorts]

private def writeFlag (h : Fin 29 → Option BSym) (k : Fin 29) : StackAct BSym :=
  if k = 28 then .push (if h 6 == some BSym.one then .one else .zero) else .keep

/-- Compute the graph-code predicate and emit exactly one result symbol on a
    fresh output port. -/
def graphFlagProg : StackProg (Fin 29) BSym :=
  .seq (liftProgC graphPorts graphInverse graphSymmetryProg) (.act writeFlag)

/-- The mathematical one-symbol characteristic function of canonical graph codes. -/
noncomputable def graphCodeFlag (w : List BSym) : List BSym := by
  classical
  exact if ∃ (n : ℕ) (G : SimpleGraph (Fin n)), w = TensorNP.Eigen.graphCode G then [.one] else [.zero]

/-- The actual finite stack program computes the characteristic flag on all
    inputs, with an explicit cubic source-step bound. -/
theorem graphFlagProg_exec (w : List BSym) :
    ∃ out steps,
      graphFlagProg.Exec (fun k ↦ if k = 0 then w else []) out steps ∧
      out 28 = graphCodeFlag w ∧
      steps ≤ 20000*(w.length+1)^3 + 47*(w.length*w.length) + 64*w.length + 64 := by
  classical
  obtain ⟨src, steps, hrun, hbound, hcorrect⟩ := graphSymmetry_decides w
  let initial : Fin 29 → List BSym := fun k ↦ if k = 0 then w else []
  have hp : project graphPorts initial = extend11 (extend7 (store7 w [] [] [] [] [] [])) := by
    funext k
    fin_cases k <;> simp [project, graphPorts, initial, extend11, extend7, store7]
  have hlift := lift_exec graphPorts hrun initial hp
  rw [← liftProgC_eq_liftProg graphPorts graphInverse graphInverse_correct graphSymmetryProg] at hlift
  let mid := write graphPorts src initial
  let out := StackProg.applyAct writeFlag mid
  have ha : (StackProg.act writeFlag).Exec mid out 1 := StackProg.Exec.act writeFlag mid
  have hs := StackProg.Exec.seq hlift ha
  have hstatus : mid 6 = src 6 := by
    simpa [mid, graphPorts] using StackProgPortLift.write_at graphPorts src initial (6 : Fin 28)
  have hblank : mid 28 = [] := by
    have ho : ∀ k : Fin 28, graphPorts k ≠ (28 : Fin 29) := by
      intro k
      apply Fin.ne_of_val_ne
      simp [graphPorts]
      omega
    simpa [mid, initial] using StackProgPortLift.write_outside graphPorts src initial ho
  refine ⟨out, steps+2, ?_, ?_, ?_⟩
  · simpa only [graphFlagProg, initial, mid, out, Nat.add_assoc] using hs
  · by_cases hv : ∃ (n : ℕ) (G : SimpleGraph (Fin n)), w = TensorNP.Eigen.graphCode G
    · have htop := hcorrect.mpr hv
      simp [out, StackProg.applyAct, writeFlag, StackAct.apply, graphCodeFlag, hv, hstatus, hblank, htop]
    · have htop : (src 6).head? ≠ some .one := fun h ↦ hv (hcorrect.mp h)
      simp [out, StackProg.applyAct, writeFlag, StackAct.apply, graphCodeFlag, hv, hstatus, hblank, htop]
  · omega

end TensorGraphRecognizer


/-- The explicit recognizer budget fits the normal form required by the
    StackProg-to-one-tape polynomial-time compiler. -/
theorem graph_cubic_budget_compiler_form (m : ℕ) :
    20000*(m+1)^3 + 47*(m*m) + 64*m + 65 ≤ m^200000 + 200000 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · norm_num
  by_cases hm1 : m = 1
  · subst m
    norm_num
  have hm2' : 2 ≤ m := by omega
  have hcub : (m+1)^3 ≤ (2*m)^3 := by gcongr <;> omega
  have hlarge : 200000 ≤ m^18 := by
    have h : (2 : ℕ)^18 ≤ m^18 := by gcongr
    norm_num at h
    omega
  have hquad : m*m ≤ m^3 := by
    have h := Nat.mul_le_mul_left (m*m) (show 1 ≤ m by omega)
    nlinarith
  have hlin : m ≤ m^3 := by
    have h := Nat.le_mul_self m
    omega
  have hone : 1 ≤ m^3 := by omega
  have hpoly : 20000*(m+1)^3 + 47*(m*m) + 64*m + 65 ≤ 200000*m^3 := by
    nlinarith
  have hprod := Nat.mul_le_mul_left (m^3) hlarge
  have h21 : 200000*m^3 ≤ m^21 := by
    rw [show (21 : ℕ) = 3+18 by decide, pow_add]
    nlinarith
  have hbig : m^21 ≤ m^200000 := by gcongr <;> omega
  omega

namespace TensorGraphRecognizer

/-- The exact canonical-graph-code flag is computable in polynomial time by
    the published one-tape Cook machine model. -/
theorem graphCodeFlag_polytime : CookPvsNP.PolyTimeComputable graphCodeFlag := by
  apply CookPvsNP.stack_program_polytime graphFlagProg (0 : Fin 29) 28 graphCodeFlag 200000
  intro w
  obtain ⟨out, steps, hrun, hout, hbound⟩ := graphFlagProg_exec w
  refine ⟨out, steps, ?_, hrun, hout⟩
  have hbudget := graph_cubic_budget_compiler_form w.length
  omega

end TensorGraphRecognizer


end TensorGraphRecognizerInternal

open CookPvsNP ProjSchedTW.Complexity

/-- A polynomial-time characteristic function for canonical graph codes. -/
theorem solution :
    ∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      ∀ w, (f w = [.one] ↔ ∃ (v : ℕ) (G : SimpleGraph (Fin v)), w = TensorNP.Eigen.graphCode G) ∧
           (f w = [.zero] ↔ ¬ ∃ (v : ℕ) (G : SimpleGraph (Fin v)), w = TensorNP.Eigen.graphCode G) := by
  classical
  refine ⟨TensorGraphRecognizerInternal.TensorGraphRecognizer.graphCodeFlag,
    TensorGraphRecognizerInternal.TensorGraphRecognizer.graphCodeFlag_polytime, ?_⟩
  intro w
  by_cases h : ∃ (v : ℕ) (G : SimpleGraph (Fin v)), w = TensorNP.Eigen.graphCode G
  · simp [TensorGraphRecognizerInternal.TensorGraphRecognizer.graphCodeFlag, h]
  · simp [TensorGraphRecognizerInternal.TensorGraphRecognizer.graphCodeFlag, h]

#print axioms solution
