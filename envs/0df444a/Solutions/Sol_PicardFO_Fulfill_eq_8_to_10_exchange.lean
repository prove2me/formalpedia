-- Prove2me | solution 1 for PicardFO.Fulfill.eq_8_to_10_exchange
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:51:19.659554+00:00
-- url     : https://prove2.me/submissions/798f063c-b694-41d3-b6dc-97df28000a7c

import Definitions.Def_PicardFO_Fulfill_Picard
import Definitions.Def_PicardFO_Fulfill_Model
import Init
import Mathlib



section
noncomputable section
namespace Queelius.Fulfillment
open PicardFO.Fulfill
variable {S A Ω ι : Type*}

theorem process_feasible (sys : System S A Ω) (π : S→Ω→A)
    (hp : ∀s w,sys.feasible s w (π s w)) (ω : ℕ→Ω) (proc : ℕ→ι)
    (α : ℕ→A) (m : ι) (s : S) (t : ℕ) :
    sys.feasible s (ω t) (sys.procAct π ω proc α m s t) := by
  classical
  unfold System.procAct
  split_ifs with h1 h2
  · exact hp s (ω t)
  · exact h2
  · exact sys.aPhi_feasible s (ω t)

theorem replay_correct_prefix (sys : System S A Ω) (π : S→Ω→A)
    (hp : ∀s w,sys.feasible s w (π s w)) (s₁ : S) (ω : ℕ→Ω) (proc : ℕ→ι)
    (α : ℕ→A) (m : ι) (t : ℕ) (hα : ∀u<t,α u=sys.seqAct π s₁ ω u) :
    sys.procState π s₁ ω proc α m t=sys.seqState π s₁ ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hstate:=ih (fun u hu=>hα u (Nat.lt_succ_of_lt hu))
    rw [System.procState,System.seqState,hstate]
    congr 1
    unfold System.procAct
    split_ifs with hown hfeas
    · rfl
    · exact hα t (Nat.lt_succ_self t)
    · exfalso
      apply hfeas
      rw [hα t (Nat.lt_succ_self t)]
      exact hp _ _

theorem cache_owner_action (sys : System S A Ω) (π : S→Ω→A) (s₁ : S) (ω : ℕ→Ω)
    (proc : ℕ→ι) (k t : ℕ) :
    sys.cache π s₁ ω proc (k+1) t=
      π (sys.procState π s₁ ω proc (sys.cache π s₁ ω proc k) (proc t) t) (ω t) := by
  simp [System.cache,System.procAct]

theorem cache_step_prefix (sys : System S A Ω) (π : S→Ω→A)
    (hp : ∀s w,sys.feasible s w (π s w)) (s₁ : S) (ω : ℕ→Ω) (proc : ℕ→ι)
    (k t : ℕ) (h : ∀u<t,sys.cache π s₁ ω proc k u=sys.seqAct π s₁ ω u) :
    sys.cache π s₁ ω proc (k+1) t=sys.seqAct π s₁ ω t := by
  rw [cache_owner_action,replay_correct_prefix sys π hp s₁ ω proc _ _ t h]
  rfl

theorem cache_fixed_point_correct (sys : System S A Ω) (π : S→Ω→A)
    (hp : ∀s w,sys.feasible s w (π s w)) (s₁ : S) (ω : ℕ→Ω) (proc : ℕ→ι)
    (k T : ℕ) (h : ∀t<T,sys.cache π s₁ ω proc (k+1) t=sys.cache π s₁ ω proc k t) :
    ∀t<T,sys.cache π s₁ ω proc (k+1) t=sys.seqAct π s₁ ω t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht
    apply cache_step_prefix sys π hp s₁ ω proc k t
    intro u hu
    rw [←h u (hu.trans ht)]
    exact ih u hu (hu.trans ht)

theorem cache_correct_prefix (sys : System S A Ω) (π : S→Ω→A)
    (hp : ∀s w,sys.feasible s w (π s w)) (s₁ : S) (ω : ℕ→Ω) (proc : ℕ→ι)
    (k : ℕ) : ∀t<k,sys.cache π s₁ ω proc k t=sys.seqAct π s₁ ω t := by
  induction k with
  | zero => intro t ht; omega
  | succ k ih =>
    intro t ht
    apply cache_step_prefix sys π hp s₁ ω proc k t
    intro u hu
    apply ih u
    omega

theorem cache_horizon_bound (sys : System S A Ω) (π : S→Ω→A)
    (hp : ∀s w,sys.feasible s w (π s w)) (s₁ : S) (ω : ℕ→Ω) (proc : ℕ→ι)
    (T k : ℕ) (hk : T≤k) : ∀t<T,sys.cache π s₁ ω proc k t=sys.seqAct π s₁ ω t := by
  intro t ht
  exact cache_correct_prefix sys π hp s₁ ω proc k t (ht.trans_le hk)

end Queelius.Fulfillment

end

section
noncomputable section
open scoped BigOperators
namespace Queelius.Fulfillment
open PicardFO.Fulfill

def debit {J : ℕ} (a : Option (Fin J)) (j : Fin J) : ℝ := if a=some j then 1 else 0

@[simp] theorem debit_none {J : ℕ} (j : Fin J) : debit none j=0 := by simp [debit]

theorem step_capacity {I J : ℕ} (s : State I J) (p : Fin I) (a : Option (Fin J)) (j : Fin J) :
    (step s p a).c j=s.c j-debit a j := by
  cases a with
  | none => simp [step,debit]
  | some k => by_cases h:j=k <;> simp [step,debit,Function.update_apply,h,eq_comm]

theorem step_inventory {I J : ℕ} (s : State I J) (p i : Fin I) (a : Option (Fin J)) (j : Fin J) :
    (step s p a).x i j=s.x i j-(if i=p then debit a j else 0) := by
  cases a with
  | none => simp [step,debit]
  | some k => by_cases hi:i=p <;> by_cases hj:j=k <;>
      simp [step,debit,Function.update_apply,hi,hj,eq_comm]

theorem step_balance {I J : ℕ} (s : State I J) (p : Fin I) (a : Option (Fin J)) (j : Fin J) :
    (step s p a).c j-∑i,(step s p a).x i j=s.c j-∑i,s.x i j := by
  simp only [step_capacity,step_inventory,Finset.sum_sub_distrib]
  simp

theorem sequential_balance {I J : ℕ} {Ω : Type*} (prod : Ω→Fin I)
    (π : State I J→Ω→Option (Fin J)) (s₁ : State I J) (ω : ℕ→Ω) (t : ℕ) (j : Fin J) :
    (seqState prod π s₁ ω t).c j-∑i,(seqState prod π s₁ ω t).x i j=s₁.c j-∑i,s₁.x i j := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (step (seqState prod π s₁ ω t) (prod (ω t)) (seqAct prod π s₁ ω t)).c j-
      ∑i,(step (seqState prod π s₁ ω t) (prod (ω t)) (seqAct prod π s₁ ω t)).x i j=_
    rw [step_balance,ih]

theorem process_balance {I J : ℕ} {Ω ι : Type*} (prod : Ω→Fin I)
    (π : State I J→Ω→Option (Fin J)) (s₁ : State I J) (ω : ℕ→Ω) (own : Fin I→ι)
    (α : ℕ→Option (Fin J)) (m : ι) (t : ℕ) (j : Fin J) :
    (procState prod π s₁ ω own α m t).c j-∑i,(procState prod π s₁ ω own α m t).x i j=
      s₁.c j-∑i,s₁.x i j := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (step (procState prod π s₁ ω own α m t) (prod (ω t))
      (procAct prod π ω own α m (procState prod π s₁ ω own α m t) t)).c j-
      ∑i,(step (procState prod π s₁ ω own α m t) (prod (ω t))
        (procAct prod π ω own α m (procState prod π s₁ ω own α m t) t)).x i j=_
    rw [step_balance,ih]

end Queelius.Fulfillment

end

section
noncomputable section
namespace Queelius.Fulfillment
open PicardFO.Fulfill

variable {I J : ℕ}

theorem state_ext (s t : State I J) (hx : ∀ i j, s.x i j=t.x i j) (hc : ∀ j, s.c j=t.c j) : s=t := by
  cases s
  cases t
  simp only [State.mk.injEq]
  exact ⟨funext (fun i => funext (hx i)),funext hc⟩

def raiseCap (s : State I J) (j : Fin J) (n : ℕ) : State I J :=
  ⟨s.x,Function.update s.c j (s.c j+n)⟩

def raiseInv (s : State I J) (i : Fin I) (j : Fin J) (n : ℕ) : State I J :=
  ⟨Function.update s.x i (Function.update (s.x i) j (s.x i j+n)),s.c⟩

@[simp] theorem raiseCap_zero (s : State I J) (j : Fin J) : raiseCap s j 0=s := by
  apply state_ext
  · intro i k; rfl
  · intro k; simp [raiseCap]

@[simp] theorem raiseInv_zero (s : State I J) (i : Fin I) (j : Fin J) : raiseInv s i j 0=s := by
  apply state_ext
  · intro a b; simp [raiseInv]
  · intro k; rfl

theorem raiseCap_succ (s : State I J) (j : Fin J) (n : ℕ) :
    raiseCap s j (n+1)=raiseCap (raiseCap s j n) j 1 := by
  apply state_ext
  · intro i k; rfl
  · intro k
    by_cases h : k=j <;> simp [raiseCap,h,Nat.cast_add,add_assoc]

theorem raiseInv_succ (s : State I J) (i : Fin I) (j : Fin J) (n : ℕ) :
    raiseInv s i j (n+1)=raiseInv (raiseInv s i j n) i j 1 := by
  apply state_ext
  · intro a b
    by_cases ha : a=i <;> by_cases hb : b=j <;> simp [raiseInv,ha,hb,Nat.cast_add,add_assoc]
  · intro k; rfl

theorem capacity_units {Ω : Type*} (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (h3 : MonotonePolicy prod π) (s : State I J) (w : Ω) (j : Fin J)
    (hj : 0 < s.c j) (n : ℕ) : π (raiseCap s j n) w=π s w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [raiseCap_succ]
    have hp : 0 < (raiseCap s j n).c j := by simp [raiseCap]; positivity
    simpa only [raiseCap,Nat.cast_one] using (h3.2 (raiseCap s j n) w j hp).trans ih

theorem chosen_inventory_units {Ω : Type*} (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (h3 : MonotonePolicy prod π) (s : State I J) (w : Ω) (j : Fin J)
    (hj : π s w=some j) (n : ℕ) : π (raiseInv s (prod w) j n) w=some j := by
  induction n with
  | zero => simpa using hj
  | succ n ih =>
    rw [raiseInv_succ]
    simpa only [raiseInv,Nat.cast_one] using h3.1 (raiseInv s (prod w) j n) w j ih

def setNode (s : State I J) (i : Fin I) (j : Fin J) (x c : ℝ) : State I J :=
  ⟨Function.update s.x i (Function.update (s.x i) j x),Function.update s.c j c⟩

theorem setNode_capacity (s : State I J) (i : Fin I) (j : Fin J) (n : ℕ) :
    setNode s i j (s.x i j) (s.c j+n)=raiseCap s j n := by
  apply state_ext
  · intro a b; simp [setNode,raiseCap]
  · intro k; rfl

theorem setNode_raises (s : State I J) (i : Fin I) (j : Fin J) (nx nc : ℕ) :
    setNode s i j (s.x i j+nx) (s.c j+nc)=raiseCap (raiseInv s i j nx) j nc := rfl

theorem one_node_exchange {Ω : Type*} (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (hfeas : PolicyFeasible prod π) (h2 : Consistent prod π) (h3 : MonotonePolicy prod π)
    (s : State I J) (w : Ω) (j : Fin J) (x c : ℝ)
    (hcase : s.c j ≤ 0 ∨ (0 < s.c j ∧ (∃ n : ℕ,c=s.c j+n) ∧ (∃ n : ℕ,x=s.x (prod w) j+n))) :
    π (setNode s (prod w) j x c) w=π s w ∨
      (π (setNode s (prod w) j x c) w=some j ∧ (s.c j ≤ 0 ∨ s.x (prod w) j < x)) := by
  classical
  by_cases hchosen : π s w=some j
  · have hpos : 0 < s.c j := by
      have hf:=hfeas s w
      rw [hchosen] at hf
      exact hf.1
    rcases hcase with hbad | ⟨hgood,⟨nc,rfl⟩,⟨nx,rfl⟩⟩
    · exact False.elim (not_lt_of_ge hbad hpos)
    · left
      rw [setNode_raises]
      rw [capacity_units prod π h3 (raiseInv s (prod w) j nx) w j hpos nc]
      exact (chosen_inventory_units prod π h3 s w j hchosen nx).trans hchosen.symm
  · have hx : ∀ a b, (a ≠ prod w ∨ b ≠ j) → (setNode s (prod w) j x c).x a b=s.x a b := by
      intro a b h
      rcases h with ha | hb
      · simp [setNode,ha]
      · by_cases ha : a=prod w <;> simp [setNode,ha,hb]
    have hc : ∀ b,b ≠ j → (setNode s (prod w) j x c).c b=s.c b := by
      intro b hb
      simp [setNode,hb]
    rcases h2 s (setNode s (prod w) j x c) w j hchosen hx hc with he | he
    · exact Or.inl he
    · right
      refine ⟨he,?_⟩
      rcases hcase with hbad | ⟨hgood,⟨nc,rfl⟩,⟨nx,rfl⟩⟩
      · exact Or.inl hbad
      · right
        by_cases hn : nx=0
        · subst nx
          simp only [Nat.cast_zero,add_zero,setNode_capacity] at he
          rw [capacity_units prod π h3 s w j hgood nc] at he
          exact False.elim (hchosen he)
        · have hnx : (0 : ℝ) < nx := by exact_mod_cast Nat.pos_of_ne_zero hn
          linarith
end Queelius.Fulfillment

end

section
noncomputable section
open scoped BigOperators
namespace Queelius.Fulfillment
open PicardFO.Fulfill

theorem debit_nonneg {J : ℕ} (a : Option (Fin J)) (j : Fin J) : 0≤debit a j := by
  simp only [debit]
  split_ifs <;> norm_num

theorem outsider_debit_le {I J : ℕ} {Ω ι : Type*} (prod : Ω→Fin I)
    (π : State I J→Ω→Option (Fin J)) (ω : ℕ→Ω) (own : Fin I→ι)
    (α : ℕ→Option (Fin J)) (m : ι) (s : State I J) (t : ℕ) (j : Fin J)
    (h : own (prod (ω t))≠m) : debit (procAct prod π ω own α m s t) j≤debit (α t) j := by
  classical
  unfold procAct System.procAct
  simp only [orderProc,h,if_false]
  split_ifs
  · rfl
  · exact debit_nonneg (α t) j

theorem process_inventory_compare {I J : ℕ} {Ω ι : Type*} (prod : Ω→Fin I)
    (π : State I J→Ω→Option (Fin J)) (s₁ : State I J) (ω : ℕ→Ω) (own : Fin I→ι)
    (α β : ℕ→Option (Fin J)) (m n : ι) (i : Fin I) (j : Fin J)
    (h : ∀t,prod (ω t)=i →
      debit (procAct prod π ω own β n (procState prod π s₁ ω own β n t) t) j≤
      debit (procAct prod π ω own α m (procState prod π s₁ ω own α m t) t) j) :
    ∀t,(procState prod π s₁ ω own α m t).x i j≤(procState prod π s₁ ω own β n t).x i j := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    change (step (procState prod π s₁ ω own α m t) (prod (ω t))
      (procAct prod π ω own α m (procState prod π s₁ ω own α m t) t)).x i j≤
      (step (procState prod π s₁ ω own β n t) (prod (ω t))
        (procAct prod π ω own β n (procState prod π s₁ ω own β n t) t)).x i j
    rw [step_inventory,step_inventory]
    by_cases hi : prod (ω t)=i
    · simp only [hi,if_true]
      linarith [h t hi]
    · simp only [Ne.symm hi,if_false,sub_zero]
      exact ih

theorem initial_outsider_inventory {I J : ℕ} {Ω ι : Type*} (prod : Ω→Fin I)
    (π : State I J→Ω→Option (Fin J)) (s₁ : State I J) (ω : ℕ→Ω) (own : Fin I→ι)
    (m : ι) (i : Fin I) (hm : own i≠m) (t : ℕ) (j : Fin J) :
    (procState prod π s₁ ω own (cache prod π s₁ ω own 0) m t).x i j=s₁.x i j := by
  classical
  induction t with
  | zero => rfl
  | succ t ih =>
    change (step (procState prod π s₁ ω own (cache prod π s₁ ω own 0) m t) (prod (ω t))
      (procAct prod π ω own (cache prod π s₁ ω own 0) m
        (procState prod π s₁ ω own (cache prod π s₁ ω own 0) m t) t)).x i j=_
    rw [step_inventory]
    by_cases hi : prod (ω t)=i
    · simp only [hi,if_true]
      have hz : procAct prod π ω own (cache prod π s₁ ω own 0) m
          (procState prod π s₁ ω own (cache prod π s₁ ω own 0) m t) t=none := by
        simp [procAct,System.procAct,orderProc,hi,hm,cache,System.cache,foSystem,Feasible]
      rw [hz,debit_none,sub_zero,ih]
    · simp only [Ne.symm hi,if_false,sub_zero,ih]

theorem later_outsider_inventory {I J : ℕ} {Ω ι : Type*} (prod : Ω→Fin I)
    (π : State I J→Ω→Option (Fin J)) (s₁ : State I J) (ω : ℕ→Ω) (own : Fin I→ι)
    (m : ι) (i : Fin I) (hm : own i≠m) (k t : ℕ) (j : Fin J) :
    (procState prod π s₁ ω own (cache prod π s₁ ω own k) (own i) t).x i j≤
      (procState prod π s₁ ω own (cache prod π s₁ ω own (k+1)) m t).x i j := by
  apply process_inventory_compare prod π s₁ ω own _ _ (own i) m i j _ t
  intro u hu
  have hown : own (prod (ω u))≠m := by rw [hu]; exact hm
  have hcache : cache prod π s₁ ω own (k+1) u=
      procAct prod π ω own (cache prod π s₁ ω own k) (own i)
        (procState prod π s₁ ω own (cache prod π s₁ ω own k) (own i) u) u := by
    change (foSystem I J Ω prod).cache π s₁ ω (orderProc prod ω own) (k+1) u=
      (foSystem I J Ω prod).procAct π ω (orderProc prod ω own)
        ((foSystem I J Ω prod).cache π s₁ ω (orderProc prod ω own) k) (own i)
        ((foSystem I J Ω prod).procState π s₁ ω (orderProc prod ω own)
          ((foSystem I J Ω prod).cache π s₁ ω (orderProc prod ω own) k) (own i) u) u
    rw [System.cache]
    simp only [orderProc,hu]
  simpa only [hcache] using outsider_debit_le prod π ω own
    (cache prod π s₁ ω own (k+1)) m
    (procState prod π s₁ ω own (cache prod π s₁ ω own (k+1)) m u) u j hown
end Queelius.Fulfillment

end

section
noncomputable section
namespace Queelius.Fulfillment.Controls
open PicardFO.Fulfill

-- A feasible fulfillment policy used to expose an actual skipped replay.
def guardedPolicy {I J : ℕ} [NeZero J] (s : State I J) (i : Fin I) : Option (Fin J) :=
  if 0<s.c 0 ∧ 0<s.x i 0 then some 0 else none

theorem guardedPolicy_feasible {I J : ℕ} [NeZero J] :
    PolicyFeasible (fun i : Fin I=>i) (guardedPolicy (I:=I) (J:=J)) := by
  intro s i
  unfold guardedPolicy
  split_ifs with h
  · exact h
  · trivial

def twoProductState : State 2 1 := ⟨fun _ _=>1,fun _=>1⟩
def alternatingOrder (t : ℕ) : Fin 2 := ⟨t%2,Nat.mod_lt _ (by decide)⟩

theorem skipped_replay_is_strict :
    (procState id (guardedPolicy (I:=2) (J:=1)) twoProductState alternatingOrder id
      (cache id guardedPolicy twoProductState alternatingOrder id 0) (1:Fin 2) 2).x 1 0=0 ∧
    (procState id (guardedPolicy (I:=2) (J:=1)) twoProductState alternatingOrder id
      (cache id guardedPolicy twoProductState alternatingOrder id 1) (0:Fin 2) 2).x 1 0=1 := by
  norm_num [procState,cache,System.procState,System.cache,System.procAct,foSystem,
    orderProc,alternatingOrder,guardedPolicy,twoProductState,step,Feasible]

def fractionalState : State 1 1 := ⟨fun _ _=>1,fun _=>(1/2:ℝ)⟩

theorem fractional_capacity_exhaustion :
    (seqState id (guardedPolicy (I:=1) (J:=1)) fractionalState (fun _=>0) 1).c 0= -(1/2:ℝ) ∧
    (0:Fin 1)∈Q id guardedPolicy fractionalState (fun _=>0) 2 := by
  norm_num [seqState,System.seqState,foSystem,guardedPolicy,fractionalState,step,Q]
  exact ⟨1,by norm_num,by norm_num [seqState,System.seqState,foSystem,guardedPolicy,fractionalState,step]⟩

def unsafeSystem : System Bool Bool Bool where
  feasible _ _ a := a=false
  aPhi := false
  aPhi_feasible _ _ := rfl
  f s a _ := xor s a

def unsafePolicy (s w : Bool) : Bool := if w then s else true
def unsafeOrders (t : ℕ) : Bool := decide (t≠0)
def alternatingProcess (t : ℕ) : Fin 2 := ⟨t%2,Nat.mod_lt _ (by decide)⟩

theorem infeasible_policy_false_fixed_point :
    (∀t<2,unsafeSystem.cache unsafePolicy false unsafeOrders alternatingProcess 2 t=
      unsafeSystem.cache unsafePolicy false unsafeOrders alternatingProcess 1 t) ∧
    unsafeSystem.cache unsafePolicy false unsafeOrders alternatingProcess 2 1≠
      unsafeSystem.seqAct unsafePolicy false unsafeOrders 1 := by
  constructor
  · intro t ht
    interval_cases t <;> norm_num [unsafeSystem,unsafePolicy,unsafeOrders,alternatingProcess,
      System.cache,System.procAct,System.procState,System.seqAct,System.seqState]
  · norm_num [unsafeSystem,unsafePolicy,unsafeOrders,alternatingProcess,
      System.cache,System.procAct,System.procState,System.seqAct,System.seqState]
end Queelius.Fulfillment.Controls

end

section
noncomputable section
namespace Queelius.Fulfillment
open PicardFO.Fulfill

theorem unit_decrement_count (z : ℕ→ℝ) (P : ℕ→Prop) [DecidablePred P]
    (hz : ∀t,z (t+1)=z t-(if P t then 1 else 0)) (t : ℕ) :
    ∃n : ℕ,n≤t ∧ z t=z 0-(n:ℝ) := by
  induction t with
  | zero => exact ⟨0,by omega,by simp⟩
  | succ t ih =>
    obtain ⟨n,hn,he⟩:=ih
    rw [hz,he]
    by_cases hp : P t
    · refine ⟨n+1,by omega,?_⟩
      simp only [hp,if_true,Nat.cast_add,Nat.cast_one]
      ring
    · exact ⟨n,by omega,by simp [hp]⟩

theorem process_inventory_count {I J : ℕ} {Ω ι : Type*} (prod : Ω→Fin I)
    (π : State I J→Ω→Option (Fin J)) (s₁ : State I J) (ω : ℕ→Ω) (own : Fin I→ι)
    (α : ℕ→Option (Fin J)) (m : ι) (t : ℕ) (i : Fin I) (j : Fin J) :
    ∃n : ℕ,n≤t ∧ (procState prod π s₁ ω own α m t).x i j=s₁.x i j-(n:ℝ) := by
  classical
  apply unit_decrement_count (fun t=>(procState prod π s₁ ω own α m t).x i j)
    (fun t=>i=prod (ω t) ∧ procAct prod π ω own α m (procState prod π s₁ ω own α m t) t=some j) _ t
  intro u
  change (step (procState prod π s₁ ω own α m u) (prod (ω u))
    (procAct prod π ω own α m (procState prod π s₁ ω own α m u) u)).x i j=_
  rw [step_inventory]
  simp only [debit]
  split_ifs <;> simp_all

theorem process_capacity_count {I J : ℕ} {Ω ι : Type*} (prod : Ω→Fin I)
    (π : State I J→Ω→Option (Fin J)) (s₁ : State I J) (ω : ℕ→Ω) (own : Fin I→ι)
    (α : ℕ→Option (Fin J)) (m : ι) (t : ℕ) (j : Fin J) :
    ∃n : ℕ,n≤t ∧ (procState prod π s₁ ω own α m t).c j=s₁.c j-(n:ℝ) := by
  classical
  apply unit_decrement_count (fun t=>(procState prod π s₁ ω own α m t).c j)
    (fun t=>procAct prod π ω own α m (procState prod π s₁ ω own α m t) t=some j) _ t
  intro u
  exact step_capacity _ _ _ _

theorem sequential_inventory_count {I J : ℕ} {Ω : Type*} (prod : Ω→Fin I)
    (π : State I J→Ω→Option (Fin J)) (s₁ : State I J) (ω : ℕ→Ω)
    (t : ℕ) (i : Fin I) (j : Fin J) :
    ∃n : ℕ,n≤t ∧ (seqState prod π s₁ ω t).x i j=s₁.x i j-(n:ℝ) := by
  classical
  apply unit_decrement_count (fun t=>(seqState prod π s₁ ω t).x i j)
    (fun t=>i=prod (ω t) ∧ seqAct prod π s₁ ω t=some j) _ t
  intro u
  change (step (seqState prod π s₁ ω u) (prod (ω u)) (seqAct prod π s₁ ω u)).x i j=_
  rw [step_inventory]
  simp only [debit]
  split_ifs <;> simp_all

theorem sequential_capacity_count {I J : ℕ} {Ω : Type*} (prod : Ω→Fin I)
    (π : State I J→Ω→Option (Fin J)) (s₁ : State I J) (ω : ℕ→Ω)
    (t : ℕ) (j : Fin J) :
    ∃n : ℕ,n≤t ∧ (seqState prod π s₁ ω t).c j=s₁.c j-(n:ℝ) := by
  classical
  apply unit_decrement_count (fun t=>(seqState prod π s₁ ω t).c j)
    (fun t=>seqAct prod π s₁ ω t=some j) _ t
  intro u
  exact step_capacity _ _ _ _

theorem integral_gap_at_least_one (a x y : ℝ) (m n : ℕ)
    (hx : x=a-(m:ℝ)) (hy : y=a-(n:ℝ)) (hxy : x<y) : x+1≤y := by
  have hn : n < m := by exact_mod_cast (show (n:ℝ) < m by linarith)
  have hs : (n:ℝ)+1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt hn
  linarith

theorem integral_gap_nat (a x y : ℝ) (m n : ℕ)
    (hx : x=a-(m:ℝ)) (hy : y=a-(n:ℝ)) (hxy : x≤y) :
    ∃d : ℕ,y=x+(d:ℝ) := by
  have hn : n ≤ m := by exact_mod_cast (show (n:ℝ) ≤ m by linarith)
  refine ⟨m-n,?_⟩
  rw [Nat.cast_sub hn]
  linarith
end Queelius.Fulfillment

end

section
noncomputable section
namespace Queelius.Fulfillment
open PicardFO.Fulfill

variable {I J : ℕ}

def mixed (s s' : State I J) (i : Fin I) (F : Finset (Fin J)) : State I J :=
  ⟨fun a b => if a=i ∧ b ∈ F then s'.x a b else s.x a b,
    fun b => if b ∈ F then s'.c b else s.c b⟩

@[simp] theorem mixed_empty (s s' : State I J) (i : Fin I) : mixed s s' i ∅=s := by
  apply state_ext <;> intros <;> simp [mixed]

theorem mixed_insert (s s' : State I J) (i : Fin I) (F : Finset (Fin J)) (j : Fin J) :
    mixed s s' i (insert j F)=setNode (mixed s s' i F) i j (s'.x i j) (s'.c j) := by
  apply state_ext
  · intro a b
    by_cases ha : a=i <;> by_cases hb : b=j <;> simp [mixed,setNode,ha,hb]
  · intro b
    by_cases hb : b=j <;> simp [mixed,setNode,hb]

theorem same_row_capacity {Ω : Type*} (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (h1 : InvIndep prod π) (s t : State I J) (w : Ω)
    (hx : ∀ j,s.x (prod w) j=t.x (prod w) j) (hc : s.c=t.c) : π s w=π t w := by
  have he : (⟨s.x,t.c⟩ : State I J)=s := by
    apply state_ext
    · intros; rfl
    · intro j; exact congrFun hc.symm j
  calc
    π s w=π ⟨s.x,t.c⟩ w := congrArg (fun u => π u w) he.symm
    _=π t w := h1 s.x t.x t.c w hx

theorem exchange {Ω : Type*} (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π) (s s' : State I J) (w : Ω) (Qs : Finset (Fin J))
    (hQ : ∀ j ∈ Qs,s.c j ≤ 0) (hQc : ∀ j ∉ Qs,0 < s.c j)
    (hc : ∀ j ∉ Qs,∃ n : ℕ,s'.c j=s.c j+n)
    (hx : ∀ j ∉ Qs,∃ n : ℕ,s'.x (prod w) j=s.x (prod w) j+n) :
    π s' w=π s w ∨ ∃ j,π s' w=some j ∧
      (j ∈ Qs ∨ (j ∉ Qs ∧ s.x (prod w) j < s'.x (prod w) j)) := by
  classical
  have hF (F : Finset (Fin J)) :
      π (mixed s s' (prod w) F) w=π s w ∨
      ∃ j,π (mixed s s' (prod w) F) w=some j ∧
        (j ∈ Qs ∨ (j ∉ Qs ∧ s.x (prod w) j < s'.x (prod w) j)) := by
    induction F using Finset.induction_on with
    | empty => exact Or.inl (by simp)
    | @insert j F hj ih =>
      have hcu : (mixed s s' (prod w) F).c j=s.c j := by simp [mixed,hj]
      have hxu : (mixed s s' (prod w) F).x (prod w) j=s.x (prod w) j := by simp [mixed,hj]
      have hcase : (mixed s s' (prod w) F).c j ≤ 0 ∨
          (0 < (mixed s s' (prod w) F).c j ∧
           (∃ n : ℕ,s'.c j=(mixed s s' (prod w) F).c j+n) ∧
           (∃ n : ℕ,s'.x (prod w) j=(mixed s s' (prod w) F).x (prod w) j+n)) := by
        rw [hcu,hxu]
        by_cases hq : j ∈ Qs
        · exact Or.inl (hQ j hq)
        · exact Or.inr ⟨hQc j hq,hc j hq,hx j hq⟩
      have hstep:=one_node_exchange prod π hfeas h2 h3 (mixed s s' (prod w) F) w j
        (s'.x (prod w) j) (s'.c j) hcase
      rw [←mixed_insert] at hstep
      rcases hstep with he | ⟨he,hreason⟩
      · rcases ih with hi | ⟨k,hk,hkq⟩
        · exact Or.inl (he.trans hi)
        · exact Or.inr ⟨k,he.trans hk,hkq⟩
      · refine Or.inr ⟨j,he,?_⟩
        by_cases hq : j ∈ Qs
        · exact Or.inl hq
        · refine Or.inr ⟨hq,?_⟩
          rcases hreason with hbad | hmore
          · rw [hcu] at hbad
            exact False.elim (not_lt_of_ge hbad (hQc j hq))
          · rwa [hxu] at hmore
  have he : π (mixed s s' (prod w) Finset.univ) w=π s' w := by
    apply same_row_capacity prod π h1
    · intro j; simp [mixed]
    · funext j; simp [mixed]
  simpa only [he] using hF Finset.univ
end Queelius.Fulfillment

end

section
namespace PicardFO.Fulfill

/-- §A.2.1 (pp. 12–13): along every run, the capacity consumed at a node equals the sum over
products of the inventory consumed there, both for every process of Algorithm 1 (any cache `α`)
and for the sequential run. No assumption on `π` is needed. -/
theorem sec_A_2_1_conservation {I J : ℕ} {Ω ι : Type*} (prod : Ω → Fin I)
    (π : State I J → Ω → Option (Fin J)) (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι) :
    (∀ (α : ℕ → Option (Fin J)) (m : ι) (t : ℕ) (j : Fin J),
        (procState prod π s₁ ω own α m t).c j =
          s₁.c j - ∑ i, (s₁.x i j - (procState prod π s₁ ω own α m t).x i j)) ∧
    (∀ (t : ℕ) (j : Fin J),
        (seqState prod π s₁ ω t).c j =
          s₁.c j - ∑ i, (s₁.x i j - (seqState prod π s₁ ω t).x i j)) := by
  constructor
  · intro α m t j
    have h:=Queelius.Fulfillment.process_balance prod π s₁ ω own α m t j
    rw [Finset.sum_sub_distrib]
    linarith
  · intro t j
    have h:=Queelius.Fulfillment.sequential_balance prod π s₁ ω t j
    rw [Finset.sum_sub_distrib]
    linarith

end PicardFO.Fulfill

namespace PicardFO.Fulfill

/-- Proof of Lemma A.1, skip step (p. 12), corrected (`=` → `≥`): a process `m` that does
not own product `i` holds, at every time, at least as much inventory of `i` at every node as
the owner of `i` held in the previous iteration; in the first iteration (cache `α⁰ ≡ aϕ`) it
has not consumed any inventory of `i`. No assumption on `π` is needed. -/
theorem lemma_A_1_skip_step {I J : ℕ} {Ω ι : Type*} (prod : Ω → Fin I)
    (π : State I J → Ω → Option (Fin J)) (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι)
    (m : ι) (i : Fin I) (hm : own i ≠ m) :
    (∀ (t : ℕ) (j : Fin J),
        (procState prod π s₁ ω own (cache prod π s₁ ω own 0) m t).x i j = s₁.x i j) ∧
    (∀ (k t : ℕ) (j : Fin J),
        (procState prod π s₁ ω own (cache prod π s₁ ω own k) (own i) t).x i j ≤
          (procState prod π s₁ ω own (cache prod π s₁ ω own (k + 1)) m t).x i j) := by
  exact ⟨Queelius.Fulfillment.initial_outsider_inventory prod π s₁ ω own m i hm,
    Queelius.Fulfillment.later_outsider_inventory prod π s₁ ω own m i hm⟩

end PicardFO.Fulfill

end

section
noncomputable section
namespace Queelius.Fulfillment.Controls
open PicardFO.Fulfill

theorem single_node_independence {I : ℕ} :
    InvIndep (fun i : Fin I => i) (guardedPolicy (I:=I) (J:=1)) := by
  intro x y c w h
  simp only [guardedPolicy,h 0]

theorem single_node_consistency {I : ℕ} :
    Consistent (fun i : Fin I => i) (guardedPolicy (I:=I) (J:=1)) := by
  intro s s' w j hn hx hc
  have hj : j=0 := Subsingleton.elim _ _
  subst j
  unfold guardedPolicy at hn ⊢
  split_ifs at hn with h
  · exact False.elim (hn rfl)
  · split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem single_node_monotone {I : ℕ} :
    MonotonePolicy (fun i : Fin I => i) (guardedPolicy (I:=I) (J:=1)) := by
  constructor
  · intro s w j hj
    have hj0 : j=0 := Subsingleton.elim _ _
    subst j
    unfold guardedPolicy at hj ⊢
    split_ifs at hj with h
    · have hi : 0 < s.x w 0+1 := by linarith [h.2]
      simp [h.1,hi]
  · intro s w j hj
    have hj0 : j=0 := Subsingleton.elim _ _
    subst j
    have hc : 0 < s.c 0+1 := by linarith
    simp [guardedPolicy,hj,hc]

theorem two_product_needs_two_iterations :
    cache id (guardedPolicy (I:=2) (J:=1)) twoProductState alternatingOrder id 1 1=some 0 ∧
    cache id (guardedPolicy (I:=2) (J:=1)) twoProductState alternatingOrder id 2 1=none ∧
    seqAct id (guardedPolicy (I:=2) (J:=1)) twoProductState alternatingOrder 1=none := by
  norm_num [cache,System.cache,System.procAct,System.procState,seqAct,System.seqAct,System.seqState,
    foSystem,orderProc,alternatingOrder,guardedPolicy,twoProductState,step,Feasible]
end Queelius.Fulfillment.Controls

end

section
noncomputable section
namespace Queelius.Fulfillment
open PicardFO.Fulfill

variable {I J : ℕ} {Ω ι : Type*}

theorem sequential_capacity_antitone (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (j : Fin J) :
    Antitone (fun t => (seqState prod π s₁ ω t).c j) := by
  apply antitone_nat_of_succ_le
  intro t
  change (step (seqState prod π s₁ ω t) (prod (ω t)) (seqAct prod π s₁ ω t)).c j ≤ _
  rw [step_capacity]
  exact sub_le_self _ (debit_nonneg _ _)

theorem Q_mono (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) {t u : ℕ} (htu : t ≤ u) : Q prod π s₁ ω t ⊆ Q prod π s₁ ω u := by
  intro j hj
  simp only [Q,Finset.mem_filter,Finset.mem_univ,true_and] at hj ⊢
  obtain ⟨hi,v,hvt,hv⟩:=hj
  exact ⟨hi,v,hvt.trans_le htu,hv⟩

theorem Q_succ_iff (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (t : ℕ) (j : Fin J) :
    j ∈ Q prod π s₁ ω (t+1) ↔ 0 < s₁.c j ∧ (seqState prod π s₁ ω t).c j ≤ 0 := by
  simp only [Q,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hi,u,hu,hc⟩
    exact ⟨hi,(sequential_capacity_antitone prod π s₁ ω j (by omega)).trans hc⟩
  · rintro ⟨hi,hc⟩
    exact ⟨hi,t,by omega,hc⟩

theorem seq_inventory_le_initial (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (t : ℕ) (i : Fin I) (j : Fin J) :
    (seqState prod π s₁ ω t).x i j ≤ s₁.x i j := by
  obtain ⟨n,hn,he⟩:=sequential_inventory_count prod π s₁ ω t i j
  rw [he]
  exact sub_le_self _ (Nat.cast_nonneg n)

theorem proc_capacity_le_initial (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι) (α : ℕ → Option (Fin J))
    (m : ι) (t : ℕ) (j : Fin J) :
    (procState prod π s₁ ω own α m t).c j ≤ s₁.c j := by
  obtain ⟨n,hn,he⟩:=process_capacity_count prod π s₁ ω own α m t j
  rw [he]
  exact sub_le_self _ (Nat.cast_nonneg n)

theorem capacity_of_inventory_order (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι) (α : ℕ → Option (Fin J))
    (m : ι) (t : ℕ) (j : Fin J)
    (h : ∀ i,(seqState prod π s₁ ω t).x i j ≤ (procState prod π s₁ ω own α m t).x i j) :
    (seqState prod π s₁ ω t).c j ≤ (procState prod π s₁ ω own α m t).c j := by
  have hs:=sequential_balance prod π s₁ ω t j
  have hp:=process_balance prod π s₁ ω own α m t j
  have hi:=Finset.sum_le_sum (s:=Finset.univ) (fun i _ => h i)
  linarith
end Queelius.Fulfillment

end

section
noncomputable section
open PicardFO.Fulfill

theorem fixed_point_clause {I J : ℕ} {Ω ι : Type*} (prod : Ω → Fin I)
    (π : State I J → Ω → Option (Fin J)) (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι)
    (hfeas : PolicyFeasible prod π) (_h1 : InvIndep prod π) (_h2 : Consistent prod π)
    (_h3 : MonotonePolicy prod π) (T : ℕ) :
    (∀ k : ℕ, 1 ≤ k →
        (∀ t < T, cache prod π s₁ ω own k t = cache prod π s₁ ω own (k - 1) t) →
        ∀ t < T, cache prod π s₁ ω own k t = seqAct prod π s₁ ω t) := by
  intro k hk he
  cases k with
  | zero => omega
  | succ k =>
    simp only [Nat.succ_sub_one] at he
    exact Queelius.Fulfillment.cache_fixed_point_correct (foSystem I J Ω prod) π hfeas
      s₁ ω (orderProc prod ω own) k T he

end

section
noncomputable section
namespace Queelius.Fulfillment
open PicardFO.Fulfill
variable {I J : ℕ} {Ω ι : Type*}

theorem decision_from_inventory_order (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι) (α : ℕ → Option (Fin J))
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π) (m : ι) (t : ℕ)
    (hdom : ∀ i j,j ∉ Q prod π s₁ ω t →
      (seqState prod π s₁ ω t).x i j ≤ (procState prod π s₁ ω own α m t).x i j) :
    π (procState prod π s₁ ω own α m t) (ω t)=seqAct prod π s₁ ω t ∨
      ∃ j,π (procState prod π s₁ ω own α m t) (ω t)=some j ∧
        (j ∈ Q prod π s₁ ω (t+1) ∨
         (j ∉ Q prod π s₁ ω (t+1) ∧
          (seqState prod π s₁ ω t).x (prod (ω t)) j <
          (procState prod π s₁ ω own α m t).x (prod (ω t)) j)) := by
  classical
  let B : Finset (Fin J) := Finset.univ.filter (fun j => (seqState prod π s₁ ω t).c j ≤ 0)
  have hbad (j : Fin J) : j ∈ B ↔ (seqState prod π s₁ ω t).c j ≤ 0 := by simp [B]
  have hpos (j : Fin J) (hj : j ∉ B) : 0 < (seqState prod π s₁ ω t).c j := by
    exact lt_of_not_ge (fun h => hj ((hbad j).mpr h))
  have hnot (j : Fin J) (hj : j ∉ B) : j ∉ Q prod π s₁ ω t := by
    intro hq
    have hh := (Q_succ_iff prod π s₁ ω t j).mp (Q_mono prod π s₁ ω (Nat.le_succ t) hq)
    exact not_lt_of_ge hh.2 (hpos j hj)
  have hc (j : Fin J) (hj : j ∉ B) :
      ∃ n : ℕ,(procState prod π s₁ ω own α m t).c j=(seqState prod π s₁ ω t).c j+n := by
    obtain ⟨a,ha,hea⟩:=sequential_capacity_count prod π s₁ ω t j
    obtain ⟨b,hb,heb⟩:=process_capacity_count prod π s₁ ω own α m t j
    exact integral_gap_nat _ _ _ a b hea heb
      (capacity_of_inventory_order prod π s₁ ω own α m t j (fun i => hdom i j (hnot j hj)))
  have hx (j : Fin J) (hj : j ∉ B) :
      ∃ n : ℕ,(procState prod π s₁ ω own α m t).x (prod (ω t)) j=
        (seqState prod π s₁ ω t).x (prod (ω t)) j+n := by
    obtain ⟨a,ha,hea⟩:=sequential_inventory_count prod π s₁ ω t (prod (ω t)) j
    obtain ⟨b,hb,heb⟩:=process_inventory_count prod π s₁ ω own α m t (prod (ω t)) j
    exact integral_gap_nat _ _ _ a b hea heb (hdom _ j (hnot j hj))
  have he:=exchange prod π hfeas h1 h2 h3 (seqState prod π s₁ ω t)
    (procState prod π s₁ ω own α m t) (ω t) B (fun j hj => (hbad j).mp hj) hpos hc hx
  rcases he with he | ⟨j,hj,hcase⟩
  · exact Or.inl he
  · refine Or.inr ⟨j,hj,?_⟩
    rcases hcase with hb | ⟨hb,hmore⟩
    · left
      apply (Q_succ_iff prod π s₁ ω t j).mpr
      have hf:=hfeas (procState prod π s₁ ω own α m t) (ω t)
      rw [hj] at hf
      exact ⟨hf.1.trans_le (proc_capacity_le_initial prod π s₁ ω own α m t j),(hbad j).mp hb⟩
    · by_cases hq : j ∈ Q prod π s₁ ω (t+1)
      · exact Or.inl hq
      · exact Or.inr ⟨hq,hmore⟩

theorem owner_next_inventory (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι) (α : ℕ → Option (Fin J))
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π) (m : ι) (t : ℕ) (hm : own (prod (ω t))=m)
    (hdom : ∀ i j,j ∉ Q prod π s₁ ω t →
      (seqState prod π s₁ ω t).x i j ≤ (procState prod π s₁ ω own α m t).x i j)
    (j : Fin J) (hj : j ∉ Q prod π s₁ ω (t+1)) :
    (seqState prod π s₁ ω (t+1)).x (prod (ω t)) j ≤
      (procState prod π s₁ ω own α m (t+1)).x (prod (ω t)) j := by
  classical
  have hjt : j ∉ Q prod π s₁ ω t := fun h => hj (Q_mono prod π s₁ ω (Nat.le_succ t) h)
  have hold:=hdom (prod (ω t)) j hjt
  have ha : procAct prod π ω own α m (procState prod π s₁ ω own α m t) t=
      π (procState prod π s₁ ω own α m t) (ω t) := by
    simp [procAct,System.procAct,orderProc,hm]
  change (step (seqState prod π s₁ ω t) (prod (ω t)) (seqAct prod π s₁ ω t)).x (prod (ω t)) j ≤
    (step (procState prod π s₁ ω own α m t) (prod (ω t))
      (procAct prod π ω own α m (procState prod π s₁ ω own α m t) t)).x (prod (ω t)) j
  rw [step_inventory,step_inventory,ha]
  simp only [ite_true]
  rcases decision_from_inventory_order prod π s₁ ω own α hfeas h1 h2 h3 m t hdom with he | ⟨k,hk,hcase⟩
  · rw [he]
    linarith
  · by_cases hkj : k=j
    · subst k
      rcases hcase with hbad | ⟨hnot,hmore⟩
      · exact False.elim (hj hbad)
      · obtain ⟨a,ha,hea⟩:=sequential_inventory_count prod π s₁ ω t (prod (ω t)) j
        obtain ⟨b,hb,heb⟩:=process_inventory_count prod π s₁ ω own α m t (prod (ω t)) j
        have hgap:=integral_gap_at_least_one _ _ _ a b hea heb hmore
        rw [hk]
        simp only [debit,ite_true]
        have hd:=debit_nonneg (seqAct prod π s₁ ω t) j
        unfold debit at hd
        linarith
    · rw [hk]
      have hz : debit (some k) j=0 := by simp [debit,hkj]
      rw [hz,sub_zero]
      exact (sub_le_self _ (debit_nonneg _ _)).trans hold
end Queelius.Fulfillment

end

section
noncomputable section
namespace Queelius.Fulfillment
open PicardFO.Fulfill
variable {I J : ℕ} {Ω ι : Type*}

theorem process_capacity_antitone (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι) (α : ℕ → Option (Fin J)) (m : ι) (j : Fin J) :
    Antitone (fun t => (procState prod π s₁ ω own α m t).c j) := by
  apply antitone_nat_of_succ_le
  intro t
  change (step (procState prod π s₁ ω own α m t) (prod (ω t))
    (procAct prod π ω own α m (procState prod π s₁ ω own α m t) t)).c j ≤ _
  rw [step_capacity]
  exact sub_le_self _ (debit_nonneg _ _)

theorem process_depleted_nodes (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι) (hfeas : PolicyFeasible prod π)
    (k t : ℕ) (m : ι) (hbound : (Q prod π s₁ ω (t+1)).card ≤ k)
    (hcache : ∀ u,(Q prod π s₁ ω (u+1)).card < k →
      cache prod π s₁ ω own k u=seqAct prod π s₁ ω u)
    (j : Fin J) (hj : j ∈ Q prod π s₁ ω (t+1)) :
    (procState prod π s₁ ω own (cache prod π s₁ ω own k) m t).c j ≤ 0 := by
  classical
  have hjc := (Q_succ_iff prod π s₁ ω t j).mp hj
  have hex : ∃ u : ℕ,(seqState prod π s₁ ω u).c j ≤ 0 := ⟨t,hjc.2⟩
  let u:=Nat.find hex
  have hut : u ≤ t := Nat.find_min' hex hjc.2
  have huc : (seqState prod π s₁ ω u).c j ≤ 0 := Nat.find_spec hex
  have hpre (v : ℕ) (hv : v < u) : cache prod π s₁ ω own k v=seqAct prod π s₁ ω v := by
    apply hcache
    have hnot : j ∉ Q prod π s₁ ω (v+1) := by
      intro h
      have hvc := ((Q_succ_iff prod π s₁ ω v j).mp h).2
      exact Nat.find_min hex hv hvc
    have hsub : Q prod π s₁ ω (v+1) ⊆ Q prod π s₁ ω (t+1) :=
      Q_mono prod π s₁ ω (by omega)
    have hstrict : Q prod π s₁ ω (v+1) ⊂ Q prod π s₁ ω (t+1) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub,fun he => hnot (he ▸ hj)⟩
    exact (Finset.card_lt_card hstrict).trans_le hbound
  have he : procState prod π s₁ ω own (cache prod π s₁ ω own k) m u=seqState prod π s₁ ω u :=
    replay_correct_prefix (foSystem I J Ω prod) π hfeas s₁ ω (orderProc prod ω own) _ m u hpre
  have hmono:=process_capacity_antitone prod π s₁ ω own (cache prod π s₁ ω own k) m j hut
  dsimp only at hmono
  rw [he] at hmono
  exact hmono.trans huc

theorem owner_action_is_cache (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι) (k t : ℕ) (m : ι)
    (hm : own (prod (ω t))=m) :
    procAct prod π ω own (cache prod π s₁ ω own k) m
      (procState prod π s₁ ω own (cache prod π s₁ ω own k) m t) t =
      cache prod π s₁ ω own (k+1) t := by
  subst m
  rfl

theorem owner_inventory_prefix (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι) (k t : ℕ) (i : Fin I)
    (hpre : ∀ u,u < t → prod (ω u)=i → cache prod π s₁ ω own (k+1) u=seqAct prod π s₁ ω u)
    (j : Fin J) :
    (procState prod π s₁ ω own (cache prod π s₁ ω own k) (own i) t).x i j=
      (seqState prod π s₁ ω t).x i j := by
  classical
  induction t with
  | zero => rfl
  | succ t ih =>
    have hi:=ih (fun u hu hp => hpre u (by omega) hp)
    change (step (procState prod π s₁ ω own (cache prod π s₁ ω own k) (own i) t) (prod (ω t))
      (procAct prod π ω own (cache prod π s₁ ω own k) (own i)
        (procState prod π s₁ ω own (cache prod π s₁ ω own k) (own i) t) t)).x i j=
      (step (seqState prod π s₁ ω t) (prod (ω t)) (seqAct prod π s₁ ω t)).x i j
    rw [step_inventory,step_inventory,hi]
    by_cases hp : prod (ω t)=i
    · have hm : own (prod (ω t))=own i := congrArg own hp
      rw [owner_action_is_cache prod π s₁ ω own k t (own i) hm,hpre t (by omega) hp]
    · simp only [Ne.symm hp,ite_false]
end Queelius.Fulfillment

end

section
noncomputable section
namespace Queelius.Fulfillment
open PicardFO.Fulfill
variable {I J : ℕ} {Ω ι : Type*}

theorem inventory_from_outsiders (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι) (α : ℕ → Option (Fin J))
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π)
    (hout : ∀ t m i,own i ≠ m → ∀ j,j ∉ Q prod π s₁ ω t →
      (seqState prod π s₁ ω t).x i j ≤ (procState prod π s₁ ω own α m t).x i j) :
    ∀ t m i j,j ∉ Q prod π s₁ ω t →
      (seqState prod π s₁ ω t).x i j ≤ (procState prod π s₁ ω own α m t).x i j := by
  intro t
  induction t with
  | zero => intro m i j hj; rfl
  | succ t ih =>
    intro m i j hj
    have hjt : j ∉ Q prod π s₁ ω t := fun h => hj (Q_mono prod π s₁ ω (Nat.le_succ t) h)
    by_cases hm : own i=m
    · by_cases hi : i=prod (ω t)
      · subst i
        exact owner_next_inventory prod π s₁ ω own α hfeas h1 h2 h3 m t hm
          (fun a b hb => ih m a b hb) j hj
      · change (step (seqState prod π s₁ ω t) (prod (ω t)) (seqAct prod π s₁ ω t)).x i j ≤
          (step (procState prod π s₁ ω own α m t) (prod (ω t))
            (procAct prod π ω own α m (procState prod π s₁ ω own α m t) t)).x i j
        rw [step_inventory,step_inventory]
        simp only [hi,ite_false,sub_zero]
        exact ih m i j hjt
    · exact hout (t+1) m i hm j hj

theorem inventory_dominance (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι)
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π) (k : ℕ) :
    ∀ t m i j,j ∉ Q prod π s₁ ω t →
      (seqState prod π s₁ ω t).x i j ≤
        (procState prod π s₁ ω own (cache prod π s₁ ω own k) m t).x i j := by
  induction k with
  | zero =>
    apply inventory_from_outsiders prod π s₁ ω own _ hfeas h1 h2 h3
    intro t m i hm j hj
    rw [initial_outsider_inventory prod π s₁ ω own m i hm t j]
    exact seq_inventory_le_initial prod π s₁ ω t i j
  | succ k ih =>
    apply inventory_from_outsiders prod π s₁ ω own _ hfeas h1 h2 h3
    intro t m i hm j hj
    exact (ih t (own i) i j hj).trans (later_outsider_inventory prod π s₁ ω own m i hm k t j)

theorem state_dominance (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι)
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π) (k t : ℕ) (m : ι) (j : Fin J) (hj : j ∉ Q prod π s₁ ω t) :
    (∀ i,(seqState prod π s₁ ω t).x i j ≤
      (procState prod π s₁ ω own (cache prod π s₁ ω own k) m t).x i j) ∧
    (seqState prod π s₁ ω t).c j ≤
      (procState prod π s₁ ω own (cache prod π s₁ ω own k) m t).c j := by
  have hi:=fun i => inventory_dominance prod π s₁ ω own hfeas h1 h2 h3 k t m i j hj
  exact ⟨hi,capacity_of_inventory_order prod π s₁ ω own _ m t j hi⟩

theorem decision_containment (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι)
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π) (k t : ℕ) (m : ι) :
    π (procState prod π s₁ ω own (cache prod π s₁ ω own k) m t) (ω t)=seqAct prod π s₁ ω t ∨
      ∃ j,π (procState prod π s₁ ω own (cache prod π s₁ ω own k) m t) (ω t)=some j ∧
        (j ∈ Q prod π s₁ ω (t+1) ∨
         (j ∉ Q prod π s₁ ω (t+1) ∧
          (seqState prod π s₁ ω t).x (prod (ω t)) j <
          (procState prod π s₁ ω own (cache prod π s₁ ω own k) m t).x (prod (ω t)) j)) :=
  decision_from_inventory_order prod π s₁ ω own _ hfeas h1 h2 h3 m t
    (fun i j hj => inventory_dominance prod π s₁ ω own hfeas h1 h2 h3 k t m i j hj)
end Queelius.Fulfillment

end

section
noncomputable section
namespace Queelius.Fulfillment
open PicardFO.Fulfill
variable {I J : ℕ} {Ω ι : Type*}

theorem exhaustion_prefix (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι)
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π) (k : ℕ) :
    ∀ t,(Q prod π s₁ ω (t+1)).card < k → cache prod π s₁ ω own k t=seqAct prod π s₁ ω t := by
  classical
  induction k with
  | zero => intro t ht; omega
  | succ k ih =>
    intro t
    induction t using Nat.strong_induction_on with
    | h t iht =>
      intro ht
      have hpre (u : ℕ) (hu : u < t) : cache prod π s₁ ω own (k+1) u=seqAct prod π s₁ ω u := by
        apply iht u hu
        have hc:=Finset.card_le_card (Q_mono prod π s₁ ω (show u+1 ≤ t+1 by omega))
        omega
      have hrow (j : Fin J) :
          (procState prod π s₁ ω own (cache prod π s₁ ω own k) (own (prod (ω t))) t).x (prod (ω t)) j=
          (seqState prod π s₁ ω t).x (prod (ω t)) j :=
        owner_inventory_prefix prod π s₁ ω own k t (prod (ω t)) (fun u hu _ => hpre u hu) j
      have hcache : cache prod π s₁ ω own (k+1) t=
          π (procState prod π s₁ ω own (cache prod π s₁ ω own k) (own (prod (ω t))) t) (ω t) :=
        cache_owner_action (foSystem I J Ω prod) π s₁ ω (orderProc prod ω own) k t
      rw [hcache]
      rcases decision_containment prod π s₁ ω own hfeas h1 h2 h3 k t (own (prod (ω t))) with he | ⟨j,hj,hcase⟩
      · exact he
      · rcases hcase with hbad | ⟨hnot,hmore⟩
        · have hcap:=process_depleted_nodes prod π s₁ ω own hfeas k t (own (prod (ω t)))
            (by omega) ih j hbad
          have hf:=hfeas (procState prod π s₁ ω own (cache prod π s₁ ω own k) (own (prod (ω t))) t) (ω t)
          rw [hj] at hf
          exact False.elim (not_lt_of_ge hcap hf.1)
        · rw [hrow j] at hmore
          exact False.elim (lt_irrefl _ hmore)

theorem exhaustion_horizon (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι)
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π) (T k : ℕ) (hk : (Q prod π s₁ ω T).card+1 ≤ k) :
    ∀ t,t < T → cache prod π s₁ ω own k t=seqAct prod π s₁ ω t := by
  intro t ht
  apply exhaustion_prefix prod π s₁ ω own hfeas h1 h2 h3 k t
  have hc:=Finset.card_le_card (Q_mono prod π s₁ ω (show t+1 ≤ T by omega))
  omega
end Queelius.Fulfillment

end

section
namespace PicardFO.Fulfill

/-- Eqs. (8)–(10) (p. 13), the policy exchange step: let `s` be a state whose non-positive
capacity nodes are exactly `Qs`, and let `s'` have, at every node `j ∉ Qs`, a capacity and an
inventory of product `i = prod w` exceeding those of `s` by whole units. Then `π s' w` is
`π s w`, or a node of `Qs`, or a node outside `Qs` where `s'` holds strictly more inventory of
`i` than `s`. -/
theorem eq_8_to_10_exchange {I J : ℕ} {Ω : Type*} (prod : Ω → Fin I)
    (π : State I J → Ω → Option (Fin J))
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π)
    (s s' : State I J) (w : Ω) (Qs : Finset (Fin J))
    (hQ : ∀ j ∈ Qs, s.c j ≤ 0) (hQc : ∀ j ∉ Qs, 0 < s.c j)
    (hc : ∀ j ∉ Qs, ∃ n : ℕ, s'.c j = s.c j + n)
    (hx : ∀ j ∉ Qs, ∃ n : ℕ, s'.x (prod w) j = s.x (prod w) j + n) :
    π s' w = π s w ∨
      ∃ j, π s' w = some j ∧ (j ∈ Qs ∨ (j ∉ Qs ∧ s.x (prod w) j < s'.x (prod w) j)) := by
  exact Queelius.Fulfillment.exchange prod π hfeas h1 h2 h3 s s' w Qs hQ hQc hc hx

end PicardFO.Fulfill

namespace PicardFO.Fulfill

/-- Eq. (5) (p. 13): when the process `m` owning the product of order `t` evaluates `π` at
order `t` (in any iteration, with cache `cache … k`), its decision is the sequential one, or a
node of `Q_{t+1}` (exhausted in the sequential run by the state before order `t`), or a node
outside `Q_{t+1}` where the process holds strictly more inventory of that product than the
sequential run before order `t`. -/
theorem eq_5 {I J : ℕ} {Ω ι : Type*} (prod : Ω → Fin I)
    (π : State I J → Ω → Option (Fin J)) (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι)
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π)
    (k t : ℕ) (m : ι) (hm : own (prod (ω t)) = m) (s : State I J)
    (hs : s = procState prod π s₁ ω own (cache prod π s₁ ω own k) m t) :
    π s (ω t) = seqAct prod π s₁ ω t ∨
      ∃ j, π s (ω t) = some j ∧
        (j ∈ Q prod π s₁ ω (t + 1) ∨
          (j ∉ Q prod π s₁ ω (t + 1) ∧
            (seqState prod π s₁ ω t).x (prod (ω t)) j < s.x (prod (ω t)) j)) := by
  subst s
  exact Queelius.Fulfillment.decision_containment prod π s₁ ω own hfeas h1 h2 h3 k t m

end PicardFO.Fulfill

namespace PicardFO.Fulfill

/-- Lemma A.1 (p. 12): in every iteration and for every process, at every node `j` not in
`Q_t`, the inventories of every product and the capacity of the process's state after the first
`t` orders are at least the sequential ones. -/
theorem lemma_A_1 {I J : ℕ} {Ω ι : Type*} (prod : Ω → Fin I)
    (π : State I J → Ω → Option (Fin J)) (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι)
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π)
    (k : ℕ) (m : ι) (t : ℕ) (j : Fin J) (hj : j ∉ Q prod π s₁ ω t) :
    (∀ i, (seqState prod π s₁ ω t).x i j ≤
        (procState prod π s₁ ω own (cache prod π s₁ ω own k) m t).x i j) ∧
    (seqState prod π s₁ ω t).c j ≤
        (procState prod π s₁ ω own (cache prod π s₁ ω own k) m t).c j := by
  exact Queelius.Fulfillment.state_dominance prod π s₁ ω own hfeas h1 h2 h3 k t m j hj

end PicardFO.Fulfill

namespace PicardFO.Fulfill

/-- Eq. (3) (p. 12), corrected (`t ≤ τ̃_k` → `t < τ̃_k`): in iteration `k`, the cached action of
order `t` is the sequential one whenever fewer than `k` nodes are in `Q_{t+1}`. -/
theorem eq_3 {I J : ℕ} {Ω ι : Type*} (prod : Ω → Fin I)
    (π : State I J → Ω → Option (Fin J)) (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι)
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π)
    (k t : ℕ) (h : (Q prod π s₁ ω (t + 1)).card < k) :
    cache prod π s₁ ω own k t = seqAct prod π s₁ ω t := by
  exact Queelius.Fulfillment.exhaustion_prefix prod π s₁ ω own hfeas h1 h2 h3 k t h

end PicardFO.Fulfill

namespace PicardFO.Fulfill

/-- Theorem 3.2 (p. 6), corrected (a node runs out when its capacity is no longer positive):
for a feasible policy satisfying Assumptions 1–3, the cache of Algorithm 1 (partition by
products) equals the sequential actions on the first `T` orders in every iteration
`k ≥ |Q_T| + 1`; and whenever the convergence test of line 10 succeeds at an iteration
`k ≥ 1`, the returned cache is the sequential one. -/
theorem theorem_3_2 {I J : ℕ} {Ω ι : Type*} (prod : Ω → Fin I)
    (π : State I J → Ω → Option (Fin J)) (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι)
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π) (T : ℕ) :
    (∀ k : ℕ, (Q prod π s₁ ω T).card + 1 ≤ k →
        ∀ t < T, cache prod π s₁ ω own k t = seqAct prod π s₁ ω t) ∧
    (∀ k : ℕ, 1 ≤ k →
        (∀ t < T, cache prod π s₁ ω own k t = cache prod π s₁ ω own (k - 1) t) →
        ∀ t < T, cache prod π s₁ ω own k t = seqAct prod π s₁ ω t) := by
  exact ⟨fun k hk => Queelius.Fulfillment.exhaustion_horizon prod π s₁ ω own hfeas h1 h2 h3 T k hk,
    fixed_point_clause prod π s₁ ω own hfeas h1 h2 h3 T⟩

end PicardFO.Fulfill

end

section
noncomputable section
universe audit_u0 audit_u1
theorem submission_primary_solution : (
∀ {I J : Nat} {Ω : Type audit_u0} {ι : Type audit_u1} (prod : Ω → Fin I)
  (π : PicardFO.Fulfill.State I J → Ω → Option (Fin J)) (s₁ : PicardFO.Fulfill.State I J) (ω : Nat → Ω)
  (own : Fin I → ι),
  @PicardFO.Fulfill.PolicyFeasible I J Ω prod π →
    @PicardFO.Fulfill.InvIndep I J Ω prod π →
      @PicardFO.Fulfill.Consistent I J Ω prod π →
        @PicardFO.Fulfill.MonotonePolicy I J Ω prod π →
          ∀ (T : Nat),
            And
              (∀ (k : Nat),
                @LE.le Nat instLENat
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@Finset.card (Fin J) (@PicardFO.Fulfill.Q I J Ω prod π s₁ ω T))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    k →
                  ∀ (t : Nat),
                    @LT.lt Nat instLTNat t T →
                      @Eq (Option (Fin J)) (@PicardFO.Fulfill.cache I J Ω ι prod π s₁ ω own k t)
                        (@PicardFO.Fulfill.seqAct I J Ω prod π s₁ ω t))
              (∀ (k : Nat),
                @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k →
                  (∀ (t : Nat),
                      @LT.lt Nat instLTNat t T →
                        @Eq (Option (Fin J)) (@PicardFO.Fulfill.cache I J Ω ι prod π s₁ ω own k t)
                          (@PicardFO.Fulfill.cache I J Ω ι prod π s₁ ω own
                            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) k
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            t)) →
                    ∀ (t : Nat),
                      @LT.lt Nat instLTNat t T →
                        @Eq (Option (Fin J)) (@PicardFO.Fulfill.cache I J Ω ι prod π s₁ ω own k t)
                          (@PicardFO.Fulfill.seqAct I J Ω prod π s₁ ω t))
) := @PicardFO.Fulfill.theorem_3_2

end

universe audit_u0

theorem solution : (
  ∀ {I J : Nat} {Ω : Type audit_u0} (prod : Ω → Fin I) (π : PicardFO.Fulfill.State I J → Ω → Option (Fin J)),
    @PicardFO.Fulfill.PolicyFeasible I J Ω prod π →
      @PicardFO.Fulfill.InvIndep I J Ω prod π →
        @PicardFO.Fulfill.Consistent I J Ω prod π →
          @PicardFO.Fulfill.MonotonePolicy I J Ω prod π →
            ∀ (s s' : PicardFO.Fulfill.State I J) (w : Ω) (Qs : Finset (Fin J)),
              (∀ (j : Fin J),
                  @Membership.mem (Fin J) (Finset (Fin J))
                      (@SetLike.instMembership (Finset (Fin J)) (Fin J) (@Finset.instSetLike (Fin J))) Qs j →
                    @LE.le Real Real.instLE (@PicardFO.Fulfill.State.c I J s j)
                      (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))) →
                (∀ (j : Fin J),
                    Not
                        (@Membership.mem (Fin J) (Finset (Fin J))
                          (@SetLike.instMembership (Finset (Fin J)) (Fin J) (@Finset.instSetLike (Fin J))) Qs j) →
                      @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                        (@PicardFO.Fulfill.State.c I J s j)) →
                  (∀ (j : Fin J),
                      Not
                          (@Membership.mem (Fin J) (Finset (Fin J))
                            (@SetLike.instMembership (Finset (Fin J)) (Fin J) (@Finset.instSetLike (Fin J))) Qs j) →
                        @Exists Nat fun (n : Nat) =>
                          @Eq Real (@PicardFO.Fulfill.State.c I J s' j)
                            (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@PicardFO.Fulfill.State.c I J s j)
                              (@Nat.cast Real Real.instNatCast n))) →
                    (∀ (j : Fin J),
                        Not
                            (@Membership.mem (Fin J) (Finset (Fin J))
                              (@SetLike.instMembership (Finset (Fin J)) (Fin J) (@Finset.instSetLike (Fin J))) Qs j) →
                          @Exists Nat fun (n : Nat) =>
                            @Eq Real (@PicardFO.Fulfill.State.x I J s' (prod w) j)
                              (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
                                (@PicardFO.Fulfill.State.x I J s (prod w) j) (@Nat.cast Real Real.instNatCast n))) →
                      Or (@Eq (Option (Fin J)) (π s' w) (π s w))
                        (@Exists (Fin J) fun (j : Fin J) =>
                          And (@Eq (Option (Fin J)) (π s' w) (@Option.some (Fin J) j))
                            (Or
                              (@Membership.mem (Fin J) (Finset (Fin J))
                                (@SetLike.instMembership (Finset (Fin J)) (Fin J) (@Finset.instSetLike (Fin J))) Qs j)
                              (And
                                (Not
                                  (@Membership.mem (Fin J) (Finset (Fin J))
                                    (@SetLike.instMembership (Finset (Fin J)) (Fin J) (@Finset.instSetLike (Fin J))) Qs
                                    j))
                                (@LT.lt Real Real.instLT (@PicardFO.Fulfill.State.x I J s (prod w) j)
                                  (@PicardFO.Fulfill.State.x I J s' (prod w) j)))))
) := @PicardFO.Fulfill.eq_8_to_10_exchange
