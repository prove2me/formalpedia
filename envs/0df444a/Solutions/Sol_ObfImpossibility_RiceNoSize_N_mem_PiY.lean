-- Prove2me | solution 1 for ObfImpossibility.RiceNoSize.N_mem_PiY
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T14:46:41.031255+00:00
-- url     : https://prove2.me/submissions/aa361feb-91d1-4bf7-8838-9a1be751007c

import Mathlib
import Definitions.Def_ObfImpossibility_RiceNoSize_ProofObjects
open ObfImpossibility.RiceNoSize Turing
namespace RiceDelay
inductive St (n r : ℕ) where
  | count : Fin (n+2) → St n r
  | scan : St n r
  | back : Fin (r+1) → St n r
  | write : Fin r → St n r
  deriving DecidableEq, Fintype
instance (n r : ℕ) : Inhabited (St n r) := ⟨St.count 0⟩
noncomputable def enc (n r : ℕ) : St n r ≃ Fin (Fintype.card (St n r) - 1 + 1) := by
  have h : Fintype.card (St n r) = Fintype.card (St n r) - 1 + 1 := by
    have := Fintype.card_pos (α := St n r)
    omega
  let e := Fintype.equivFinOfCardEq h
  exact e.trans (Equiv.swap (e (St.count 0)) 0)
@[simp] lemma enc_start (n r : ℕ) : enc n r (St.count 0) = 0 := by
  simp [enc]

def trans (n r : ℕ) : St n r → Bool → Option (St n r × TM0.Stmt Bool)
  | .count k, a =>
      if h : k.val < n+1 then
        if a then some (.count ⟨k.val+1,by omega⟩,.move .right) else none
      else if a then some (.scan,.move .right) else some (.back 0,.write true)
  | .scan, a => if a then some (.scan,.move .right) else some (.back ⟨r,by omega⟩,.write false)
  | .back j, _ => if h : j.val = 0 then none
      else some (.write ⟨j.val-1,by have := j.isLt; omega⟩,.move .left)
  | .write j, _ => some (.back ⟨j.val,by have := j.isLt; omega⟩,.write true)
noncomputable def mach (n r : ℕ) : Machine where
  q := Fintype.card (St n r)-1
  δ := fun s a => (trans n r ((enc n r).symm s) a).map (fun p => (enc n r p.1,p.2))
noncomputable def cfg {n r : ℕ} (s : St n r) (L R : ListBlank Bool) :
    TM0.Cfg Bool (Fin ((mach n r).q+1)) := ⟨enc n r s,Tape.mk' L R⟩
def ones (k : ℕ) : ListBlank Bool := ListBlank.mk (List.replicate k true)
@[simp] lemma ones_head_zero : (ones 0).head = false := rfl
@[simp] lemma ones_head_succ (k : ℕ) : (ones (k+1)).head = true := by simp [ones,List.replicate_succ]
@[simp] lemma ones_tail_succ (k : ℕ) : (ones (k+1)).tail = ones k := by simp [ones,List.replicate_succ]
@[simp] lemma ones_cons (k : ℕ) : (ones k).cons true = ones (k+1) := by simp [ones,List.replicate_succ]

lemma count_zero (n r k : ℕ) (hk : k ≤ n) (L : ListBlank Bool) :
    TM0.step (mach n r).δ (cfg (.count ⟨k,by omega⟩) L (ones 0)) = none := by
  simp [TM0.step,mach,cfg,trans,show k<n+1 by omega]
lemma count_succ (n r k : ℕ) (hk : k ≤ n) (L : ListBlank Bool) (x : ℕ) :
    TM0.step (mach n r).δ (cfg (.count ⟨k,by omega⟩) L (ones (x+1))) =
      some (cfg (.count ⟨k+1,by omega⟩) (L.cons true) (ones x)) := by
  simp [TM0.step,mach,cfg,trans,show k<n+1 by omega]
lemma edge_zero (n r : ℕ) (L : ListBlank Bool) :
    TM0.step (mach n r).δ (cfg (.count ⟨n+1,by omega⟩) L (ones 0)) =
      some (cfg (.back 0) L (ones 1)) := by
  simp [TM0.step,mach,cfg,trans,ones,List.replicate_succ]
lemma edge_succ (n r : ℕ) (L : ListBlank Bool) (x : ℕ) :
    TM0.step (mach n r).δ (cfg (.count ⟨n+1,by omega⟩) L (ones (x+1))) =
      some (cfg .scan (L.cons true) (ones x)) := by
  simp [TM0.step,mach,cfg,trans]
lemma scan_zero (n r : ℕ) (L : ListBlank Bool) :
    TM0.step (mach n r).δ (cfg .scan L (ones 0)) =
      some (cfg (.back ⟨r,by omega⟩) L (ones 0)) := by
  have hb : ListBlank.mk [false] = ListBlank.mk ([] : List Bool) :=
    ListBlank.cons_head_tail (ListBlank.mk ([] : List Bool))
  simp [TM0.step,mach,cfg,trans,ones,hb]
lemma scan_succ (n r : ℕ) (L : ListBlank Bool) (x : ℕ) :
    TM0.step (mach n r).δ (cfg .scan L (ones (x+1))) =
      some (cfg .scan (L.cons true) (ones x)) := by
  simp [TM0.step,mach,cfg,trans]
lemma back_zero (n r : ℕ) (L R : ListBlank Bool) :
    TM0.step (mach n r).δ (cfg (.back 0) L R) = none := by
  simp [TM0.step,mach,cfg,trans]
lemma back_succ (n r j : ℕ) (hj : j < r) (L R : ListBlank Bool) :
    TM0.step (mach n r).δ (cfg (.back ⟨j+1,by omega⟩) L R) =
      some (cfg (.write ⟨j,hj⟩) L.tail (R.cons L.head)) := by
  simp [TM0.step,mach,cfg,trans]
lemma write_step (n r j : ℕ) (hj : j < r) (L R : ListBlank Bool) :
    TM0.step (mach n r).δ (cfg (.write ⟨j,hj⟩) L R) =
      some (cfg (.back ⟨j,by omega⟩) L (R.tail.cons true)) := by
  simp [TM0.step,mach,cfg,trans]
lemma output_ones {n r : ℕ} (s : St n r) (L : ListBlank Bool) (k : ℕ) :
    output (cfg s L (ones k)) = k := by
  simp only [output,cfg,Tape.mk'_right₀]
  change ((List.replicate k true).takeWhile id).length = k
  simp
end RiceDelay

open ObfImpossibility.RiceNoSize Turing
namespace RiceDelay
lemma back_reaches (n r j : ℕ) (hj : j ≤ r) (L : ListBlank Bool) (k : ℕ) :
    ∃ L', StateTransition.Reaches (TM0.step (mach n r).δ)
      (cfg (.back ⟨j,by omega⟩) L (ones k)) (cfg (.back 0) L' (ones (k+j))) := by
  induction j generalizing L k with
  | zero => exact ⟨L,Relation.ReflTransGen.refl⟩
  | succ j ih =>
    obtain ⟨L',h⟩ := ih (by omega) L.tail (k+1)
    refine ⟨L',Relation.ReflTransGen.head (back_succ n r j (by omega) L (ones k)) ?_⟩
    refine Relation.ReflTransGen.head (b := cfg (.back ⟨j,by omega⟩) L.tail (ones (k+1))) ?_ ?_
    · simpa using write_step n r j (by omega) L.tail ((ones k).cons L.head)
    · simpa [StateTransition.Reaches,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

lemma scan_reaches (n r x : ℕ) (L : ListBlank Bool) :
    ∃ L', StateTransition.Reaches (TM0.step (mach n r).δ)
      (cfg .scan L (ones x)) (cfg (.back 0) L' (ones r)) := by
  induction x generalizing L with
  | zero =>
    obtain ⟨L',h⟩ := back_reaches n r r le_rfl L 0
    exact ⟨L',Relation.ReflTransGen.head (scan_zero n r L) (by simpa [StateTransition.Reaches] using h)⟩
  | succ x ih =>
    obtain ⟨L',h⟩ := ih (L.cons true)
    exact ⟨L',Relation.ReflTransGen.head (scan_succ n r L x) h⟩

lemma advance (n r j k : ℕ) (hk : k+j ≤ n+1) (L : ListBlank Bool) (x : ℕ) :
    ∃ L', StateTransition.Reaches (TM0.step (mach n r).δ)
      (cfg (.count ⟨k,by omega⟩) L (ones (x+j)))
      (cfg (.count ⟨k+j,by omega⟩) L' (ones x)) := by
  induction j generalizing k L with
  | zero => exact ⟨L,Relation.ReflTransGen.refl⟩
  | succ j ih =>
    obtain ⟨L',h⟩ := ih (k+1) (by omega) (L.cons true)
    refine ⟨L',Relation.ReflTransGen.head (count_succ n r k (by omega) L (x+j)) ?_⟩
    simpa [StateTransition.Reaches,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

lemma short_profile (n r t x k : ℕ) (hk : k+x ≤ n) (L : ListBlank Bool) :
    runFor (mach n r) t (cfg (.count ⟨k,by omega⟩) L (ones x)) =
      if t < x then none else some 0 := by
  induction t generalizing x k L with
  | zero =>
    cases x with
    | zero => simp [runFor,count_zero n r k (by omega),output_ones]
    | succ x => simp [runFor,count_succ n r k (by omega)]
  | succ t ih =>
    cases x with
    | zero => simp [runFor,count_zero n r k (by omega),output_ones]
    | succ x => simpa [runFor,count_succ n r k (by omega)] using ih x (k+1) (by omega) (L.cons true)
end RiceDelay

open ObfImpossibility.RiceNoSize Turing
namespace RiceDelay
lemma init_eq (n r x : ℕ) : TM0.init (input x) =
    cfg (r := r) (St.count (0 : Fin (n+2))) (ListBlank.mk []) (ones x) := by
  simp [TM0.init,cfg,input,ones,Tape.mk₁,Tape.mk₂]
  rfl
lemma fn_from_reaches (n r x k : ℕ) (s : St n r) (L : ListBlank Bool)
    (h : StateTransition.Reaches (TM0.step (mach n r).δ)
      (TM0.init (input x)) (cfg s L (ones k)))
    (hs : TM0.step (mach n r).δ (cfg s L (ones k)) = none) :
    fn (mach n r) x = Part.some k := by
  have hm := StateTransition.mem_eval.mpr ⟨h,hs⟩
  apply Part.eq_some_iff.mpr
  unfold fn TM0.eval
  apply (Part.mem_map_iff _).mpr
  refine ⟨(cfg s L (ones k)).Tape.right₀,?_,?_⟩
  · exact (Part.mem_map_iff _).mpr ⟨cfg s L (ones k),hm,rfl⟩
  · exact output_ones s L k
lemma fn_value (n r x : ℕ) : fn (mach n r) x = Nfun n r x := by
  by_cases hx : x ≤ n
  · obtain ⟨L,h⟩ := advance n r x 0 (by omega) (ListBlank.mk []) 0
    have hh : StateTransition.Reaches (TM0.step (mach n r).δ) (TM0.init (input x))
        (cfg (.count ⟨x,by omega⟩) L (ones 0)) := by simpa [init_eq] using h
    simpa [Nfun,hx] using fn_from_reaches n r x 0 _ L hh (count_zero n r x hx L)
  · by_cases he : x = n+1
    · subst x
      obtain ⟨L,h⟩ := advance n r (n+1) 0 (by omega) (ListBlank.mk []) 0
      have hh : StateTransition.Reaches (TM0.step (mach n r).δ) (TM0.init (input (n+1)))
          (cfg (.count ⟨n+1,by omega⟩) L (ones 0)) := by simpa [init_eq] using h
      have hh' := hh.tail (edge_zero n r L)
      simpa [Nfun] using fn_from_reaches n r (n+1) 1 _ L hh' (back_zero n r L (ones 1))
    · obtain ⟨L,h⟩ := advance n r (n+1) 0 (by omega) (ListBlank.mk []) (x-(n+1))
      have hd : x-(n+1) = (x-(n+2))+1 := by omega
      have hh : StateTransition.Reaches (TM0.step (mach n r).δ) (TM0.init (input x))
          (cfg (.count ⟨n+1,by omega⟩) L (ones ((x-(n+2))+1))) := by
        simpa [init_eq,hd,show x-(n+2)+1+(n+1)=x by omega] using h
      obtain ⟨L',hl⟩ := scan_reaches n r (x-(n+2)) (L.cons true)
      have hh' := (hh.tail (edge_succ n r L (x-(n+2)))).trans hl
      simpa [Nfun,hx,he] using fn_from_reaches n r x r _ L' hh' (back_zero n r L' (ones r))
end RiceDelay


private instance : Finite Turing.Dir :=
  Finite.of_surjective (fun b : Bool => if b then Turing.Dir.right else Turing.Dir.left)
    (by intro d; cases d <;> first | exact ⟨false,rfl⟩ | exact ⟨true,rfl⟩)

private instance : Finite (Turing.TM0.Stmt Bool) :=
  Finite.of_surjective
    (fun s : Sum Turing.Dir Bool => match s with
      | .inl d => Turing.TM0.Stmt.move d
      | .inr b => Turing.TM0.Stmt.write b)
    (by intro s; cases s with
        | move d => exact ⟨.inl d,rfl⟩
        | write b => exact ⟨.inr b,rfl⟩)

open ObfImpossibility.RiceNoSize

namespace RiceComplexity

theorem finite_small_machines (k : ℕ) : {M : Machine | size M ≤ k}.Finite := by
  classical
  let A := (q : Fin k) × Turing.TM0.Machine Bool (Fin (q.val+1))
  letI : Finite A := by dsimp [A,Turing.TM0.Machine]; infer_instance
  let decode : A → Machine := fun a => ⟨a.1.val,a.2⟩
  apply (Set.finite_range decode).subset
  intro M hM
  have hq : M.q < k := by change M.q+1 ≤ k at hM; omega
  exact ⟨⟨⟨M.q,hq⟩,M.δ⟩,rfl⟩

theorem Nfun_injective (n : ℕ) : Function.Injective (Nfun n) := by
  intro r s h
  have he := congrFun h (n+2)
  simpa [Nfun] using he

theorem high_complexity (n : ℕ)
    (hrep : ∀ r : ℕ, ∃ M : Machine, fn M = Nfun n r) :
    ∃ r : ℕ, n+1 < KC (Nfun n r) ∧ ∀ N : Machine, fn N = Nfun n r → N ∈ PiY := by
  classical
  let F := fn '' {M : Machine | size M ≤ n+1}
  have hF : F.Finite := (finite_small_machines (n+1)).image fn
  have hpre : ((Nfun n) ⁻¹' F).Finite := Set.Finite.preimage (Nfun_injective n).injOn hF
  obtain ⟨r,hr⟩ := hpre.exists_notMem
  have hnot : Nfun n r ∉ F := hr
  have hgt : n+1 < KC (Nfun n r) := by
    by_contra hle
    have hle' : KC (Nfun n r) ≤ n+1 := by omega
    have hex : {s : ℕ | ∃ M : Machine, fn M = Nfun n r ∧ size M = s}.Nonempty := by
      obtain ⟨M,hM⟩ := hrep r
      exact ⟨size M,M,hM,rfl⟩
    obtain ⟨M,hfn,hsize⟩ := Nat.sInf_mem hex
    apply hnot
    refine ⟨M,?_,hfn⟩
    change size M ≤ n+1
    rw [hsize]
    exact hle'
  refine ⟨r,hgt,?_⟩
  intro N hN
  constructor
  · intro x
    rw [hN]
    simp [Nfun]
  · refine ⟨n+1,?_,?_⟩
    · simpa [hN] using hgt
    · rw [hN]
      simp [Nfun]

#print axioms high_complexity
end RiceComplexity

theorem solution (n : ℕ) :
    ∃ r : ℕ, n + 1 < KC (Nfun n r) ∧ ∀ N : Machine, fn N = Nfun n r → N ∈ PiY := by
  apply RiceComplexity.high_complexity n
  intro r
  exact ⟨RiceDelay.mach n r,funext (RiceDelay.fn_value n r)⟩
#print axioms solution
