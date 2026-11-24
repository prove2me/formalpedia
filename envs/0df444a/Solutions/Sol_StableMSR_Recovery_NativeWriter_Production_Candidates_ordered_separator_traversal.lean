-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.ordered_separator_traversal
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T23:52:03.557549+00:00
-- url     : https://prove2.me/submissions/fb2cdac4-8b85-4dc0-8976-bb526e4bab72

import Definitions.Def_StableMSR_UnfilteredSeparatorCandidates
set_option linter.all false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.Separators
set_option autoImplicit false

/-- Eligible next vertices in descending order. The argument lo excludes
vertices that have already been considered on this branch. -/
def choices (n:ℕ) (active:ℕ→Bool) (lo:ℕ) :=
  ((List.range n).filter (fun v=>decide (lo≤v) && active v)).reverse

/-- Emit the present separator first. Each extension increases its vertex
indices and consumes one unit of width. -/
def walk (n:ℕ) (active:ℕ→Bool) (lo:ℕ) : ℕ→List (List ℕ)
  | 0=>[[]]
  | w+1=>[]::(choices n active lo).flatMap (fun v=>(walk n active (v+1) w).map (v::·))
termination_by w => w

/-- One charge for emitting the present separator and one per vertex tested
at an internal node. -/
def work (n:ℕ) (active:ℕ→Bool) (lo:ℕ) : ℕ→ℕ
  | 0=>1
  | w+1=>1+n+((choices n active lo).map (fun v=>work n active (v+1) w)).sum
termination_by w => w

end StableMSR.Recovery.NativeWriter.Production.Candidates.Separators
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.Separators
open TightLanguage SingleCircuit
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem greater_filter (vs:List ℕ) (w:ℕ) (ordered:vs.Pairwise (·<·)) :
    cuts vs (w+1)=[]::vs.reverse.flatMap (fun v=>(cuts (vs.filter (fun t=>decide (v<t))) w).map (v::·)) := by
  induction vs with
  | nil=>simp [cuts]
  | cons v vs ih=>
    obtain ⟨lt,sort⟩:=List.pairwise_cons.mp ordered
    have after:(vs.filter (fun t=>decide (v<t)))=vs:=List.filter_eq_self.mpr (fun a ha=>by simp [lt a ha])
    let tail:=fun a=>(cuts (vs.filter (fun t=>decide (a<t))) w).map (a::·)
    let all':=fun a=>(cuts ((v::vs).filter (fun t=>decide (a<t))) w).map (a::·)
    have same:vs.reverse.flatMap all'=vs.reverse.flatMap tail:=by
      apply List.flatMap_congr;intro a ha
      have l:v<a:=lt a (List.mem_reverse.mp ha)
      simp [all',tail,show ¬a<v by omega]
    have start:all' v=(cuts vs w).map (v::·):=by simp [all',after]
    change cuts vs (w+1)++(cuts vs w).map (v::·)=[]::(v::vs).reverse.flatMap all'
    rw [List.reverse_cons,List.flatMap_append,same,List.flatMap_singleton,start,ih sort];rfl

theorem walk_exact (n:ℕ) (a:ℕ→Bool) (lo w:ℕ) :
    walk n a lo w=cuts ((List.range n).filter (fun v=>decide (lo≤v) && a v)) w:=by
  let vs:=fun l:ℕ=>(List.range n).filter (fun v=>decide (l≤v) && a v)
  change walk n a lo w=cuts (vs lo) w
  induction w generalizing lo with
  | zero=>rw [walk];cases vs lo <;> rfl
  | succ w ih=>
    have order:(vs lo).Pairwise (·<·):=List.pairwise_lt_range.filter _
    rw [walk,greater_filter _ _ order]
    apply congrArg (List.cons [])
    apply List.flatMap_congr
    intro v hv
    have mem:v∈vs lo:=List.mem_reverse.mp hv
    have lo':lo≤v:=by have b:=(List.mem_filter.mp mem).2;simpa only [Bool.and_eq_true,decide_eq_true_eq] using (show decide (lo≤v)=true from (Bool.and_eq_true_iff.mp b).1)
    have eq:(vs lo).filter (fun t=>decide (v<t))=vs (v+1):=by
      dsimp only [vs];rw [List.filter_filter];apply List.filter_congr
      intro t _;by_cases gt:v<t
      · simp [gt,show lo≤t by omega,show v+1≤t by omega]
      · simp [gt,show ¬v+1≤t by omega]
    rw [eq,ih (v+1)]

theorem member_of_cut {vs s:List ℕ} {w v:ℕ} (h:s∈cuts vs w) (mem:v∈s) : v∈vs:=by
  induction vs generalizing s w with
  | nil=>simp [cuts] at h;subst s;simp at mem
  | cons x xs ih=>
    cases w with
    | zero=>simp [cuts] at h;subst s;simp at mem
    | succ w=>
      rcases List.mem_append.mp h with tail|head
      · exact List.mem_cons_of_mem _ (ih tail mem)
      · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp head
        rcases List.mem_cons.mp mem with eq|hv
        · simp [eq]
        · exact List.mem_cons_of_mem _ (ih ha hv)

theorem distinct_cuts (vs:List ℕ) (w:ℕ) (d:vs.Nodup) : (cuts vs w).Nodup:=by
  induction vs generalizing w with
  | nil=>simp [cuts]
  | cons v vs ih=>
    obtain ⟨absent,tail⟩:=List.nodup_cons.mp d
    cases w with
    | zero=>simp [cuts]
    | succ w=>
      change (cuts vs (w+1)++(cuts vs w).map (v::·)).Nodup
      rw [List.nodup_append]
      refine ⟨ih _ tail,List.Nodup.map (fun _ _ h=>List.cons.inj h |>.2) (ih _ tail),?_⟩
      intro c hc b hb eq;subst b;obtain ⟨s,_,rfl⟩:=List.mem_map.mp hb
      exact absent (member_of_cut hc (by simp))

theorem work_bound (n:ℕ) (a:ℕ→Bool) (lo w:ℕ) : work n a lo w≤(n+1)^(w+1):=by
  have sum_cap {f:ℕ→ℕ} (c:List ℕ) (B:ℕ) (cap:∀v∈c,f v≤B) : (c.map f).sum≤c.length*B:=by
    induction c with
    | nil=>simp
    | cons v c ih=>
      have h:=ih (fun z hz=>cap z (by simp [hz]));have v0:=cap v (by simp)
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul];omega
  induction w generalizing lo with
  | zero=>simp [work]
  | succ w ih=>
    let B:=(n+1)^(w+1)
    have len:(choices n a lo).length≤n:=by simpa [choices] using (List.length_filter_le (fun v=>decide (lo≤v) && a v) (List.range n))
    have bound:((choices n a lo).map (fun v=>work n a (v+1) w)).sum≤n*B:=
      (sum_cap _ _ (fun v _=>ih (v+1))).trans (Nat.mul_le_mul_right B len)
    have pos:n+1≤B:=by simpa [B] using (Nat.pow_le_pow_right (n:=n+1) (by omega) (show 1≤w+1 by omega))
    rw [work,pow_succ];change 1+n+_≤B*(n+1);rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm B n];omega

end StableMSR.Recovery.NativeWriter.Production.Candidates.Separators
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.Separators
open SingleCircuit TightLanguage
set_option autoImplicit false
theorem cover (n:ℕ) (active:ℕ→Bool) :
    let V:=fun lo:ℕ=>(List.range n).filter (fun v=>decide (lo≤v) && active v)
    ∃(walk:ℕ→ℕ→List (List ℕ)) (tests:ℕ→ℕ→ℕ),
      (∀lo,walk lo 0=[[]] ∧ tests lo 0=1) ∧
      (∀lo w,walk lo (w+1)=[]::(V lo).reverse.flatMap (fun v=>(walk (v+1) w).map (v::·)) ∧
        tests lo (w+1)=1+n+((V lo).reverse.map (fun v=>tests (v+1) w)).sum) ∧
      ∀lo w,walk lo w=TightLanguage.cuts (V lo) w ∧ (walk lo w).Nodup ∧
        tests lo w≤(n+1)^(w+1) := by
  dsimp only
  refine ⟨walk n active,work n active,?_,?_,?_⟩
  · intro lo;exact ⟨by rw [walk],by rw [work]⟩
  · intro lo w;exact ⟨by rw [walk];rfl,by rw [work];rfl⟩
  · intro lo w;refine ⟨walk_exact n active lo w,?_,work_bound n active lo w⟩
    rw [walk_exact];apply distinct_cuts;exact List.Nodup.filter _ List.nodup_range
theorem candidate_rows (enc:Key→ℕ) (d:Instance) (w:ℕ) :
    rowTape enc d w=(List.range d.n).flatMap (fun j=>
      (walk d.n d.active 0 (min w d.n)).flatMap (fun s=>(keysFor d (vertices d) s).flatMap (visitTape enc d j s))) := by
  simp [rowTape,walk_exact,vertices]

end StableMSR.Recovery.NativeWriter.Production.Candidates.Separators
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates
theorem solution (n:ℕ) (active:ℕ→Bool) :
    let V:=fun lo:ℕ=>(List.range n).filter (fun v=>decide (lo≤v) && active v)
    ∃(walk:ℕ→ℕ→List (List ℕ)) (tests:ℕ→ℕ→ℕ),
      (∀lo,walk lo 0=[[]] ∧ tests lo 0=1) ∧
      (∀lo w,walk lo (w+1)=[]::(V lo).reverse.flatMap (fun v=>(walk (v+1) w).map (v::·)) ∧
        tests lo (w+1)=1+n+((V lo).reverse.map (fun v=>tests (v+1) w)).sum) ∧
      ∀lo w,walk lo w=TightLanguage.cuts (V lo) w ∧ (walk lo w).Nodup ∧
        tests lo w≤(n+1)^(w+1) := StableMSR.Recovery.NativeWriter.Production.Candidates.Separators.cover n active
