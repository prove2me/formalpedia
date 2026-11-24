-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Relative.native_relative_relocation_pass
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T22:37:00.090923+00:00
-- url     : https://prove2.me/submissions/e980c8b7-fa1b-4924-b0ae-0d439cca9644

import Definitions.Def_StableMSR_RelativeRegionReports
set_option linter.all false
set_option maxRecDepth 16000
namespace StableMSR.Recovery.NativeWriter.Relative
open OracleQueries Compiler SingleCircuit SingleCodes SingleRAM WindowCSP
open WindowProfiles (keys piece)
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000

def resolve (base token : ℤ) : ℤ := if 0≤token then base+token else -1-token
def adjust (tag : ℤ) (p : ℕ) (a : ℤ) := if 1≤tag then a+(p:ℤ) else a

theorem raw_succ (x : World) (h w r : ℕ) :
    rawAssembly x h w (r+1)=appendRegion x h w r (rawAssembly x h w r) := by
  simp [rawAssembly,List.range_succ]

theorem append_fields (x : World) (h w r : ℕ) (a : Assembly) :
    (appendRegion x h w r a).gates = a.gates ++ (packet x h w r).gates.map (relocateGate a.gates.size) ∧
    ((appendRegion x h w r a).roots r:ℤ)=resolve a.gates.size (packet x h w r).token ∧
    ∀ i, i≠r → (appendRegion x h w r a).roots i=a.roots i := by
  by_cases key:r%x.n∈keys x (r/x.n)
  · by_cases pos:0<scale x (r/x.n)
    · simp [appendRegion,packet,key,pos,resolve,Function.update_of_ne] <;> exact fun i hi=>Function.update_of_ne hi ..
    · simp [appendRegion,packet,key,pos,resolve,Function.update_of_ne] <;> exact fun i hi=>Function.update_of_ne hi ..
  · simp [appendRegion,packet,key,resolve,Function.update_of_ne] <;> exact fun i hi=>Function.update_of_ne hi ..

theorem raw_size (x : World) (h w r : ℕ) : (rawAssembly x h w r).gates.size=firstGate x h w r := by
  induction r with
  | zero=>rfl
  | succ r ih=>rw [raw_succ,(append_fields ..).1,Array.size_append,Array.size_map,ih,firstGate]

theorem total_size (x : World) (h w : ℕ) : (globalAssembly x h w).gates.size=total x h w := by
  unfold globalAssembly padAssembly total
  simp only [Array.size_append,Array.size_replicate,raw_size]; omega

theorem raw_roots (x : World) (h w R r : ℕ) :
    ((rawAssembly x h w R).roots r:ℤ)=
      if r<R then resolve (firstGate x h w r) (packet x h w r).token else 0 := by
  induction R with
  | zero=>simp [rawAssembly,emptyAssembly]
  | succ R ih=>
    rw [raw_succ]
    by_cases e:r=R
    · subst r;rw [(append_fields ..).2.1,raw_size,if_pos (by omega)]
    · rw [(append_fields ..).2.2 _ e,ih]
      by_cases q:r<R <;> simp [q,show (r<R+1)↔r<R by omega]

def Matches (n : ℕ) (s : Store) (p : ℕ) (op : Gate) : Prop :=
  s.imem (word 1 p)=opCode op ∧
  adjust (s.imem (word 1 p)) p (s.imem (word 2 p))=(leftID op:ℤ) ∧
  adjust (s.imem (word 1 p)) p (s.imem (word 3 p))=(rightID op:ℤ) ∧
  ∀ i<n, s.imem (word 5 (p*n+i))=(if (tinyMask op).contains i then 1 else 0)

theorem record_relocates (n : ℕ) (s : Store) (off j : ℕ) (op : Gate)
    (h : Record n s (off+j) j op) : Matches n s (off+j) (relocateGate off op) := by
  obtain ⟨tag,l,r,bit⟩:=h
  cases op <;> refine ⟨tag,?_,?_,bit⟩ <;>
    simp [relocateGate,tag,l,r,opCode,displacement,adjust,leftID,rightID] <;> omega

theorem record_stop (n : ℕ) (s : Store) (p j : ℕ) (h : Record n s p j .stop) : Matches n s p .stop := by
  obtain ⟨t,l,r,b⟩:=h
  exact ⟨t,by simp [adjust,t,opCode,l,displacement],by simp [adjust,t,opCode,r,displacement],b⟩

theorem raw_matches (x : World) (h w R : ℕ) (s : Store) (a0 : Record x.n s 0 0 (.atom []))
    (a1 : Record x.n s 1 1 .stop)
    (localData : ∀ r<R, let c:=packet x h w r
       ∀ j<c.gates.size, Record x.n s (firstGate x h w r+j) j (gateAt c.gates j)) :
    ∀p<(rawAssembly x h w R).gates.size, Matches x.n s p (gateAt (rawAssembly x h w R).gates p) := by
  induction R with
  | zero=>
    intro p hp;change p<2 at hp
    interval_cases p
    · exact record_relocates x.n s 0 0 (.atom []) a0
    · exact record_stop x.n s 1 1 a1
  | succ R ih=>
    rw [raw_succ,(append_fields ..).1]
    let a:=(rawAssembly x h w R).gates
    let c:=(packet x h w R).gates
    change ∀p<(a++c.map (relocateGate a.size)).size,Matches x.n s p (gateAt (a++c.map (relocateGate a.size)) p)
    intro p hp
    by_cases old:p<a.size
    · simp only [gateAt,Array.getElem?_append_left old]
      exact ih (fun r hr=>localData r (by omega)) p old
    · let j:=p-a.size
      have eq:p=a.size+j:=by dsimp [j];omega
      have hj:j<c.size:=by simp only [Array.size_append,Array.size_map] at hp;dsimp [j];omega
      rw [eq]
      have rd:=localData R (by omega) j hj
      rw [←raw_size] at rd
      have good:=record_relocates x.n s a.size j (gateAt c j) rd
      have id : gateAt (a++c.map (relocateGate a.size)) (a.size+j)=relocateGate a.size (gateAt c j) := by
        simp only [gateAt,Array.getElem?_append_right (show a.size≤a.size+j by omega),
          Nat.add_sub_cancel_left,Array.getElem?_map]
        simp [getElem?_pos c j hj]
      rwa [id]

theorem reports_fields (x : World) (h w : ℕ) (s : Store) (rep : Reports x h w s) :
    let a:=globalAssembly x h w
    let R:=x.rows*x.n
    let carry:=fun r=>((firstGate x h w (min r R)):ℤ)
    a.gates.size=total x h w ∧ (∀p<a.gates.size,Matches x.n s p (gateAt a.gates p)) ∧
    ∀r<3*a.gates.size,
      carry r+s.imem (word 6 r)=carry (r+1) ∧
      resolve (carry r) (s.imem (word 4 r))=(a.roots r:ℤ) := by
  dsimp only
  obtain ⟨_,_,_,_,a0,a1,records,padding,directory⟩:=rep
  let R:=x.rows*x.n
  let raw:=(rawAssembly x h w R).gates
  refine ⟨total_size ..,?_,?_⟩
  · intro p hp
    by_cases hp0:p<raw.size
    · have h0:=raw_matches x h w R s a0 a1 records p hp0
      change Matches x.n s p (gateAt (raw++_) p)
      simpa only [gateAt,Array.getElem?_append_left hp0] using h0
    · have after : firstGate x h w R≤p:=by rw [←raw_size];exact Nat.le_of_not_gt hp0
      rw [total_size] at hp
      have stop:=record_stop _ _ _ _ (padding p after hp)
      change Matches x.n s p (gateAt (raw++Array.replicate _ .stop) p)
      simp only [gateAt,Array.getElem?_append_right (Nat.le_of_not_gt hp0),Array.getElem?_replicate]
      split <;> exact stop
  · intro r hr
    rw [total_size] at hr
    obtain ⟨rt,ln⟩:=directory r hr
    change _ ∧ _=((rawAssembly x h w R).roots r:ℤ)
    rw [raw_roots,rt,ln]
    by_cases lo:r<R
    · have a:min r R=r:=Nat.min_eq_left (by omega)
      have b:min (r+1) R=r+1:=Nat.min_eq_left (by omega)
      change ((firstGate x h w (min r R):ℕ):ℤ)+_=_ ∧ resolve (firstGate x h w (min r R)) _=_
      simp [R] at lo a b ⊢
      simp [lo,a,b,firstGate]
    · have a:min r R=R:=Nat.min_eq_right (by omega)
      have b:min (r+1) R=R:=Nat.min_eq_right (by omega)
      change ((firstGate x h w (min r R):ℕ):ℤ)+_=_ ∧ resolve (firstGate x h w (min r R)) _=_
      change ¬r<x.rows*x.n at lo
      simp only [if_neg lo]
      simp [a,b,resolve,R,lo]

end StableMSR.Recovery.NativeWriter.Relative


namespace StableMSR.Recovery.NativeWriter.Relative.Machine
open Compiler
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 14000
def line : List Op → Cmd | []=>.skip | o::os=>.seq (.atom o) (line os)
noncomputable def perform {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) : List Op → Store
  | []=>s | o::os=>perform d (o.eval d s) os
theorem line_exec {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (os : List Op) :
    Executes d (line os) s (perform d s os) os.length := by
  induction os generalizing s with
  | nil=>exact .skip _
  | cons o os ih=>simpa only [line,perform,List.length_cons,Nat.add_comm 1] using Executes.seq (.atom o s) (ih (o.eval d s))

theorem word_inj {j f a b : ℕ} (hj : j<8) (hf : f<8) : word j a=word f b ↔ j=f ∧ a=b := by
  unfold word;omega

def edgesOps : List Op :=
  [.integerLoad 14 7,.pointerAdd 14 14 3,.integerStore 7 14,
   .integerLoad 14 8,.pointerAdd 14 14 3,.integerStore 8 14]
def edges := Cmd.seq (.atom (.integerLoad 14 6)) (.ite (.pointerLE 12 14) (line edgesOps) .skip)

structure Cursor (s : Store) (i m : ℕ) (base : ℤ) : Prop where
  idx : s.ptrs 3=(i:ℤ)
  remaining : s.ptrs 4=(m:ℤ)
  carry : s.ptrs 5=base
  tag : s.ptrs 6=word 1 i
  left : s.ptrs 7=word 2 i
  right : s.ptrs 8=word 3 i
  root : s.ptrs 9=word 4 i
  len : s.ptrs 10=word 6 i
  stride : s.ptrs 11=8
  one : s.ptrs 12=1
  zero : s.ptrs 13=0

theorem edges_run {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (i m : ℕ) (b : ℤ) (h : Cursor s i m b) :
    ∃ t z, Executes d edges s t z ∧ z≤8 ∧ (∀r<14, t.ptrs r=s.ptrs r) ∧
      ∀p, t.imem p=if p=word 2 i then adjust (s.imem (word 1 i)) i (s.imem p)
        else if p=word 3 i then adjust (s.imem (word 1 i)) i (s.imem p) else s.imem p := by
  let load:=Op.integerLoad 14 6
  let u:=load.eval d s
  have test : (Cond.pointerLE 12 14).test u ↔ (1 ≤ s.imem (word 1 i)) := by
    simp [u,load,Op.eval,Cond.test,h.one,h.tag]
  by_cases yes:1≤ s.imem (word 1 i)
  · let t:=perform d u edgesOps
    refine ⟨t,1+(1+edgesOps.length),.seq (.atom load s) (.ite_true (test.2 yes) (line_exec d u _)),by decide,?_,?_⟩
    · intro r hr
      simp [t,u,load,edgesOps,perform,Op.eval,Function.update_of_ne (by omega:r≠14)]
    · intro p
      have ne:word 3 i≠word 2 i:=by unfold word;omega
      by_cases e:p=word 2 i
      · subst p
        simp [t,u,load,perform,edgesOps,Op.eval,h.left,h.right,h.idx,ne,Ne.symm ne,adjust,yes]
      · by_cases f:p=word 3 i
        · subst p
          simp [t,u,load,perform,edgesOps,Op.eval,h.left,h.right,h.idx,ne,adjust,yes]
        · simp [t,u,load,perform,edgesOps,Op.eval,h.left,h.right,h.idx,ne,Function.update_of_ne e,
            Function.update_of_ne f,e,f]
  · refine ⟨u,1+(1+0+1),.seq (.atom load s) (.ite_false (fun e=>yes (test.1 e)) (.skip _)),by decide,?_,?_⟩
    · intro r hr;simp [u,load,Op.eval,Function.update_of_ne (by omega:r≠14)]
    · intro p;simp [u,load,Op.eval,adjust,yes]

theorem Cursor.transport {s t : Store} {i m : ℕ} {b : ℤ} (h : Cursor s i m b)
    (eq : ∀r<14, t.ptrs r=s.ptrs r) : Cursor t i m b := by
  constructor <;> first
    | exact (eq _ (by decide)).trans h.idx
    | exact (eq _ (by decide)).trans h.remaining
    | exact (eq _ (by decide)).trans h.carry
    | exact (eq _ (by decide)).trans h.tag
    | exact (eq _ (by decide)).trans h.left
    | exact (eq _ (by decide)).trans h.right
    | exact (eq _ (by decide)).trans h.root
    | exact (eq _ (by decide)).trans h.len
    | exact (eq _ (by decide)).trans h.stride
    | exact (eq _ (by decide)).trans h.one
    | exact (eq _ (by decide)).trans h.zero

def negative : List Op := [.pointerSub 14 13 14,.pointerDec 14]
def decodeRoot := Cmd.seq (.atom (.integerLoad 14 9)) (.ite (.pointerLE 13 14) (.atom (.pointerAdd 14 14 5)) (line negative))
theorem decode_run {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (i m : ℕ) (b : ℤ) (h : Cursor s i m b) :
    ∃ t z, Executes d decodeRoot s t z ∧ z≤5 ∧ (∀r<14, t.ptrs r=s.ptrs r) ∧
      t.imem=s.imem ∧ t.ptrs 14=resolve b (s.imem (word 4 i)) := by
  let o:=Op.integerLoad 14 9
  let u:=o.eval d s
  have test : (Cond.pointerLE 13 14).test u ↔ (0 ≤ s.imem (word 4 i)) := by simp [u,o,Op.eval,Cond.test,h.zero,h.root]
  by_cases pos:0≤ s.imem (word 4 i)
  · let f:=Op.pointerAdd 14 14 5
    refine ⟨f.eval d u,1+(1+1),.seq (.atom o s) (.ite_true (test.2 pos) (.atom f u)),by decide,?_,rfl,?_⟩
    · intro r hr;simp [f,u,o,Op.eval,Function.update_of_ne (by omega:r≠14)]
    · simp [f,u,o,Op.eval,h.root,h.carry,resolve,pos,add_comm]
  · refine ⟨perform d u negative,1+(1+negative.length+1),.seq (.atom o s)
      (.ite_false (fun e=>pos (test.1 e)) (line_exec d u _)),by decide,?_,rfl,?_⟩
    · intro r hr;simp [u,o,negative,perform,Op.eval,Function.update_of_ne (by omega:r≠14)]
    · simp [u,o,negative,perform,Op.eval,h.zero,h.root,resolve,pos];omega

def finish : List Op := [.integerStore 9 14,.integerLoad 14 10,.pointerAdd 5 5 14,
  .pointerInc 3,.pointerDec 4,.pointerSub 6 6 11,.pointerSub 7 7 11,.pointerSub 8 8 11,
  .pointerSub 9 9 11,.pointerSub 10 10 11]
def step : Cmd := .seq edges (.seq decodeRoot (line finish))

theorem finish_run {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (i m : ℕ) (b : ℤ)
    (h : Cursor s i (m+1) b) :
    let t:=perform d s finish
    Cursor t (i+1) m (b+s.imem (word 6 i)) ∧ (∀r<3,t.ptrs r=s.ptrs r) ∧
      ∀p, t.imem p=if p=word 4 i then s.ptrs 14 else s.imem p := by
  have ne:word 6 i≠word 4 i:=by unfold word;omega
  dsimp only
  refine ⟨?_,?_,?_⟩
  · constructor <;> simp [perform,finish,Op.eval,h.idx,h.remaining,h.carry,h.tag,h.left,h.right,h.root,h.len,h.stride,h.one,h.zero,ne,word] <;> ring
  · intro r hr;interval_cases r <;> simp [perform,finish,Op.eval]
  · intro p;simp [perform,finish,Op.eval,h.root,Function.update_apply]

end StableMSR.Recovery.NativeWriter.Relative.Machine


namespace StableMSR.Recovery.NativeWriter.Relative.Machine
open Compiler
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 14000

def corrected (s : Store) (carry : ℕ→ℤ) (j p : ℕ) : ℤ :=
  if j=2 ∨ j=3 then adjust (s.imem (word 1 p)) p (s.imem (word j p))
  else if j=4 then resolve (carry p) (s.imem (word 4 p)) else s.imem (word j p)
def View (s t : Store) (carry : ℕ→ℤ) (i : ℕ) :=
  ∀ j<8,∀p,t.imem (word j p) = if p < i then corrected s carry j p else s.imem (word j p)

theorem step_run {n : ℕ} (d : Point n→Point n→ℝ) (s t : Store) (i m : ℕ) (carry : ℕ→ℤ)
    (c : Cursor t i (m+1) (carry i)) (v : View s t carry i)
    (next : carry i+s.imem (word 6 i)=carry (i+1)) :
    ∃ u z, Executes d step t u z ∧ z≤23 ∧ Cursor u (i+1) m (carry (i+1)) ∧
      (∀r<3,u.ptrs r=t.ptrs r) ∧ View s u carry (i+1) := by
  obtain ⟨a,z,ea,ta,ka,ma⟩:=edges_run d t i (m+1) _ c
  have ca:=c.transport ka
  obtain ⟨b,f,eb,tb,kb,mb,rb⟩:=decode_run d a i (m+1) _ ca
  have cb:=ca.transport kb
  let u:=perform d b finish
  obtain ⟨cu,keep,mu⟩:=finish_run d b i m _ cb
  have old (j : ℕ) (hj : j<8) : t.imem (word j i)=s.imem (word j i) := by simpa using v j hj i
  have fresh (j : ℕ) (hj : j<8) (j2 : j≠2) (j3 : j≠3) : a.imem (word j i)=s.imem (word j i) := by
    rw [ma];simp [word_inj hj (by decide : 2<8),word_inj hj (by decide : 3<8),j2,j3,old j hj]
  have len := fresh 6 (by decide) (by decide) (by decide)
  have tok := fresh 4 (by decide) (by decide) (by decide)
  rw [mb,len,next] at cu
  refine ⟨u,z+(f+finish.length),.seq ea (.seq eb (line_exec d b _)),?_,cu,?_,?_⟩
  · change z+(f+10)≤23;omega
  · intro r hr;exact (keep r hr).trans ((kb r (by omega)).trans (ka r (by omega)))
  · intro j hj p
    rw [mu,rb,tok,mb,ma]
    by_cases eq:p=i
    · subst p
      simp only [Nat.lt_succ_self,if_true,word_inj hj (by decide : 4<8),word_inj hj (by decide : 2<8),
        word_inj hj (by decide : 3<8),and_true,old 1 (by decide),old j hj]
      by_cases j4:j=4 <;> by_cases j2:j=2 <;> by_cases j3:j=3 <;> simp_all [corrected]
    · have a4:word j p≠word 4 i:=by rw [ne_eq,word_inj hj (by decide)];simp [eq]
      have a2:word j p≠word 2 i:=by rw [ne_eq,word_inj hj (by decide)];simp [eq]
      have a3:word j p≠word 3 i:=by rw [ne_eq,word_inj hj (by decide)];simp [eq]
      simpa only [if_neg a4,if_neg a2,if_neg a3,show (p < i+1)↔p < i by omega] using v j hj p

def control : Cmd := .whileDo (.pointerLE 12 4) step

theorem loop_run {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (L : ℕ) (carry : ℕ→ℤ)
    (inc : ∀i<L, carry i+s.imem (word 6 i)=carry (i+1)) (m i : ℕ) (bound : i+m=L) (t : Store)
    (c : Cursor t i m (carry i)) (v : View s t carry i) :
    ∃u z,Executes d control t u z ∧ z≤2+25*m ∧ (∀r<3,u.ptrs r=t.ptrs r) ∧ View s u carry L := by
  induction m generalizing i t with
  | zero =>
    have il:i=L:=by omega
    refine ⟨t,2,Executes.while_false ?_,by omega,fun _ _=>rfl,by simpa [←il] using v⟩
    change ¬t.ptrs 12≤t.ptrs 4;rw [c.one,c.remaining];decide
  | succ m ih =>
    obtain ⟨u,z,go,cost,cu,ku,vu⟩:=step_run d s t i m carry c v (inc i (by omega))
    obtain ⟨w,l,loop,rest,kw,vw⟩:=ih (i+1) (by omega) u cu vu
    have yes:(Cond.pointerLE 12 4).test t:=by change t.ptrs 12≤t.ptrs 4;rw [c.one,c.remaining];omega
    refine ⟨w,1+z+1+l,Executes.while_true yes go loop,by omega,fun r hr=>(kw r hr).trans (ku r hr),vw⟩

def startOps : List Op := [
  .pointerConst 14 (word 0 0),.integerLoad 4 14,.pointerCopy 14 4,.pointerAdd 4 4 4,.pointerAdd 4 4 14,
  .pointerConst 3 0,.pointerConst 5 2,.pointerConst 6 (word 1 0),.pointerConst 7 (word 2 0),
  .pointerConst 8 (word 3 0),.pointerConst 9 (word 4 0),.pointerConst 10 (word 6 0),
  .pointerConst 11 8,.pointerConst 12 1,.pointerConst 13 0]
def relocate : Cmd := .seq (line startOps) control

theorem relocate_run {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (G : ℕ) (carry : ℕ→ℤ)
    (cnt : s.imem (word 0 0)=(G:ℤ)) (start : carry 0=2)
    (inc : ∀i<3*G, carry i+s.imem (word 6 i)=carry (i+1)) :
    ∃t z, Executes d relocate s t z ∧ z≤17+75*G ∧ (∀r<3,t.ptrs r=s.ptrs r) ∧ View s t carry (3*G) := by
  let u:=perform d s startOps
  have c : Cursor u 0 (3*G) (carry 0) := by
    constructor <;> simp [u,perform,startOps,Op.eval,cnt,start] <;> ring
  have v : View s u carry 0 := by intro j hj p;simp [u,perform,startOps,Op.eval]
  obtain ⟨t,z,go,cost,keep,out⟩:=loop_run d s (3*G) carry inc (3*G) 0 (by omega) u c v
  refine ⟨t,startOps.length+z,.seq (line_exec d s _) go,?_,?_,out⟩
  · change 15+z≤17+75*G;omega
  · intro r hr;rw [keep _ hr];interval_cases r <;> simp [u,perform,startOps,Op.eval]

end StableMSR.Recovery.NativeWriter.Relative.Machine


namespace StableMSR.Recovery.NativeWriter.Relative
open Compiler OracleQueries SingleCircuit SingleRAM
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem native_relative_relocation_pass :
    ∃ cmd : Cmd, ∀ (x : World) (h w : ℕ) (s : Store), Reports x h w s →
      ∃ t z, Executes x.dist cmd s t z ∧ z ≤ 17+75*total x h w ∧
        let a := globalAssembly x h w
        Columns x.n x.k x.rows a.gates a.roots t := by
  refine ⟨Machine.relocate,?_⟩
  intro x h w s rep
  let a:=globalAssembly x h w
  let carry:=fun r=>((firstGate x h w (min r (x.rows*x.n))):ℤ)
  obtain ⟨sz,all,dir⟩:=reports_fields x h w s rep
  obtain ⟨sn,sk,cnt,rows,_⟩:=rep
  obtain ⟨t,z,run,cost,keep,view⟩:=Machine.relocate_run x.dist s a.gates.size carry
    (by simpa only [a,sz] using cnt) (by simp [carry,firstGate]) (fun i hi=>(dir i hi).1)
  have same (j : ℕ) (hj : j<8) (j2 : j≠2) (j3 : j≠3) (j4 : j≠4) (p : ℕ) :
      t.imem (word j p)=s.imem (word j p) := by
    simpa [Machine.corrected,j2,j3,j4] using view j hj p
  refine ⟨t,z,run,by simpa only [a,sz] using cost,(keep 0 (by decide)).trans sn,(keep 1 (by decide)).trans sk,
    (same 0 (by decide) (by decide) (by decide) (by decide) 0).trans (by simpa only [a,sz] using cnt),
    (same 0 (by decide) (by decide) (by decide) (by decide) 1).trans rows,?_,?_,?_⟩
  · intro p hp
    obtain ⟨tag,l,r,_⟩:=all p hp
    have h3:p<3*a.gates.size:=by change p<a.gates.size at hp;omega
    refine ⟨(same 1 (by decide) (by decide) (by decide) (by decide) p).trans tag,?_,?_⟩
    · simpa [view 2 (by decide) p,h3,Machine.corrected] using l
    · simpa [view 3 (by decide) p,h3,Machine.corrected] using r
  · intro r hr
    have ir:=view 4 (by decide) r
    have h3:r<3*a.gates.size:=hr
    simp only [h3,if_true,Machine.corrected,show ¬(4=2 ∨ 4=3) by decide,if_false] at ir
    exact ir.trans (dir r hr).2
  · intro p hp i hi
    exact (same 5 (by decide) (by decide) (by decide) (by decide) _).trans ((all p hp).2.2.2 i hi)

end StableMSR.Recovery.NativeWriter.Relative

open StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.SingleRAM StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative
theorem solution :
    ∃ cmd : Cmd, ∀ (x : World) (h w : ℕ) (s : Store), Reports x h w s →
      ∃ t z, Executes x.dist cmd s t z ∧ z ≤ 17+75*total x h w ∧
        let a := globalAssembly x h w
        Columns x.n x.k x.rows a.gates a.roots t := StableMSR.Recovery.NativeWriter.Relative.native_relative_relocation_pass
