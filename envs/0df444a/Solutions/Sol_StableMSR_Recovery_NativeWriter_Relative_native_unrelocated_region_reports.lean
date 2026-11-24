-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Relative.native_unrelocated_region_reports
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T22:50:08.031797+00:00
-- url     : https://prove2.me/submissions/be18cb41-3d89-467c-979f-2d2c2e2c79ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StableMSR_Recovery_SingleRAM_global_assembly_resource_bound
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Relative_native_single_region_packet
set_option linter.all false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
namespace StableMSR.Recovery.NativeWriter.Relative
open OracleQueries Compiler SingleCircuit SingleCodes SingleRAM WindowCSP
open WindowProfiles (keys piece)
open scoped Classical
set_option autoImplicit false
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

end StableMSR.Recovery.NativeWriter.Relative.Machine

namespace StableMSR.Recovery.NativeWriter.Relative.Machine
theorem word_inj {j f a b : ℕ} (hj : j<8) (hf : f<8) : word j a=word f b ↔ j=f ∧ a=b := by
  unfold word;omega


end StableMSR.Recovery.NativeWriter.Relative.Machine

namespace StableMSR.Recovery.NativeWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit Machine
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 14000

def count (q : Request) : ℕ := match q with | .region | .absent=>1 | _=>0
structure Head (x : World) (r p : ℕ) (s : Store) : Prop where
  ready : Ready x s
  slot : s.ptrs 3=(r:ℤ)
  gate : s.ptrs 4=(p:ℤ)
  slots : s.ptrs 5=(x.rows*x.n:ℕ)
structure At (x : World) (r p : ℕ) (s : Store) : Prop extends Head x r p s where
  nextRow : s.ptrs 6=(r+1:ℕ)
  triple : s.ptrs 8=(3*p:ℕ)
  nextTriple : s.ptrs 9=(3*p+1:ℕ)
structure Writes (x : World) (h w r p : ℕ) (q : Request) (s t : Store) : Prop where
  gates : ∀ j<(payload x h w r q).size, Record x.n t (p+j) j (gateAt (payload x h w r q) j)
  dir : ∀v,directory x h w r q=some v → DirAt t r v
  oldGate : ∀a<p,∀j op,Record x.n s a j op → Record x.n t a j op
  oldDir : ∀a<r,∀v,DirAt s a v → DirAt t a v

def afterOps (q : Request) : List Op :=
  (if count q=1 then [.pointerInc 3] else []) ++
  [.pointerAdd 4 4 7,.pointerCopy 6 3,.pointerInc 6,.pointerAdd 8 4 4,
   .pointerAdd 8 8 4,.pointerCopy 9 8,.pointerInc 9]
def emit (call : Request→Cmd) (q : Request) := Cmd.seq (call q) (line (afterOps q))
def Runs (x : World) (h w T : ℕ) (call : Request→Cmd) :=
  ∀q r p s, Head x r p s → (q=Request.region → r<x.rows*x.n) →
    ∃t z,Executes x.dist (call q) s t z ∧ z≤T ∧ PacketCall x h w r p q s t

end StableMSR.Recovery.NativeWriter.Relative.Controller

namespace StableMSR.Recovery.NativeWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit Machine
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000
theorem emit_run (x : World) (h w T : ℕ) (call : Request→Cmd) (run : Runs x h w T call)
    (q : Request) (r p : ℕ) (s : Store) (hd : Head x r p s) (valid : q=Request.region → r<x.rows*x.n) :
    ∃t z,Executes x.dist (emit call q) s t z ∧ z≤T+8 ∧
      At x (r+count q) (p+(payload x h w r q).size) t ∧ Writes x h w r p q s t := by
  obtain ⟨u,z,go,cost,ready,regs,len,gate,dir,earlier,prev⟩:=run q r p s hd valid
  let t:=perform x.dist u (afterOps q)
  have r3 : u.ptrs 3=(r:ℤ):=(regs 3 (by simp)).trans hd.slot
  have r4 : u.ptrs 4=(p:ℤ):=(regs 4 (by simp)).trans hd.gate
  have r5 : u.ptrs 5=(x.rows*x.n:ℕ):=(regs 5 (by simp)).trans hd.slots
  have tm:(afterOps q).length≤8:=by cases q <;> decide
  have fl : t.imem=u.imem:=by cases q <;> rfl
  have low (i : ℕ) (hi : i<3) : t.ptrs i=u.ptrs i := by
    interval_cases i <;> cases q <;> simp [t,afterOps,count,perform,Op.eval]
  have rd : Ready x t := by
    constructor
    · intro ax
      have small:ax.reg<3:=by cases ax <;> decide
      exact (low ax.reg small).trans (ready.1 ax)
    · intro i;rw [fl,ready.2]
  refine ⟨t,z+(afterOps q).length,.seq go (line_exec x.dist u _),by omega,?_,?_⟩
  · refine ⟨⟨rd,?_,?_,?_⟩,?_,?_,?_⟩ <;> cases q <;>
      simp [t,afterOps,count,perform,Op.eval,r3,r4,r5,len] <;> ring
  · have rr (a j : ℕ) (op : Gate) : Record x.n t a j op ↔ Record x.n u a j op := by simp only [Record,fl]
    have dd (a : ℕ) (v : ℤ×ℕ) : DirAt t a v ↔ DirAt u a v := by simp only [DirAt,fl]
    exact ⟨fun j hj=>(rr ..).2 (gate j hj),fun v hv=>(dd ..).2 (dir v hv),
      fun a ha j op old=>(rr ..).2 (earlier a ha j op old),fun a ha v old=>(dd ..).2 (prev a ha v old)⟩

end StableMSR.Recovery.NativeWriter.Relative.Controller

namespace StableMSR.Recovery.NativeWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit Machine
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000
theorem firstGate_mono (x : World) (h w : ℕ) : Monotone (firstGate x h w) :=
  monotone_nat_of_le_succ (fun r=>by rw [firstGate];omega)

noncomputable def wanted (x : World) (h w r : ℕ) : ℤ×ℕ :=
  if r<x.rows*x.n then ((packet x h w r).token,(packet x h w r).gates.size) else (-1,0)
structure Past (x : World) (h w m r p : ℕ) (s : Store) : Prop where
  seed0 : Record x.n s 0 0 (.atom [])
  seed1 : Record x.n s 1 1 .stop
  blocks : ∀ a < m, ∀j<(packet x h w a).gates.size,
    Record x.n s (firstGate x h w a+j) j (gateAt (packet x h w a).gates j)
  padding : ∀a,firstGate x h w m≤a → a<p → Record x.n s a 0 .stop
  dirs : ∀a<r, DirAt s a (wanted x h w a)

end StableMSR.Recovery.NativeWriter.Relative.Controller

namespace StableMSR.Recovery.NativeWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit Machine
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000
theorem seed_past (x : World) (h w : ℕ) (s t : Store) (wr : Writes x h w 0 0 .seed s t) :
    Past x h w 0 0 2 t :=
  ⟨wr.gates 0 (by change 0<2;decide),wr.gates 1 (by change 1<2;decide),fun a e=>by omega,
   fun a ha ha2=>by change 2≤a at ha;omega,fun a ha=>by omega⟩

end StableMSR.Recovery.NativeWriter.Relative.Controller

namespace StableMSR.Recovery.NativeWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit Machine
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000
theorem slot_past (x : World) (h w r : ℕ) (s t : Store) (hr : r<x.rows*x.n)
    (old : Past x h w r r (firstGate x h w r) s) (wr : Writes x h w r (firstGate x h w r) .region s t) :
    Past x h w (r+1) (r+1) (firstGate x h w (r+1)) t := by
  let F:=firstGate x h w
  have two : 2≤F r:=firstGate_mono x h w (Nat.zero_le r)
  refine ⟨wr.oldGate _ (by change 0<F r;omega) _ _ old.seed0,wr.oldGate _ (by change 1<F r;omega) _ _ old.seed1,?_,?_,?_⟩
  · intro a ha j hj
    by_cases e:a=r
    · subst a;exact wr.gates j hj
    · have before:=firstGate_mono x h w (show a+1≤r by omega)
      change F a+(packet x h w a).gates.size≤F r at before
      exact wr.oldGate _ (by change F a+j<F r;omega) _ _ (old.blocks a (by omega) j hj)
  · intro a ha hb;omega
  · intro a ha
    by_cases e:a=r
    · subst a
      simpa only [wanted,if_pos hr] using wr.dir _ rfl
    · exact wr.oldDir _ (by omega) _ (old.dirs _ (by omega))

theorem pad_past (x : World) (h w R p : ℕ) (s t : Store) (hp : firstGate x h w R≤p)
    (old : Past x h w R R p s) (wr : Writes x h w R p .pad s t) :
    Past x h w R R (p+1) t := by
  have two:2≤p:=(firstGate_mono x h w (Nat.zero_le R)).trans hp
  refine ⟨wr.oldGate _ (by omega) _ _ old.seed0,wr.oldGate _ (by omega) _ _ old.seed1,?_,?_,fun a ha=>wr.oldDir _ ha _ (old.dirs a ha)⟩
  · intro a ha j hj
    have before:=(firstGate_mono x h w (show a+1≤R by omega)).trans hp
    rw [firstGate] at before
    exact wr.oldGate _ (by omega) _ _ (old.blocks a ha j hj)
  · intro a ha hb
    by_cases e:a=p
    · subst a;exact wr.gates 0 (by change 0<1;decide)
    · exact wr.oldGate _ (by omega) _ _ (old.padding a ha (by omega))

theorem tail_past (x : World) (h w r p : ℕ) (s t : Store) (hr : x.rows*x.n≤r)
    (hp : firstGate x h w (x.rows*x.n)≤p) (old : Past x h w (x.rows*x.n) r p s)
    (wr : Writes x h w r p .absent s t) : Past x h w (x.rows*x.n) (r+1) p t := by
  have two:2≤p:=(firstGate_mono x h w (Nat.zero_le _)).trans hp
  refine ⟨wr.oldGate _ (by omega) _ _ old.seed0,wr.oldGate _ (by omega) _ _ old.seed1,?_,?_,?_⟩
  · intro a ha j hj
    have before:=(firstGate_mono x h w (show a+1≤x.rows*x.n by omega)).trans hp
    rw [firstGate] at before
    exact wr.oldGate _ (by omega) _ _ (old.blocks a ha j hj)
  · intro a ha hb;exact wr.oldGate _ hb _ _ (old.padding a ha hb)
  · intro a ha
    by_cases e:a=r
    · subst a;simpa [wanted,Nat.not_lt.mpr hr] using wr.dir _ rfl
    · exact wr.oldDir _ (by omega) _ (old.dirs a (by omega))

end StableMSR.Recovery.NativeWriter.Relative.Controller


namespace StableMSR.Recovery.NativeWriter.Relative.Controller
open Compiler Machine
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Registers below b and all integer memory survive evaluation of a header expression. -/
def Frame (b : ℕ) (s t : Store) := (∀ i<b, t.ptrs i=s.ptrs i) ∧ t.imem=s.imem
theorem frame_trans {b : ℕ} {s t u : Store} (h : Frame b s t) (v : Frame b t u) : Frame b s u :=
  ⟨fun i hi => (v.1 i hi).trans (h.1 i hi),v.2.trans h.2⟩

def addBody (b : ℕ) : List Op := [.pointerAdd b b (b+1),.pointerDec (b+2)]
def addLoop (b : ℕ) : Cmd := .whileDo (.pointerLE (b+3) (b+2)) (line (addBody b))

theorem addLoop_run {n : ℕ} (d : Point n→Point n→ℝ) (b m : ℕ) (s : Store) (a v : ℤ)
    (ha : s.ptrs b=a) (hv : s.ptrs (b+1)=v) (hm : s.ptrs (b+2)=(m:ℤ)) (ho : s.ptrs (b+3)=1) :
    ∃ t, Executes d (addLoop b) s t (2+4*m) ∧ Frame b s t ∧ t.ptrs b=a+(m:ℤ)*v := by
  induction m generalizing s a with
  | zero =>
    refine ⟨s,Executes.while_false ?_,⟨fun _ _=>rfl,rfl⟩,by simpa using ha⟩
    change ¬ s.ptrs (b+3) ≤ s.ptrs (b+2)
    rw [ho,hm];decide
  | succ m ih =>
    let t:=perform d s (addBody b)
    have ht : Frame b s t := by
      refine ⟨?_,rfl⟩;intro i hi
      simp [t,perform,addBody,Op.eval,Function.update_of_ne (by omega : i≠b+2),Function.update_of_ne (by omega : i≠b)]
    obtain ⟨u,go,hu,final⟩:=ih t (a+v) (by simp [t,perform,addBody,Op.eval,ha,hv])
      (by simp [t,perform,addBody,Op.eval,hv]) (by simp [t,perform,addBody,Op.eval,hm])
      (by simp [t,perform,addBody,Op.eval,ho])
    have yes : (Cond.pointerLE (b+3) (b+2)).test s := by change s.ptrs _ ≤ s.ptrs _;rw [ho,hm];omega
    have all:=Executes.while_true yes (line_exec d s (addBody b)) go
    refine ⟨u,?_,frame_trans ht hu,?_⟩
    · simpa only [addLoop,show 1+(addBody b).length+1+(2+4*m)=2+4*(m+1) by change 1+2+1+_= _;omega] using all
    · rw [final];push_cast;ring

end StableMSR.Recovery.NativeWriter.Relative.Controller

namespace StableMSR.Recovery.NativeWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit Machine
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 14000
def start : List Op := [.pointerConst 3 0,.pointerConst 4 0,.pointerConst 5 0,
  .pointerCopy 6 2,.pointerCopy 7 0,.pointerConst 8 1]
def beginProgram : Cmd := .seq (line start) (addLoop 5)
theorem begin_run (x : World) (s : Store) (rd : Ready x s) :
    ∃t, Executes x.dist beginProgram s t (8+4*x.n) ∧ Head x 0 0 t := by
  let u:=perform x.dist s start
  have pts:s.ptrs 0=(x.n:ℤ):=rd.1 .points
  have rows:s.ptrs 2=(x.rows:ℤ):=rd.1 .rows
  obtain ⟨t,go,fr,endval⟩:=addLoop_run x.dist 5 x.n u 0 (x.rows:ℤ)
    (by simp [u,perform,start,Op.eval]) (by simp [u,perform,start,Op.eval,rows])
    (by simp [u,perform,start,Op.eval,pts]) (by simp [u,perform,start,Op.eval])
  refine ⟨t,?_,⟨⟨?_,?_⟩,?_,?_,?_⟩⟩
  · have h:=Executes.seq (line_exec x.dist s start) go
    simpa only [beginProgram,show start.length+(2+4*x.n)=8+4*x.n by change 6+_= _;omega] using h
  · intro ax;cases ax <;> simpa [u,start,perform,Op.eval,Axis.reg,World.size] using
      (fr.1 _ (by decide)).trans (by first | exact rd.1 .points | exact rd.1 .blocks | exact rd.1 .rows)
  · intro i;rw [fr.2];exact rd.2 i
  · simpa [u,perform,start,Op.eval] using fr.1 3 (by decide)
  · simpa [u,perform,start,Op.eval] using fr.1 4 (by decide)
  · simpa [mul_comm] using endval

/-- A guarded loop over any prescribed finite list of consecutive states. -/
theorem bounded_loop (x : World) (c : Cond) (body : Cmd) (I : ℕ→Store→Prop) (N T : ℕ)
    (guard : ∀ i s, I i s → (c.test s ↔ i<N))
    (advance : ∀ i<N, ∀s, I i s → ∃t z,Executes x.dist body s t z ∧ z≤T ∧ I (i+1) t)
    (s : Store) (init : I 0 s) :
    ∃t z,Executes x.dist (.whileDo c body) s t z ∧ z≤2+N*(T+2) ∧ I N t := by
  have loop (m i : ℕ) (eq : i+m=N) (s : Store) (p : I i s) :
      ∃t z,Executes x.dist (.whileDo c body) s t z ∧ z≤2+m*(T+2) ∧ I N t := by
    induction m generalizing i s with
    | zero=>
      have same:i=N:=by omega
      exact ⟨s,2,.while_false (fun h=>by have:= (guard i s p).1 h;omega),by omega,by simpa [←same] using p⟩
    | succ m ih=>
      have span:i<N:=by omega
      obtain ⟨u,z,go,work,next⟩:=advance i span s p
      obtain ⟨t,f,nextgo,rest,out⟩:=ih (i+1) (by omega) u next
      refine ⟨t,1+z+1+f,.while_true ((guard i s p).2 span) go nextgo,?_,out⟩
      rw [Nat.succ_mul];omega
  exact loop N 0 (by omega) s init

def slotGuard := Cond.pointerLE 6 5
def padGuard := Cond.pointerLE 9 5
def tailGuard := Cond.pointerLE 6 8

theorem real_slots (x : World) (h w T : ℕ) (call : Request→Cmd) (run : Runs x h w T call) (s : Store)
    (a : At x 0 2 s) (hist : Past x h w 0 0 2 s) :
    let R:=x.rows*x.n
    ∃t z, Executes x.dist (.whileDo slotGuard (emit call .region)) s t z ∧ z≤2+R*(T+10) ∧
      At x R (firstGate x h w R) t ∧ Past x h w R R (firstGate x h w R) t := by
  let R:=x.rows*x.n
  let I:=fun r t=>At x r (firstGate x h w r) t ∧ Past x h w r r (firstGate x h w r) t
  apply bounded_loop x slotGuard (emit call .region) I R (T+8) ?_ ?_ s ⟨a,hist⟩
  · intro r t it
    change t.ptrs 6≤t.ptrs 5 ↔ (r<R)
    rw [it.1.nextRow,it.1.slots];dsimp [R];omega
  · intro r hr t it
    obtain ⟨u,z,go,work,out,wr⟩:=emit_run x h w T call run .region r (firstGate x h w r) t it.1.toHead (fun _=>hr)
    exact ⟨u,z,go,work,out,slot_past x h w r t u hr it.2 wr⟩

theorem padding_slots (x : World) (h w T : ℕ) (call : Request→Cmd) (run : Runs x h w T call) (s : Store)
    (a : At x (x.rows*x.n) (firstGate x h w (x.rows*x.n)) s)
    (hist : Past x h w (x.rows*x.n) (x.rows*x.n) (firstGate x h w (x.rows*x.n)) s) :
    let R:=x.rows*x.n
    let raw:=firstGate x h w R
    let G:=total x h w
    ∃t z, Executes x.dist (.whileDo padGuard (emit call .pad)) s t z ∧ z≤2+(G-raw)*(T+10) ∧
      At x R G t ∧ Past x h w R R G t := by
  let R:=x.rows*x.n
  let raw:=firstGate x h w R
  let G:=total x h w
  have le:raw≤G:=Nat.le_max_left .. 
  let I:=fun i t=>At x R (raw+i) t ∧ Past x h w R R (raw+i) t
  have go:=bounded_loop x padGuard (emit call .pad) I (G-raw) (T+8) (by
    intro i t it
    change t.ptrs 9≤t.ptrs 5 ↔ (i<G-raw)
    rw [it.1.nextTriple,it.1.slots]
    change ((3*(raw+i)+1:ℕ):ℤ)≤(R:ℤ) ↔ (i < max raw ((R+2)/3)-raw)
    omega) (by
    intro i hi t it
    obtain ⟨u,z,go,tm,out,wr⟩:=emit_run x h w T call run .pad R (raw+i) t it.1.toHead (by intro e;cases e)
    refine ⟨u,z,go,tm,?_,?_⟩
    · simpa only [count,Nat.add_zero,payload,show (#[(SingleCircuit.Gate.stop)]).size=1 by rfl,Nat.add_assoc] using out
    · simpa only [Nat.add_assoc] using pad_past x h w R (raw+i) t u (by change raw≤raw+i;omega) it.2 wr)
    s (by simpa only [I,Nat.add_zero] using And.intro a hist)
  simpa only [I,Nat.add_sub_of_le le,show raw+(G-raw)=G by omega] using go

theorem absent_slots (x : World) (h w T : ℕ) (call : Request→Cmd) (run : Runs x h w T call) (s : Store)
    (a : At x (x.rows*x.n) (total x h w) s)
    (hist : Past x h w (x.rows*x.n) (x.rows*x.n) (total x h w) s) :
    let R:=x.rows*x.n
    let G:=total x h w
    ∃t z,Executes x.dist (.whileDo tailGuard (emit call .absent)) s t z ∧ z≤2+(3*G-R)*(T+10) ∧
      At x (3*G) G t ∧ Past x h w R (3*G) G t := by
  let R:=x.rows*x.n
  let G:=total x h w
  have le:R≤3*G:=by dsimp [R,G,total];omega
  let I:=fun i t=>At x (R+i) G t ∧ Past x h w R (R+i) G t
  have go:=bounded_loop x tailGuard (emit call .absent) I (3*G-R) (T+8) (by
    intro i t it
    change t.ptrs 6≤t.ptrs 8 ↔ (i<3*G-R)
    rw [it.1.nextRow,it.1.triple];omega) (by
    intro i hi t it
    obtain ⟨u,z,go,tm,out,wr⟩:=emit_run x h w T call run .absent (R+i) G t it.1.toHead (by intro e;cases e)
    refine ⟨u,z,go,tm,?_,?_⟩
    · exact out
    · simpa only [Nat.add_assoc] using tail_past x h w (R+i) G t u (by change R≤R+i;omega) (Nat.le_max_left ..) it.2 wr)
    s (by simpa only [I,Nat.add_zero] using And.intro a hist)
  simpa only [I,show R+(3*G-R)=3*G by omega] using go

end StableMSR.Recovery.NativeWriter.Relative.Controller


namespace StableMSR.Recovery.NativeWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit SingleRAM WindowCSP Machine
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 14000
def saveCounts : List Op := [.pointerConst 10 (word 0 0),.integerStore 10 4,.pointerConst 10 (word 0 1),.integerStore 10 2]

theorem finish_reports (x : World) (h w : ℕ) (s : Store) (hd : At x (3*total x h w) (total x h w) s)
    (past : Past x h w (x.rows*x.n) (3*total x h w) (total x h w) s) :
    Reports x h w (perform x.dist s saveCounts) := by
  let t:=perform x.dist s saveCounts
  have m (j i : ℕ) (hj : j<8) (nz : j≠0) : t.imem (word j i)=s.imem (word j i) := by
    simp [t,perform,saveCounts,Op.eval,Function.update_apply,word_inj hj (by decide : 0<8),nz]
  have retains (p j : ℕ) (a : Gate) (v : Record x.n s p j a) : Record x.n t p j a :=
    ⟨(m 1 _ (by decide) (by decide)).trans v.1,(m 2 _ (by decide) (by decide)).trans v.2.1,
      (m 3 _ (by decide) (by decide)).trans v.2.2.1,fun i hi=>(m 5 _ (by decide) (by decide)).trans (v.2.2.2 i hi)⟩
  have pts:=hd.ready.1 Axis.points
  have blocks:=hd.ready.1 Axis.blocks
  change s.ptrs 0=(x.n:ℤ) at pts
  change s.ptrs 1=(x.k:ℤ) at blocks
  have rows:=hd.ready.1 Axis.rows
  change s.ptrs 2=(x.rows:ℤ) at rows
  refine ⟨by simpa [t,perform,saveCounts,Op.eval] using pts,by simpa [t,perform,saveCounts,Op.eval] using blocks,
    ?_,?_,retains _ _ _ past.seed0,retains _ _ _ past.seed1,?_,?_,?_⟩
  · simp [perform,saveCounts,Op.eval,word,hd.gate]
  · simp [perform,saveCounts,Op.eval,word,rows]
  · intro r hr;dsimp only;intro j hj;exact retains _ _ _ (past.blocks r hr j hj)
  · intro p ha hb;exact retains _ _ _ (past.padding p ha hb)
  · intro r hr
    obtain ⟨v,l⟩:=past.dirs r hr
    rw [m 4 r (by decide) (by decide),m 6 r (by decide) (by decide),v,l]
    by_cases h0:r<x.rows*x.n <;> simp [wanted,h0]

def controller (call : Request→Cmd) : Cmd := .seq beginProgram (.seq (emit call .seed)
  (.seq (.whileDo slotGuard (emit call .region)) (.seq (.whileDo padGuard (emit call .pad))
  (.seq (.whileDo tailGuard (emit call .absent)) (line saveCounts)))))

theorem controller_run (x : World) (h w T : ℕ) (call : Request→Cmd) (run : Runs x h w T call) (s : Store)
    (ready : Ready x s) :
    ∃t z,Executes x.dist (controller call) s t z ∧ z≤(T+40)*(x.n+4*total x h w+1) ∧ Reports x h w t := by
  let R:=x.rows*x.n
  let raw:=firstGate x h w R
  let G:=total x h w
  obtain ⟨a,init,head⟩:=begin_run x s ready
  obtain ⟨b,zb,eg,tb,hb,wb⟩:=emit_run x h w T call run .seed 0 0 a head (by intro e;cases e)
  obtain ⟨c,zc,ec,tc,hc,pc⟩:=real_slots x h w T call run b hb (seed_past x h w a b wb)
  obtain ⟨d,zd,ed,td,hd,pd⟩:=padding_slots x h w T call run c hc pc
  obtain ⟨v,zv,ev,tv,hv,pv⟩:=absent_slots x h w T call run d hd pd
  refine ⟨perform x.dist v saveCounts,_,.seq init (.seq eg (.seq ec (.seq ed (.seq ev (line_exec x.dist v _))))),?_,
    finish_reports x h w v hv pv⟩
  change zc≤2+R*(T+10) at tc
  change zd≤2+(G-raw)*(T+10) at td
  change zv≤2+(3*G-R)*(T+10) at tv
  change 8+4*x.n+(zb+(zc+(zd+(zv+4)))) ≤ (T+40)*(x.n+4*G+1)
  have rle:R≤3*G:=by dsimp [R,G,total];omega
  have terms:R+(G-raw)+(3*G-R)≤4*G:=by omega
  have k:=Nat.mul_le_mul_right (T+10) terms
  simp only [Nat.add_mul] at k
  calc _ ≤ 26+4*x.n+T+4*G*(T+10) := by omega
       _ ≤ _ := by nlinarith [Nat.zero_le (T*x.n)]

theorem reports_of_packet_generator
    (size : ∀(x : World) (e : ℚ),0<e → e<1 → 2≤x.n →
      let G:=total x (budget (e:ℝ)) (widthBound (e:ℝ))
      82+42*G+7*(G*x.n)≤256*x.cap^3*x.n^(75*parameterEnvelope (e:ℝ)))
    (packets : ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃call:Request→Cmd,PacketGenerator e c D b call) :
    ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,GeneratesReports e c D b cmd := by
  obtain ⟨c,D,b,gen⟩:=packets
  refine ⟨(c+40)*258,D+3,b+75,?_⟩
  intro e he hl
  obtain ⟨call,localRun⟩:=gen e he hl
  refine ⟨controller call,?_⟩
  intro x s hk hn md rd
  let E:=parameterEnvelope (e:ℝ)
  let B:=x.cap^D*x.n^(b*E)
  let A:=x.cap^3*x.n^(75*E)
  let G:=total x (budget (e:ℝ)) (widthBound (e:ℝ))
  have cp:1≤x.cap:=by unfold World.cap;omega
  have npos:1≤x.n:=by omega
  have Bpos:1≤B:=Nat.mul_pos (Nat.pow_pos cp) (Nat.pow_pos npos)
  have Apos:1≤A:=Nat.mul_pos (Nat.pow_pos cp) (Nat.pow_pos npos)
  have run : Runs x (budget (e:ℝ)) (widthBound (e:ℝ)) (c*B) call := by
    intro q r p u head valid
    obtain ⟨t,z,go,tm,ok⟩:=localRun x u hk hn md head.ready q r p head.slot head.gate valid
    exact ⟨t,z,go,by simpa only [B,E,Nat.mul_assoc] using tm,ok⟩
  obtain ⟨t,z,go,tm,done⟩:=controller_run x _ _ _ call run s rd
  refine ⟨t,z,go,tm.trans ?_,done⟩
  have bounds:82+42*G+7*(G*x.n)≤256*A:=by
    simpa only [A,E,G,Nat.mul_assoc] using size x e he hl (by omega)
  have nx:x.n≤A:=by
    have capN:x.n≤x.cap:=by dsimp [World.cap];omega
    calc x.n ≤ x.cap^1 := by simpa using capN
         _ ≤ x.cap^3 := Nat.pow_le_pow_right cp (by decide)
         _ ≤ _ := Nat.le_mul_of_pos_right _ (Nat.pow_pos npos)
  have first:c*B+40≤(c+40)*B:=by rw [Nat.add_mul];omega
  have second:x.n+4*G+1≤258*A:=by omega
  apply (Nat.mul_le_mul first second).trans
  change ((c+40)*(x.cap^D*x.n^(b*E)))*(258*(x.cap^3*x.n^(75*E)))≤
    ((c+40)*258)*x.cap^(D+3)*x.n^((b+75)*E)
  rw [Nat.add_mul b 75,pow_add,pow_add]
  exact le_of_eq (by ring)

end StableMSR.Recovery.NativeWriter.Relative.Controller


namespace StableMSR.Recovery.NativeWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit Machine
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

def putOps (j idx : ℕ) (v : ℤ) : List Op := [
  .pointerAdd 20 idx idx,.pointerAdd 20 20 20,.pointerAdd 20 20 20,
  .pointerConst 21 (-(32+(j:ℤ))),.pointerSub 20 21 20,.pointerConst 21 v,.integerStore 20 21]
theorem put_run {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (j idx a : ℕ) (v : ℤ)
    (arg : s.ptrs idx=(a:ℤ)) :
    let t:=perform d s (putOps j idx v)
    (∀r<20,t.ptrs r=s.ptrs r) ∧ ∀q,t.imem q=if q=word j a then v else s.imem q := by
  dsimp only
  refine ⟨?_,?_⟩
  · intro r hr;simp [perform,putOps,Op.eval,Function.update_of_ne (by omega:r≠20),Function.update_of_ne (by omega:r≠21)]
  · intro q
    have ad:-(32+(j:ℤ))-(((a:ℤ)+a+(a+a))+((a+a)+(a+a)))=word j a:=by unfold word;ring
    simp only [putOps,perform,Op.eval,Function.update_self,Function.update_of_ne (by decide:20≠21),arg,ad,Function.update_apply]

def cleared (s t : Store) (lo i : ℕ) := (∀j < i,t.imem (word 5 (lo+j))=0) ∧
  ∀q:ℤ,(∀j < i,q≠word 5 (lo+j)) → t.imem q=s.imem q
def bitAdvance : List Op := [.pointerInc 14,.pointerDec 15]
def bitBody : Cmd := .seq (line (putOps 5 14 0)) (line bitAdvance)
def bitLoop := Cmd.whileDo (.pointerLE 16 15) bitBody

theorem bit_loop_run (x : World) (s : Store) (lo : ℕ)
    (a : s.ptrs 14=(lo:ℤ)) (cnt : s.ptrs 15=(x.n:ℤ)) (one : s.ptrs 16=1) :
    ∃t z,Executes x.dist bitLoop s t z ∧ z≤2+x.n*11 ∧
      (∀r<10,t.ptrs r=s.ptrs r) ∧ cleared s t lo x.n := by
  let I:=fun i (t:Store)=>t.ptrs 14=(lo+i:ℕ) ∧ t.ptrs 15=(x.n-i:ℕ) ∧ t.ptrs 16=1 ∧
    (∀r<10,t.ptrs r=s.ptrs r) ∧ cleared s t lo i
  have go:=bounded_loop x (.pointerLE 16 15) bitBody I x.n 9 (by
    intro i t h;change t.ptrs 16≤t.ptrs 15 ↔ (i<x.n)
    rw [h.2.2.1,h.2.1];omega) (by
    intro i hi t h
    obtain ⟨atIdx,rem,unit,keep,yes,no⟩:=h
    let u:=perform x.dist t (putOps 5 14 0)
    let v:=perform x.dist u bitAdvance
    obtain ⟨reg,mem⟩:=put_run x.dist t 5 14 (lo+i) 0 atIdx
    have same (r : ℕ) (hr:r<10) : v.ptrs r=s.ptrs r := by
      simpa [v,bitAdvance,perform,Op.eval,Function.update_of_ne (by omega:r≠14),Function.update_of_ne (by omega:r≠15)] using
        (reg r (by omega)).trans (keep r hr)
    refine ⟨v,7+2,.seq (line_exec x.dist t _) (line_exec x.dist u _),by decide,?_,?_,?_,same,?_,?_⟩
    · simp [v,bitAdvance,perform,Op.eval,show u.ptrs 14= t.ptrs 14 from reg 14 (by decide),atIdx];omega
    · simp [v,bitAdvance,perform,Op.eval,show u.ptrs 15= t.ptrs 15 from reg 15 (by decide),rem];omega
    · simpa [v,bitAdvance,perform,Op.eval] using (reg 16 (by decide)).trans unit
    · intro j hj
      change u.imem _=0;rw [mem]
      split
      · rfl
      · next ne=>
          have diff:j≠i:=fun e=>ne (by rw [e])
          exact yes j (by omega)
    · intro q avoid
      change u.imem q=s.imem q
      rw [mem,if_neg (avoid i (by omega))]
      exact no q (fun j hj=>avoid j (by omega))) s (by
    exact ⟨by simpa using a,by simpa using cnt,one,fun _ _=>rfl,fun j hj=>by omega,fun _ _=>rfl⟩)
  obtain ⟨t,z,run,cost,_,_,_,keep,last⟩:=go
  exact ⟨t,z,run,cost,keep,last⟩

def productInit : List Op := [.pointerConst 14 0,.pointerCopy 15 9,.pointerCopy 16 0,.pointerConst 17 1]
def bitInit : List Op := [.pointerCopy 15 0,.pointerConst 16 1]
def eraseBits : Cmd := .seq (line productInit) (.seq (addLoop 14) (.seq (line bitInit) bitLoop))

theorem erase_bits (x : World) (s : Store) (p : ℕ) (pn : s.ptrs 0=(x.n:ℤ)) (arg : s.ptrs 9=(p:ℤ)) :
    ∃t z,Executes x.dist eraseBits s t z ∧ z≤10+15*x.n ∧ (∀r<10,t.ptrs r=s.ptrs r) ∧
      cleared s t (p*x.n) x.n := by
  let a:=perform x.dist s productInit
  have low (r : ℕ) (hr:r<10) : a.ptrs r=s.ptrs r := by
    simp [a,productInit,perform,Op.eval,Function.update_of_ne (by omega:r≠14),Function.update_of_ne (by omega:r≠15),
      Function.update_of_ne (by omega:r≠16),Function.update_of_ne (by omega:r≠17)]
  obtain ⟨b,prod,fr,pval⟩:=addLoop_run x.dist 14 x.n a 0 (p:ℤ)
    (by simp [a,perform,productInit,Op.eval]) (by simp [a,perform,productInit,Op.eval,arg])
    (by simp [a,perform,productInit,Op.eval,pn]) (by simp [a,perform,productInit,Op.eval])
  let c:=perform x.dist b bitInit
  have low' (r : ℕ) (hr:r<10) : c.ptrs r=s.ptrs r:=by
    simpa [c,bitInit,perform,Op.eval,Function.update_of_ne (by omega:r≠15),Function.update_of_ne (by omega:r≠16)]
      using (fr.1 r (by omega)).trans (low r hr)
  obtain ⟨t,z,go,cost,eq,hit,elsewhere⟩:=bit_loop_run x c (p*x.n)
    (by simp [c,bitInit,perform,Op.eval,pval,mul_comm])
    (by simp [c,bitInit,perform,Op.eval,(fr.1 0 (by decide)).trans (low 0 (by decide)),pn])
    (by simp [c,bitInit,perform,Op.eval])
  have m:c.imem=s.imem:=fr.2
  refine ⟨t,4+((2+4*x.n)+(2+z)),.seq (line_exec x.dist s _) (.seq prod (.seq (line_exec x.dist b _) go)),by omega,
    fun r hr=>(eq r hr).trans (low' r hr),hit,?_⟩
  intro q e;rw [elsewhere q e,m]

end StableMSR.Recovery.NativeWriter.Relative.Controller


namespace StableMSR.Recovery.NativeWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit SingleRAM Machine
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

def blank (stop : Bool) : Gate := if stop then .stop else .atom []
def touched (n p : ℕ) (q : ℤ) := q=word 1 p ∨ q=word 2 p ∨ q=word 3 p ∨ ∃i<n,q=word 5 (p*n+i)
def indices (second : Bool) : List Op :=
  [.pointerCopy 9 4] ++ (if second then [.pointerInc 9] else [])
def fields (stop : Bool) : Cmd :=
  .seq (line (putOps 1 9 (opCode (blank stop)))) (.seq (line (putOps 2 9 0)) (line (putOps 3 9 0)))
def blankGate (second stop : Bool) : Cmd := .seq (line (indices second)) (.seq (fields stop) eraseBits)
def off (second : Bool) : ℕ := if second then 1 else 0

theorem fields_run (x : World) (s : Store) (p : ℕ) (stop : Bool) (addr : s.ptrs 9=(p:ℤ)) :
    ∃t,Executes x.dist (fields stop) s t 21 ∧ (∀r<20,t.ptrs r=s.ptrs r) ∧
      ∀q,t.imem q=if q=word 3 p then 0 else if q=word 2 p then 0 else if q=word 1 p then opCode (blank stop) else s.imem q := by
  let a:=perform x.dist s (putOps 1 9 (opCode (blank stop)))
  let b:=perform x.dist a (putOps 2 9 0)
  let c:=perform x.dist b (putOps 3 9 0)
  obtain ⟨ka,ma⟩:=put_run x.dist s 1 9 p (opCode (blank stop)) addr
  obtain ⟨kb,mb⟩:=put_run x.dist a 2 9 p 0 ((ka 9 (by decide)).trans addr)
  obtain ⟨kc,mc⟩:=put_run x.dist b 3 9 p 0 ((kb 9 (by decide)).trans ((ka 9 (by decide)).trans addr))
  refine ⟨c,.seq (line_exec x.dist s _) (.seq (line_exec x.dist a _) (line_exec x.dist b _)),
    fun r hr=>(kc r hr).trans ((kb r hr).trans (ka r hr)),?_⟩
  intro q;change (perform x.dist b (putOps 3 9 0)).imem q=_
  rw [mc,mb,ma]

theorem blank_gate_run (x : World) (s : Store) (p : ℕ) (second stop : Bool)
    (pn : s.ptrs 0=(x.n:ℤ)) (gate : s.ptrs 4=(p:ℤ)) :
    let P:=p+off second
    ∃t z,Executes x.dist (blankGate second stop) s t z ∧ z≤33+15*x.n ∧
      (∀r<8,t.ptrs r=s.ptrs r) ∧ (∀j,Record x.n t P j (blank stop)) ∧
      ∀q,¬touched x.n P q → t.imem q=s.imem q := by
  let P:=p+off second
  let a:=perform x.dist s (indices second)
  have pos:a.ptrs 9=(P:ℤ):=by cases second <;> simp [P,off,a,indices,perform,Op.eval,gate]
  have low (r : ℕ) (hr:r<8) : a.ptrs r=s.ptrs r:=by
    cases second <;> simp [a,indices,perform,Op.eval,Function.update_of_ne (by omega:r≠9)]
  have cells:a.imem=s.imem:=by cases second <;> rfl
  obtain ⟨b,run,regs,mem⟩:=fields_run x a P stop pos
  obtain ⟨t,z,go,work,keep,hit,avoid⟩:=erase_bits x b P ((regs 0 (by decide)).trans ((low 0 (by decide)).trans pn))
    ((regs 9 (by decide)).trans pos)
  have head (j : ℕ) (hj : j<5) : t.imem (word j P)=b.imem (word j P) := by
    apply avoid;intro i hi;rw [ne_eq,word_inj (by omega) (by decide)];omega
  have h1 : t.imem (word 1 P)=opCode (blank stop):=by
    rw [head 1 (by decide),mem];simp [word_inj (by decide : 1<8) (by decide : 3<8),
      word_inj (by decide : 1<8) (by decide : 2<8)]
  have h2 : t.imem (word 2 P)=0:=by
    rw [head 2 (by decide),mem];simp [word_inj (by decide : 2<8) (by decide : 3<8)]
  have h3 : t.imem (word 3 P)=0:=by rw [head 3 (by decide),mem];simp
  have len:(indices second).length≤2:=by cases second <;> decide
  refine ⟨t,(indices second).length+(21+z),.seq (line_exec x.dist s _) (.seq run go),by omega,
    fun r hr=>(keep r (by omega)).trans ((regs r (by omega)).trans (low r hr)),?_,?_⟩
  · intro j
    refine ⟨h1,?_,?_,?_⟩
    · cases stop <;> simpa [blank,displacement,opCode,leftID] using h2
    · cases stop <;> simpa [blank,displacement,opCode,rightID] using h3
    · intro i hi;cases stop <;> simpa [blank,tinyMask] using hit i hi
  · intro q nq
    have a1:q≠word 1 P:=fun e=>nq (Or.inl e)
    have a2:q≠word 2 P:=fun e=>nq (Or.inr (Or.inl e))
    have a3:q≠word 3 P:=fun e=>nq (Or.inr (Or.inr (Or.inl e)))
    rw [avoid q (fun i hi e=>nq (Or.inr (Or.inr (Or.inr ⟨i,hi,e⟩)))),mem,if_neg a3,if_neg a2,if_neg a1,cells]

theorem preserve_gate {n p a j : ℕ} {op : Gate} {s t : Store}
    (same : ∀q,¬touched n p q → t.imem q=s.imem q) (lt : a<p) (old : Record n s a j op) : Record n t a j op := by
  have point (k : ℕ) (hk : k<4) : t.imem (word k a)=s.imem (word k a) := by
    apply same;unfold touched
    simp [word_inj (by omega : k<8) (by decide : 1<8),word_inj (by omega : k<8) (by decide : 2<8),
      word_inj (by omega : k<8) (by decide : 3<8),word_inj (by omega : k<8) (by decide : 5<8),
      Nat.ne_of_lt lt,show k≠5 by omega]
  refine ⟨(point 1 (by decide)).trans old.1,(point 2 (by decide)).trans old.2.1,(point 3 (by decide)).trans old.2.2.1,?_⟩
  intro i hi
  apply Eq.trans (same _ ?_) (old.2.2.2 i hi)
  unfold touched
  have sep:=Nat.mul_le_mul_right n (show a+1≤p by omega)
  rw [Nat.add_mul,Nat.one_mul] at sep
  simp only [word_inj (by decide : 5<8) (by decide : 1<8),word_inj (by decide : 5<8) (by decide : 2<8),
    word_inj (by decide : 5<8) (by decide : 3<8),word_inj (by decide : 5<8) (by decide : 5<8)]
  omega

theorem preserve_dir {n p a : ℕ} {v : ℤ×ℕ} {s t : Store}
    (same : ∀q,¬touched n p q → t.imem q=s.imem q) (old : DirAt s a v) : DirAt t a v := by
  have no (j : ℕ) (hj : j=4 ∨ j=6) : ¬touched n p (word j a) := by
    rcases hj with rfl|rfl <;> simp [touched,word_inj (by decide : 4<8),word_inj (by decide : 6<8)]
  exact ⟨(same _ (no _ (Or.inl rfl))).trans old.1,(same _ (no _ (Or.inr rfl))).trans old.2⟩

theorem preserve_ready {x : World} {p : ℕ} {s t : Store} (rd : Ready x s)
    (regs : ∀r<8,t.ptrs r=s.ptrs r) (same : ∀q,¬touched x.n p q → t.imem q=s.imem q) : Ready x t := by
  refine ⟨fun ax=>(regs _ (by cases ax <;> decide)).trans (rd.1 ax),?_⟩
  intro i
  apply (same _ ?_).trans (rd.2 i)
  unfold touched word
  push_neg;constructor
  · omega
  · constructor
    · omega
    · constructor
      · omega
      · intro a ha;omega

end StableMSR.Recovery.NativeWriter.Relative.Controller


namespace StableMSR.Recovery.NativeWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit SingleRAM WindowCSP Machine
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 12000

def blankPacket : Request→Cmd
  | .seed=>.seq (blankGate false false) (blankGate true true)
  | .pad=>blankGate false true
  | .absent=>.seq (line (putOps 4 3 (-1))) (line (putOps 6 3 0))
  | .region=>.skip
def fixedLength : Request→ℕ | .seed=>2 | .pad=>1 | _=>0
def constCall (q : Request) := Cmd.seq (blankPacket q) (.atom (.pointerConst 7 (fixedLength q)))

theorem absent_write (x : World) (h w r p : ℕ) (s : Store) (rd : Ready x s) (slot : s.ptrs 3=(r:ℤ)) :
    ∃t,Executes x.dist (blankPacket .absent) s t 14 ∧ Ready x t ∧ (∀a<8,t.ptrs a=s.ptrs a) ∧
      Writes x h w r p .absent s t := by
  let a:=perform x.dist s (putOps 4 3 (-1))
  let t:=perform x.dist a (putOps 6 3 0)
  obtain ⟨ka,ma⟩:=put_run x.dist s 4 3 r (-1) slot
  obtain ⟨kt,mt⟩:=put_run x.dist a 6 3 r 0 ((ka 3 (by decide)).trans slot)
  have mem (z : ℤ) : t.imem z=if z=word 6 r then 0 else if z=word 4 r then -1 else s.imem z := by
    change (perform x.dist a (putOps 6 3 0)).imem z=_
    rw [mt,ma]
  have low (a : ℕ) (ha : a<8) : t.ptrs a=s.ptrs a:=(kt a (by omega)).trans (ka a (by omega))
  have gate (j i : ℕ) (hj : j<8) (a : j≠4) (b : j≠6) : t.imem (word j i)=s.imem (word j i) := by
    rw [mem];simp [word_inj hj (by decide : 4<8),word_inj hj (by decide : 6<8),a,b]
  have keep (a : ℕ) (lt : a<r) (j : ℕ) (hj:j<8) : t.imem (word j a)=s.imem (word j a) := by
    rw [mem];simp [word_inj hj (by decide : 4<8),word_inj hj (by decide : 6<8),Nat.ne_of_lt lt]
  refine ⟨t,.seq (line_exec x.dist s _) (line_exec x.dist a _),⟨fun ax=>(low _ (by cases ax <;> decide)).trans (rd.1 ax),?_⟩,
    low,⟨?_,?_,?_,?_⟩⟩
  · intro i;rw [mem,if_neg (by unfold word;omega),if_neg (by unfold word;omega),rd.2]
  · intro j hj;change j<0 at hj;omega
  · intro v hv;change some ((-1:ℤ),0)=some v at hv;cases hv
    constructor <;> rw [mem] <;> simp [word_inj (by decide : 4<8) (by decide : 6<8)]
  · intro a ha j op o
    exact ⟨(gate 1 _ (by decide) (by decide) (by decide)).trans o.1,(gate 2 _ (by decide) (by decide) (by decide)).trans o.2.1,
      (gate 3 _ (by decide) (by decide) (by decide)).trans o.2.2.1,
      fun i hi=>(gate 5 _ (by decide) (by decide) (by decide)).trans (o.2.2.2 i hi)⟩
  · intro a ha v o;exact ⟨(keep a ha 4 (by decide)).trans o.1,(keep a ha 6 (by decide)).trans o.2⟩

theorem fixed_write (x : World) (h w r p : ℕ) (q : Request) (s : Store) (rd : Ready x s)
    (slot : s.ptrs 3=(r:ℤ)) (base : s.ptrs 4=(p:ℤ)) (fixed : q≠.region) :
    ∃t z,Executes x.dist (blankPacket q) s t z ∧ z≤70+30*x.n ∧ Ready x t ∧
      (∀a<8,t.ptrs a=s.ptrs a) ∧ Writes x h w r p q s t := by
  have pn:s.ptrs 0=(x.n:ℤ):=rd.1 .points
  cases q with
  | region=>exact (fixed rfl).elim
  | absent=>
    obtain ⟨t,go,ready,regs,out⟩:=absent_write x h w r p s rd slot
    exact ⟨t,14,go,by omega,ready,regs,out⟩
  | pad=>
    obtain ⟨t,z,go,tm,regs,gate,fr⟩:=blank_gate_run x s p false true pn base
    change ∀q,¬touched x.n p q → t.imem q=s.imem q at fr
    refine ⟨t,z,go,by omega,preserve_ready rd regs fr,regs,⟨?_,?_,?_,?_⟩⟩
    · intro j hj
      change j<1 at hj
      have e:j=0:=by omega
      subst j
      exact gate 0
    · intro v hv;cases hv
    · intro a ha j op old;exact preserve_gate fr ha old
    · intro a ha v old;exact preserve_dir fr old
  | seed=>
    obtain ⟨a,z,ea,za,ka,ga,fa⟩:=blank_gate_run x s p false false pn base
    change ∀q,¬touched x.n p q → a.imem q=s.imem q at fa
    obtain ⟨t,l,et,zt,kt,gt,ft⟩:=blank_gate_run x a p true true ((ka 0 (by decide)).trans pn) ((ka 4 (by decide)).trans base)
    change ∀q,¬touched x.n (p+1) q → t.imem q=a.imem q at ft
    refine ⟨t,z+l,.seq ea et,by omega,preserve_ready (preserve_ready rd ka fa) kt ft,
      fun i hi=>(kt i hi).trans (ka i hi),⟨?_,?_,?_,?_⟩⟩
    · intro j hj;change j<2 at hj
      interval_cases j
      · exact preserve_gate ft (show p<p+1 by omega) (ga 0)
      · exact gt 1
    · intro v hv;cases hv
    · intro a ha j op old;exact preserve_gate ft (by omega) (preserve_gate fa ha old)
    · intro a ha v old;exact preserve_dir ft (preserve_dir fa old)

theorem const_call_run (x : World) (h w r p : ℕ) (q : Request) (s : Store) (rd : Ready x s)
    (slot : s.ptrs 3=(r:ℤ)) (base : s.ptrs 4=(p:ℤ)) (fixed : q≠.region) :
    ∃t z,Executes x.dist (constCall q) s t z ∧ z≤128*(1+x.n) ∧ PacketCall x h w r p q s t := by
  obtain ⟨a,z,go,cost,ready,regs,out⟩:=fixed_write x h w r p q s rd slot base fixed
  let o:=Op.pointerConst 7 (fixedLength q)
  let t:=o.eval x.dist a
  have eq:fixedLength q=(payload x h w r q).size:=by cases q <;> first | rfl | contradiction
  refine ⟨t,z+1,.seq go (.atom o a),by omega,⟨⟨?_,ready.2⟩,?_,?_,out.gates,out.dir,out.oldGate,out.oldDir⟩⟩
  · intro ax
    have neq:ax.reg≠7:=by cases ax <;> decide
    simpa [t,o,Op.eval,Function.update_of_ne neq] using ready.1 ax
  · intro i hi
    have lt:i<7:=by simp at hi;omega
    simpa [t,o,Op.eval,Function.update_of_ne (by omega : i≠7)] using regs i (by omega)
  · simp [t,o,Op.eval,eq]

theorem packets_of_region
    (region : ∃ c D b : ℕ, ∀e : ℚ, 0<e → e<1 → ∃cmd:Cmd,
      ∀(x : World) (s : Store), 1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
      ∀r p : ℕ, s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
      ∃t z, Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
        PacketCall x (budget (e:ℝ)) (widthBound (e:ℝ)) r p .region s t) :
    ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃call:Request→Cmd,PacketGenerator e c D b call := by
  obtain ⟨c,D,b,make⟩:=region
  refine ⟨c+128,D+1,b,?_⟩
  intro e he hl
  obtain ⟨cmd,src⟩:=make e he hl
  let call : Request→Cmd := fun q=>match q with | .region=>cmd | q=>constCall q
  refine ⟨call,?_⟩
  intro x s hk kn met rd q r p slot base valid
  have cp:1≤x.cap:=by dsimp [World.cap];omega
  have xp:1≤x.n^(b*parameterEnvelope (e:ℝ)):=Nat.pow_pos (by omega)
  by_cases real:q=.region
  · subst q
    obtain ⟨t,z,go,tm,ok⟩:=src x s hk kn met rd r p slot base (valid rfl)
    refine ⟨t,z,go,tm.trans ?_,ok⟩
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right cp (by omega)))
  · have eq:call q=constCall q:=by cases q <;> first | rfl | contradiction
    obtain ⟨t,z,go,tm,ok⟩:=const_call_run x _ _ r p q s rd slot base real
    refine ⟨t,z,eq.symm ▸ go,tm.trans ?_,ok⟩
    have lo:1+x.n≤x.cap:=by dsimp [World.cap];omega
    have cap:x.cap≤x.cap^(D+1):=by simpa using Nat.pow_le_pow_right cp (show 1≤D+1 by omega)
    exact (Nat.mul_le_mul (by omega : 128≤c+128) (lo.trans cap)).trans (Nat.le_mul_of_pos_right _ xp)

end StableMSR.Recovery.NativeWriter.Relative.Controller

open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.SingleRAM StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative
theorem solution :
    ∃ c D b : ℕ, ∀ e : ℚ, 0 < e → e < 1 → ∃ cmd : Cmd, GeneratesReports e c D b cmd := by
  apply Controller.reports_of_packet_generator _ (Controller.packets_of_region native_single_region_packet)
  intro x e he hl hn
  rw [←total_size]
  exact (global_assembly_resource_bound x e he hl hn).2.2
