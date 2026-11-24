-- Prove2me | solution 1 for StableMSR.Recovery.SingleRAM.native_global_assembly_writer
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T22:33:49.506685+00:00
-- url     : https://prove2.me/submissions/ce5604c9-a45a-43d6-8bb0-108cc46d87da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StableMSR_Recovery_SingleRAM_global_assembly_resource_bound
import Theorems.Thm_StableMSR_Recovery_NativeWriter_native_assembly_gate_columns
set_option linter.all false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
namespace StableMSR.Recovery.NativeWriter.Encoding
open SingleCircuit SingleRAM
open StableMSR.Recovery.BallCoverCatalog
open StableMSR.Recovery.OracleQueries
set_option autoImplicit false
set_option maxHeartbeats 1500000
def address (k r j : ℕ) := 3+(2*k)*r+j
def fieldValue (g : Gates) (roots : ℕ→ℕ) (r j : ℕ) : ℤ :=
  if r<1+g.size then
    let a:=gateAt g (r-1)
    if j=0 then opCode a else if j=1 then (leftID a:ℤ) else 0
  else if r<1+2*g.size then
    if j=0 then (rightID (gateAt g (r-(1+g.size))):ℤ) else 0
  else if j=0 then (roots (r-(1+2*g.size)):ℤ) else 0
/-- Executable value of each integer cell in the dense target table. -/
def memory (n k S : ℕ) (g : Gates) (roots : ℕ→ℕ) (p : ℕ) : ℤ :=
  let B:=address k (1+5*g.size) 0
  if p=0 then (g.size:ℤ) else if p=1 then (S:ℤ) else if p<B then
    fieldValue g roots ((p-3)/(2*k)) ((p-3)%(2*k))
  else
    let q:=p-B
    if (tinyMask (gateAt g (q/n))).contains (q%n) then 1 else 0
def capacity (n : ℕ) (g : Gates) := 2+5*(1+3*g.size*n*n)
lemma readField (n k S : ℕ) (g : Gates) (roots : ℕ→ℕ)
    {r j : ℕ} (hk : 0<k) (hr : r<1+5*g.size) (hj : j<2*k) :
    memory n k S g roots (address k r j)=fieldValue g roots r j := by
  have h : address k r j<address k (1+5*g.size) 0 := calc
    address k r j < 3+(2*k)*(r+1) := by simp only [address,Nat.mul_add,Nat.mul_one];omega
    _ ≤ address k (1+5*g.size) 0 := by
      unfold address
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  have z : address k r j≠0 := by unfold address;omega
  have o : address k r j≠1 := by unfold address;omega
  unfold memory
  dsimp only
  rw [if_neg z,if_neg o,if_pos h]
  have delta : address k r j-3=(2*k)*r+j := by unfold address;omega
  rw [delta,Nat.mul_add_div (by omega),Nat.div_eq_of_lt hj,Nat.add_zero,Nat.mul_add_mod,Nat.mod_eq_of_lt hj]
private lemma readBit (n k S : ℕ) (g : Gates) (roots : ℕ→ℕ) (p : ℕ) (i : Point n) :
    0< memory n k S g roots (address k (1+5*g.size) 0+p*n+i.val) ↔ i.val∈tinyMask (gateAt g p) := by
  let B:=address k (1+5*g.size) 0
  have Bpos : 3≤B := by dsimp [B,address];omega
  have off : B+p*n+i.val-B=p*n+i.val := by omega
  have div : (p*n+i.val)/n=p := by rw [Nat.mul_comm p n,Nat.mul_add_div (by have:=i.isLt;omega),Nat.div_eq_of_lt i.isLt,Nat.add_zero]
  have rem : (p*n+i.val)%n=i.val := by simp [Nat.add_mod,Nat.mod_eq_of_lt i.isLt]
  change 0< memory n k S g roots (B+p*n+i.val) ↔ _
  unfold memory
  rw [if_neg (by omega),if_neg (by omega),if_neg (show ¬B+p*n+i.val<B by omega),off]
  dsimp only
  rw [div,rem]
  by_cases h:i.val∈tinyMask (gateAt g p) <;> simp [h]
theorem dense_encoding_exact (x : World) (g : Gates) (roots : ℕ→ℕ) (hk : 0<x.k) :
    let H:=capacity x.n g
    let y:={x with rows:=H,mem:=memory x.n x.k x.rows g roots}
    1+5*(1+3*g.size*x.n*x.n)<H ∧ y.mem 1=(x.rows:ℤ) ∧ Input y g roots := by
  let y:={x with rows:=capacity x.n g,mem:=memory x.n x.k x.rows g roots}
  have raw : WindowPorts.rawSize y=g.size := by simp [WindowPorts.rawSize,y,memory]
  have rd (r j : ℕ) (hr:r<1+5*g.size) (hj:j<2*x.k) :
      y.mem (address x.k r j)=fieldValue g roots r j :=readField _ _ _ _ _ hk hr hj
  have addr0 (r : ℕ) : addr x.k r 0=address x.k r 0 := by unfold addr address;ring
  have addr1 (r : ℕ) : addr x.k r 0+1=address x.k r 1 := by rw [addr0]; rfl
  refine ⟨by dsimp [capacity];omega,by simp [y,memory],raw,?_,?_,?_⟩
  · intro p hp
    change y.mem (addr x.k (1+p) 0)=_ ∧ y.mem (addr x.k (1+p) 0+1)=_ ∧ y.mem (addr x.k (1+WindowPorts.rawSize y+p) 0)=_
    rw [raw,addr1,addr0,addr0,rd,rd,rd] <;> try omega
    simp only [fieldValue,if_pos (show 1+p<1+g.size by omega),if_neg (show ¬1+g.size+p<1+g.size by omega),
      if_pos (show 1+g.size+p<1+2*g.size by omega)] 
    simp
  · intro q hq
    change y.mem (addr x.k (1+2*WindowPorts.rawSize y+q) 0)=_
    rw [raw,addr0,rd] <;> try omega
    simp [fieldValue,show ¬1+2*g.size+q<1+g.size by omega,show ¬1+2*g.size+q<1+2*g.size by omega]
  · intro p hp i
    change 0<y.mem (addr x.k (1+5*WindowPorts.rawSize y) 0+p*x.n+i.val) ↔ _
    rw [raw,addr0]
    exact readBit _ _ _ _ _ _ _
end StableMSR.Recovery.NativeWriter.Encoding
namespace StableMSR.Recovery.NativeWriter.Scatter
open Compiler
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
structure Column where
  start : ℕ
  stride : ℕ
  len : ℕ
def Column.addr (c : Column) (i : ℕ) := c.start+c.stride*i
def header (j f : ℕ) : ℤ := -(1+3*(j:ℤ)+(f:ℤ))
def tape (j i : ℕ) : ℤ := -(32+8*(i:ℤ)+(j:ℤ))
def line : List Op→Cmd | []=>.skip | o::os=>.seq (.atom o) (line os)
noncomputable def perform {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) : List Op→Store
  | []=>s | o::os=>perform d (o.eval d s) os
theorem line_exec {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (ops : List Op) :
    Executes d (line ops) s (perform d s ops) ops.length := by
  induction ops generalizing s with
  | nil=>exact .skip s
  | cons x xs ih=>simpa only [line,perform,List.length_cons,Nat.add_comm 1] using Executes.seq (.atom x s) (ih (x.eval d s))
def initOps (j : ℕ) : List Op :=
  [.pointerConst 9 (header j 0),.integerLoad 4 9,.pointerConst 9 (header j 1),.integerLoad 5 9,
   .pointerConst 9 (header j 2),.integerLoad 6 9,.pointerConst 3 (tape j 0),.pointerConst 7 8,.pointerConst 8 1]
def bodyOps : List Op := [.integerLoad 9 3,.integerStore 4 9,.pointerSub 3 3 7,.pointerAdd 4 4 5,.pointerDec 6]
def copyOne (j : ℕ) := Cmd.seq (line (initOps j)) (.whileDo (.pointerLE 8 6) (line bodyOps))
def copyMany : List ℕ→Cmd | []=>.skip | j::js=>.seq (copyOne j) (copyMany js)
def untouched (a b : Store) := (∀r<3,b.ptrs r=a.ptrs r) ∧ ∀q:ℤ,q<0 → b.imem q=a.imem q
def Has (s : Store) (want : ℕ→ℤ) (j : ℕ) (c : Column) :=
  s.imem (header j 0)=(c.start:ℤ) ∧ s.imem (header j 1)=(c.stride:ℤ) ∧ s.imem (header j 2)=(c.len:ℤ) ∧
    ∀i<c.len,s.imem (tape j i)=want (c.addr i)
theorem has_persists {a b : Store} (u:untouched a b) {want : ℕ→ℤ} {j : ℕ} {c : Column} (h:Has a want j c) : Has b want j c := by
  have H (f : ℕ) : b.imem (header j f)=a.imem (header j f):=u.2 _ (by unfold header;omega)
  exact ⟨(H 0).trans h.1,(H 1).trans h.2.1,(H 2).trans h.2.2.1,fun i hi=>(u.2 _ (by unfold tape;omega)).trans (h.2.2.2 i hi)⟩
def Filled (b s : Store) (want : ℕ→ℤ) (c : Column) (i : ℕ) :=
  ∀p : ℕ,b.imem (p:ℤ)=want p ∨ (∃l < i,c.addr l=p) → s.imem (p:ℤ)=want p
structure At (base s : Store) (want : ℕ→ℤ) (j : ℕ) (c : Column) (i m : ℕ) : Prop where
  source : s.ptrs 3=tape j i
  dest : s.ptrs 4=(c.addr i:ℤ)
  stride : s.ptrs 5=(c.stride:ℤ)
  remain : s.ptrs 6=(m:ℤ)
  eight : s.ptrs 7=8
  one : s.ptrs 8=1
  keep : untouched base s
  filled : Filled base s want c i
theorem initial {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (want : ℕ→ℤ) (j : ℕ) (c : Column) (h:Has s want j c) :
    At s (perform d s (initOps j)) want j c 0 c.len := by
  obtain ⟨h0,h1,h2,hv⟩:=h
  constructor
  · simp [perform,initOps,Op.eval]
  · simp [perform,initOps,Op.eval,Column.addr,h0]
  · simp [perform,initOps,Op.eval,h1]
  · simp [perform,initOps,Op.eval,h2]
  · simp [perform,initOps,Op.eval]
  · simp [perform,initOps,Op.eval]
  · constructor
    · intro r hr;interval_cases r <;> simp [perform,initOps,Op.eval,Function.update]
    · intro q hq;rfl
  · intro p h;rcases h with h|⟨l,hl,_⟩
    · exact h
    · omega
theorem advance {n : ℕ} (d : Point n→Point n→ℝ) {base s : Store} {want : ℕ→ℤ} {j : ℕ} {c : Column} {i m : ℕ}
    (src:Has base want j c) (hi:i<c.len) (h:At base s want j c i (m+1)) :
    At base (perform d s bodyOps) want j c (i+1) m := by
  let t:=perform d s bodyOps
  have val:s.imem (s.ptrs 3)=want (c.addr i):=by
    rw [h.source,h.keep.2 _ (by unfold tape;omega),src.2.2.2 i hi]
  have mem (p : ℤ) : t.imem p=if p=(c.addr i:ℤ) then want (c.addr i) else s.imem p := by
    simp [t,perform,bodyOps,Op.eval,Function.update,h.dest,val]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [perform,bodyOps,Op.eval,h.source,h.eight,tape];ring
  · simp [perform,bodyOps,Op.eval,h.dest,h.stride,Column.addr,Nat.mul_add,add_assoc]
  · simpa [perform,bodyOps,Op.eval] using h.stride
  · simp [perform,bodyOps,Op.eval,h.remain]
  · simpa [perform,bodyOps,Op.eval] using h.eight
  · simpa [perform,bodyOps,Op.eval] using h.one
  · constructor
    · intro r hr;interval_cases r <;> simpa [perform,bodyOps,Op.eval,Function.update] using h.keep.1 _ (by decide)
    · intro q hq;rw [mem,if_neg (by omega)];exact h.keep.2 _ hq
  · intro p hp
    rw [mem];by_cases e:p=c.addr i
    · subst p;simp
    · rw [if_neg (by exact_mod_cast e)]
      apply h.filled
      rcases hp with hz|⟨k,hk,eq⟩
      · exact Or.inl hz
      · have ne : k≠i := by rintro rfl;exact e eq.symm
        exact Or.inr ⟨k,by omega,eq⟩
theorem while_exec {n : ℕ} (d : Point n→Point n→ℝ) {base : Store} {want : ℕ→ℤ} {j : ℕ} {c : Column}
    (src:Has base want j c) (m i : ℕ) (endAt:i+m=c.len) (s : Store) (h:At base s want j c i m) :
    ∃t,Executes d (.whileDo (.pointerLE 8 6) (line bodyOps)) s t (7*m+2) ∧ At base t want j c (i+m) 0 := by
  induction m generalizing i s with
  | zero=>
    exact ⟨s,.while_false (by change ¬s.ptrs 8 ≤ s.ptrs 6;rw [h.one,h.remain];decide),by simpa using h⟩
  | succ m ih=>
    let t:=perform d s bodyOps
    have a:=advance d src (by omega) h
    obtain ⟨z,go,last⟩:=ih (i+1) (by omega) t a
    have yes : (Cond.pointerLE 8 6).test s := by change s.ptrs 8 ≤ s.ptrs 6;rw [h.one,h.remain];omega
    have step:=Executes.while_true yes (line_exec d s bodyOps) go
    exact ⟨z,by simpa only [show 1+bodyOps.length+1+(7*m+2)=7*(m+1)+2 by change 1+5+1+(7*m+2)=_;omega] using step,by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using last⟩
theorem one_exec {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (want : ℕ→ℤ) (j : ℕ) (c : Column) (h:Has s want j c) :
    ∃t,Executes d (copyOne j) s t (11+7*c.len) ∧ untouched s t ∧ Filled s t want c c.len := by
  have a:=initial d s want j c h
  obtain ⟨t,go,u⟩:=while_exec d h c.len 0 (by simp) _ a
  refine ⟨t,?_,u.keep,by simpa using u.filled⟩
  have p:=Executes.seq (line_exec d s (initOps j)) go
  simpa only [copyOne,show (initOps j).length+(7*c.len+2)=11+7*c.len by change 9+_=11+_;omega] using p
theorem many_exec {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (cols : ℕ → Column) (want : ℕ→ℤ) (js : List ℕ)
    (all : ∀j∈js,Has s want j (cols j)) :
    ∃t,Executes d (copyMany js) s t ((js.map (fun j=>11+7*(cols j).len)).sum) ∧ untouched s t ∧
    ∀p:ℕ,s.imem (p:ℤ)=want p ∨ (∃j∈js,∃i<(cols j).len,(cols j).addr i=p) → t.imem (p:ℤ)=want p := by
  induction js generalizing s with
  | nil=>exact ⟨s,.skip s,⟨fun _ _=>rfl,fun _ _=>rfl⟩,fun p h=>by simpa using h⟩
  | cons j js ih=>
    obtain ⟨t,one,ut,ft⟩:=one_exec d s want j _ (all j (by simp))
    obtain ⟨z,go,uz,fz⟩:=ih t (fun k hk=>has_persists ut (all k (by simp [hk])))
    refine ⟨z,.seq one go,⟨fun r hr=>(uz.1 r hr).trans (ut.1 r hr),fun q hq=>(uz.2 q hq).trans (ut.2 q hq)⟩,?_⟩
    intro p h;apply fz
    rcases h with h|⟨k,hk,i,hi,eq⟩
    · exact Or.inl (ft p (Or.inl h))
    · rcases List.mem_cons.mp hk with rfl|hm
      · exact Or.inl (ft p (Or.inr ⟨i,hi,eq⟩))
      · exact Or.inr ⟨k,hm,i,hi,eq⟩
end StableMSR.Recovery.NativeWriter.Scatter

/-! The six physical columns, the exact native execution time, and the dense input contract. -/

namespace StableMSR.Recovery.NativeWriter.Scatter
open Compiler OracleQueries SingleCircuit SingleRAM BallCoverCatalog
set_option autoImplicit false
set_option maxHeartbeats 1600000
def columns (n k g : ℕ) : ℕ → Column
  | 0=>⟨0,1,2⟩
  | 1=>⟨addr k 1 0,2*k,g⟩
  | 2=>⟨addr k 1 0+1,2*k,g⟩
  | 3=>⟨addr k (1+g) 0,2*k,g⟩
  | 4=>⟨addr k (1+2*g) 0,2*k,3*g⟩
  | _=>⟨addr k (1+5*g) 0,1,g*n⟩
def jobs : List ℕ := [0,1,2,3,4,5]
def lastOps : List Op := [.pointerConst 9 (-24),.integerLoad 2 9]
def format := Cmd.seq (copyMany jobs) (line lastOps)
def Packed (n k S : ℕ) (g : Gates) (roots : ℕ→ℕ) (s : Store) :=
  s.ptrs 0=(n:ℤ) ∧ s.ptrs 1=(k:ℤ) ∧ s.imem (-24)=(Encoding.capacity n g:ℤ) ∧
  ∀j∈jobs, Has s (Encoding.memory n k S g roots) j (columns n k g.size j)
theorem format_exec {n : ℕ} (d : Point n→Point n→ℝ) (k S : ℕ) (g : Gates) (roots : ℕ→ℕ) (s : Store)
    (hk : 0<k) (pk:Packed n k S g roots s) :
    ∃t,Executes d format s t (82+42*g.size+7*(g.size*n)) ∧
      let y:=worldOf k (Encoding.capacity n g) d t
      Ready y t ∧ y.mem 1=(S:ℤ) ∧ Input y g roots := by
  let cs:=columns n k g.size
  let want:=Encoding.memory n k S g roots
  obtain ⟨v,go,uv,fill⟩:=many_exec d s cs want jobs pk.2.2.2
  let t:=perform d v lastOps
  let y:=worldOf k (Encoding.capacity n g) d t
  let z : World:=⟨n,k,Encoding.capacity n g,d,want⟩
  have act:=Executes.seq go (line_exec d v lastOps)
  refine ⟨t,?_,?_,?_,?_⟩
  · have tm:(jobs.map (fun j=>11+7*(cs j).len)).sum+lastOps.length=82+42*g.size+7*(g.size*n) := by
      simp [jobs,cs,columns,lastOps,List.sum_cons] <;> ring
    simpa only [format,t,tm] using act
  · constructor
    · intro a;cases a with
      | points=>exact (uv.1 0 (by decide)).trans pk.1
      | blocks=>exact (uv.1 1 (by decide)).trans pk.2.1
      | rows=>change (perform d v lastOps).ptrs 2=(Encoding.capacity n g:ℤ);simpa [perform,lastOps,Op.eval] using (uv.2 (-24) (by decide)).trans pk.2.2.1
    · intro p;rfl
  · have h:=fill 1 (Or.inr ⟨0,by decide,1,by change 1<2;decide,rfl⟩)
    change v.imem (1:ℤ)=_;simpa [want,Encoding.memory] using h
  · have cell (j : ℕ) (hj:j∈jobs) (i : ℕ) (hi:i<(cs j).len) : y.mem ((cs j).addr i)=z.mem ((cs j).addr i) := fill _ (Or.inr ⟨j,hj,i,hi,rfl⟩)
    let x : World:=⟨n,k,S,d,want⟩
    have exactZ : Input z g roots := (Encoding.dense_encoding_exact x g roots hk).2.2
    have rawY:WindowPorts.rawSize y=g.size:=by
      have h:=cell 0 (by decide) 0 (by change 0<2;decide)
      change y.mem 0=want 0 at h
      unfold WindowPorts.rawSize;rw [h];simp [want,Encoding.memory]
    have tag (p : ℕ) : (cs 1).addr p=addr k (1+p) 0 := by dsimp [cs,columns,Column.addr,addr];ring <;> simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
    have left (p : ℕ) : (cs 2).addr p=addr k (1+p) 0+1 := by dsimp [cs,columns,Column.addr,addr];ring <;> simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
    have right (p : ℕ) : (cs 3).addr p=addr k (1+g.size+p) 0 := by dsimp [cs,columns,Column.addr,addr];ring <;> simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
    have root (p : ℕ) : (cs 4).addr p=addr k (1+2*g.size+p) 0 := by dsimp [cs,columns,Column.addr,addr];ring <;> simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
    have bit (p : ℕ) : (cs 5).addr p=addr k (1+5*g.size) 0+p := by simp [cs,columns,Column.addr]
    refine ⟨rawY,?_,?_,?_⟩
    · intro p hp
      have h1:=cell 1 (by decide) p hp;rw [tag] at h1
      have h2:=cell 2 (by decide) p hp;rw [left] at h2
      have h3:=cell 3 (by decide) p hp;rw [right] at h3
      have info:=exactZ.2.1 p hp
      change z.mem (addr k (1+p) 0)=_ ∧ z.mem (addr k (1+p) 0+1)=_ ∧ z.mem (addr k (1+WindowPorts.rawSize z+p) 0)=_ at info
      rw [exactZ.1] at info
      change y.mem (addr k (1+p) 0)=_ ∧ y.mem (addr k (1+p) 0+1)=_ ∧ y.mem (addr k (1+WindowPorts.rawSize y+p) 0)=_
      rw [rawY,h1,h2,h3];exact info
    · intro p hp;have h:=cell 4 (by decide) p hp;rw [root] at h
      have zt:=exactZ.2.2.1 p hp
      change z.mem (addr k (1+2*WindowPorts.rawSize z+p) 0)=_ at zt
      change y.mem (addr k (1+2*WindowPorts.rawSize y+p) 0)=_
      rw [exactZ.1] at zt;rw [rawY,h];exact zt
    · intro p hp i
      have bound:p*n+i.val<g.size*n:=by
        have le:=Nat.mul_le_mul_right n (show p+1≤g.size by omega)
        rw [Nat.add_mul,one_mul] at le;have hi:i.val<n:=i.isLt;omega
      have h:=cell 5 (by decide) (p*n+i.val) bound;rw [bit,←Nat.add_assoc] at h
      have zt:=exactZ.2.2.2 p hp i
      change (0<z.mem (addr k (1+5*WindowPorts.rawSize z) 0+p*n+i.val)) ↔ _ at zt
      change (0<y.mem (addr k (1+5*WindowPorts.rawSize y) 0+p*n+i.val)) ↔ _
      rw [exactZ.1] at zt;rw [rawY,h];exact zt
end StableMSR.Recovery.NativeWriter.Scatter

/-! The scratch tape words are exactly the logical gate data. -/

namespace StableMSR.Recovery.NativeWriter.Scatter
open Compiler SingleCircuit SingleRAM BallCoverCatalog
set_option autoImplicit false
set_option maxHeartbeats 1500000
/-- Logical scratch columns, in copy order. A bitmap index ranges over gate-major, point-minor order. -/
def datum (n S : ℕ) (g : Gates) (roots : ℕ→ℕ) : ℕ→ℕ→ℤ
  | 0,i=>if i=0 then (g.size:ℤ) else (S:ℤ)
  | 1,i=>opCode (gateAt g i)
  | 2,i=>(leftID (gateAt g i):ℤ)
  | 3,i=>(rightID (gateAt g i):ℤ)
  | 4,i=>(roots i:ℤ)
  | _,i=>if (tinyMask (gateAt g (i/n))).contains (i%n) then 1 else 0
theorem column_contents (n k S : ℕ) (hk:0<k) (g : Gates) (roots : ℕ→ℕ) (j : ℕ) (hj:j∈jobs)
    (i : ℕ) (hi:i<(columns n k g.size j).len) :
    Encoding.memory n k S g roots ((columns n k g.size j).addr i)=datum n S g roots j i := by
  have jj:j<6:=by simp [jobs] at hj;omega
  interval_cases j
  · change i<2 at hi
    interval_cases i <;> simp [columns,Column.addr,datum,Encoding.memory]
  · change i<g.size at hi
    have loc:(columns n k g.size 1).addr i=Encoding.address k (1+i) 0 := by
      dsimp [columns,Column.addr,Encoding.address,addr];ring <;> simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    rw [loc,Encoding.readField _ _ _ _ _ hk (by omega) (by omega)]
    simp [datum,Encoding.fieldValue,show 1+i<1+g.size by omega]
  · change i<g.size at hi
    have loc:(columns n k g.size 2).addr i=Encoding.address k (1+i) 1 := by
      dsimp [columns,Column.addr,Encoding.address,addr];ring <;> simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    rw [loc,Encoding.readField _ _ _ _ _ hk (by omega) (by omega)]
    simp [datum,Encoding.fieldValue,show 1+i<1+g.size by omega]
  · change i<g.size at hi
    have loc:(columns n k g.size 3).addr i=Encoding.address k (1+g.size+i) 0 := by
      dsimp [columns,Column.addr,Encoding.address,addr];ring <;> simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    rw [loc,Encoding.readField _ _ _ _ _ hk (by omega) (by omega)]
    simp [datum,Encoding.fieldValue,show ¬1+g.size+i<1+g.size by omega,show 1+g.size+i<1+2*g.size by omega]
  · change i<3*g.size at hi
    have loc:(columns n k g.size 4).addr i=Encoding.address k (1+2*g.size+i) 0 := by
      dsimp [columns,Column.addr,Encoding.address,addr];ring <;> simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    rw [loc,Encoding.readField _ _ _ _ _ hk (by omega) (by omega)]
    simp [datum,Encoding.fieldValue,show ¬1+2*g.size+i<1+g.size by omega,show ¬1+2*g.size+i<1+2*g.size by omega]
  · let B:=Encoding.address k (1+5*g.size) 0
    have loc:(columns n k g.size 5).addr i=B+i := by
      dsimp [columns,Column.addr,B,Encoding.address,addr];ring <;> simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    have hb:3≤B:=by dsimp [B,Encoding.address];omega
    rw [loc]
    change (if B+i=0 then _ else if B+i=1 then _ else if B+i<B then _ else _) = _
    simp only [if_neg (show B+i≠0 by omega),if_neg (show B+i≠1 by omega),if_neg (show ¬B+i<B by omega)]
    change (if (tinyMask (gateAt g ((B+i-B)/n))).contains ((B+i-B)%n) then (1:ℤ) else 0)=_
    rw [Nat.add_sub_cancel_left];rfl
theorem packed_iff_gate_data (n k S : ℕ) (hk:0<k) (g : Gates) (roots : ℕ→ℕ) (s : Store) :
    Packed n k S g roots s ↔ s.ptrs 0=(n:ℤ) ∧ s.ptrs 1=(k:ℤ) ∧ s.imem (-24)=(Encoding.capacity n g:ℤ) ∧
      ∀j∈jobs,let c:=columns n k g.size j
      s.imem (header j 0)=(c.start:ℤ) ∧ s.imem (header j 1)=(c.stride:ℤ) ∧ s.imem (header j 2)=(c.len:ℤ) ∧
      ∀i<c.len,s.imem (tape j i)=datum n S g roots j i := by
  unfold Packed Has
  apply and_congr_right;intro _
  apply and_congr_right;intro _
  apply and_congr_right;intro _
  apply forall_congr';intro j
  apply forall_congr';intro hj
  dsimp only
  apply and_congr_right;intro _
  apply and_congr_right;intro _
  apply and_congr_right;intro _
  apply forall_congr';intro i
  apply forall_congr';intro hi
  rw [column_contents n k S hk g roots j hj i hi]
end StableMSR.Recovery.NativeWriter.Scatter


namespace StableMSR.Recovery.NativeWriter.Header
open Compiler Scatter
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

/-- Nonnegative header arithmetic. Only the point and block dimensions occur as loop bounds. -/
inductive Term where
  | num (c : ℕ) | n | k | g | plus (a b : Term) | scale (points : Bool) (a : Term)
def Term.val (n k g : ℕ) : Term → ℕ
  | .num c=>c | .n=>n | .k=>k | .g=>g
  | .plus a b=>a.val n k g+b.val n k g
  | .scale points a=>a.val n k g*(if points then n else k)
def Term.weight : Term → ℕ
  | .plus a b=>a.weight+b.weight+1
  | .scale _ a=>a.weight+10
  | _=>1
def setup (b : ℕ) (points : Bool) : List Op :=
  [.pointerCopy (b+1) b,.pointerConst b 0,.pointerCopy (b+2) (if points then 0 else 1),.pointerConst (b+3) 1]
def Term.code : Term → ℕ → Cmd
  | .num c,b=>.atom (.pointerConst b c)
  | .n,b=>.atom (.pointerCopy b 0) | .k,b=>.atom (.pointerCopy b 1) | .g,b=>.atom (.pointerCopy b 3)
  | .plus a t,b=>.seq (a.code b) (.seq (t.code (b+1)) (.atom (.pointerAdd b b (b+1))))
  | .scale flag a,b=>.seq (a.code b) (.seq (line (setup b flag)) (addLoop b))

def Args (n k g : ℕ) (s : Store) := s.ptrs 0=(n:ℤ) ∧ s.ptrs 1=(k:ℤ) ∧ s.ptrs 3=(g:ℤ)
theorem args_frame {n k g b : ℕ} {s t : Store} (hb : 4≤b) (args : Args n k g s) (h : Frame b s t) : Args n k g t :=
  ⟨(h.1 0 (by omega)).trans args.1,(h.1 1 (by omega)).trans args.2.1,(h.1 3 (by omega)).trans args.2.2⟩

theorem term_run {n : ℕ} (d : Point n→Point n→ℝ) (k g : ℕ) (a : Term) (b : ℕ) (hb : 4≤b)
    (s : Store) (args : Args n k g s) :
    ∃ t z, Executes d (a.code b) s t z ∧ Frame b s t ∧ t.ptrs b=(a.val n k g:ℤ) ∧
      z ≤ a.weight*(1+n+k) := by
  induction a generalizing b s with
  | num c | n | k | g =>
    all_goals refine ⟨_,1,.atom _ _,⟨?_,rfl⟩,?_,?_⟩
    all_goals first
      | intro i hi; simp [Op.eval,Function.update_of_ne (by omega : i≠b)]
      | solve | simp [Term.val,Op.eval,args.1,args.2.1,args.2.2]
      | simp [Term.weight] <;> omega
  | plus a t ha ht =>
    obtain ⟨u,za,ea,fa,va,ta⟩:=ha b hb s args
    obtain ⟨v,zc,ec,fc,vc,tc⟩:=ht (b+1) (by omega) u (args_frame hb args fa)
    let op:=Op.pointerAdd b b (b+1)
    let l:=op.eval d v
    refine ⟨l,za+(zc+1),.seq ea (.seq ec (.atom op v)),⟨?_,fc.2.trans fa.2⟩,?_,?_⟩
    · intro i hi
      simpa [l,op,Op.eval,Function.update_of_ne (by omega : i≠b)] using (fc.1 i (by omega)).trans (fa.1 i hi)
    · simp [l,op,Op.eval,Term.val,fc.1 b (by omega),va,vc]
    · simp only [Term.weight,Nat.add_mul,Nat.one_mul];omega
  | scale flag a ih =>
    obtain ⟨u,z,go,fr,val,cost⟩:=ih b hb s args
    let m:=if flag then n else k
    let v:=perform d u (setup b flag)
    have au:=args_frame hb args fr
    have start : Frame b u v := by
      refine ⟨?_,rfl⟩;intro i hi
      simp [v,perform,setup,Op.eval,Function.update_of_ne (by omega : i≠b+3),
        Function.update_of_ne (by omega : i≠b+2),Function.update_of_ne (by omega : i≠b+1),Function.update_of_ne (by omega : i≠b)]
    have reg : v.ptrs (b+2)=(m:ℤ) := by
      have i0:0≠b:=by omega
      have i1:1≠b:=by omega
      cases flag <;> simp [v,m,perform,setup,Op.eval,i0,i1,Function.update_of_ne (by omega : 1≠b+1),au.1,au.2.1]
    obtain ⟨t,loop,ft,out⟩:=addLoop_run d b m v 0 (a.val n k g:ℤ)
      (by simp [v,perform,setup,Op.eval]) (by simp [v,perform,setup,Op.eval,val]) reg (by simp [v,perform,setup,Op.eval])
    refine ⟨t,z+((setup b flag).length+(2+4*m)),.seq go (.seq (line_exec d u _) loop),frame_trans fr (frame_trans start ft),?_,?_⟩
    · cases flag <;> simpa [Term.val,m,mul_comm] using out
    · have bound : m≤n+k := by cases flag <;> simp [m] <;> omega
      change z+(4+(2+4*m))≤(a.weight+10)*(1+n+k)
      rw [Nat.add_mul];omega

end StableMSR.Recovery.NativeWriter.Header


namespace StableMSR.Recovery.NativeWriter.Header
open Compiler Scatter SingleCircuit
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 14000

def copies : ℕ → Term → Term
  | 0,_=>.num 0
  | m+1,a=>.plus (copies m a) a
@[simp] theorem copies_val (m n k g : ℕ) (a : Term) : (copies m a).val n k g=m*a.val n k g := by
  induction m <;> simp [copies,Term.val, *, Nat.succ_mul]
def record (m : ℕ) : Term := .plus (.num 3) (copies 2 (.scale false (.plus (.num 1) (copies m .g))))
def descriptor : ℕ → ℕ → Term
  | 0,0=>.num 0 | 0,1=>.num 1 | 0,_=>.num 2
  | 1,0=>record 0 | 2,0=>.plus (record 0) (.num 1)
  | 3,0=>record 1 | 4,0=>record 2 | _,0=>record 5
  | 5,1=>.num 1 | _,1=>copies 2 .k
  | 4,_=>copies 3 .g | 5,_=>.scale true .g | _,_=>.g
def expression (i : ℕ) : Term :=
  if i=23 then .plus (.num 7) (copies 15 (.scale true (.scale true .g))) else descriptor (i/3) (i%3)
def cell (i : ℕ) : ℤ := -(1+(i:ℤ))
def tailOps (i : ℕ) : List Op := [.pointerConst 5 (cell i),.integerStore 5 4]
def writeOne (i : ℕ) : Cmd := .seq ((expression i).code 4) (line (tailOps i))
def writeList : List ℕ → Cmd | []=>.skip | i::is=>.seq (writeOne i) (writeList is)
def totalWeight (is : List ℕ) := (is.map (fun i => (expression i).weight+2)).sum
def loadSize : List Op := [.pointerConst 4 (word 0 0),.integerLoad 3 4]
def prepare : Cmd := .seq (line loadSize) (writeList (List.range 24))
def overhead : ℕ := totalWeight (List.range 24)+2

theorem list_run {n : ℕ} (d : Point n→Point n→ℝ) (k g : ℕ) (is : List ℕ) (s : Store)
    (args : Args n k g s) (small : ∀ i ∈ is, i<24) :
    ∃ t z, Executes d (writeList is) s t z ∧ z ≤ totalWeight is*(1+n+k) ∧ Args n k g t ∧
      (∀q:ℤ, q≤ -32 → t.imem q=s.imem q) ∧
      ∀ j, s.imem (cell j)=((expression j).val n k g:ℤ) ∨ j∈is →
        t.imem (cell j)=((expression j).val n k g:ℤ) := by
  induction is generalizing s with
  | nil => exact ⟨s,0,.skip _,by simp [totalWeight],args,fun _ _=>rfl,fun _ h=>by simpa using h⟩
  | cons i is ih =>
    obtain ⟨u,zu,go,fr,val,tm⟩:=term_run d k g (expression i) 4 (by decide) s args
    let v:=perform d u (tailOps i)
    have mv (q : ℤ) : v.imem q = if q=cell i then ((expression i).val n k g:ℤ) else s.imem q := by
      simp [v,perform,tailOps,Op.eval,Function.update_apply,val,fr.2]
    have av : Args n k g v := by
      obtain ⟨a,b,c⟩:=args_frame (by decide) args fr
      exact ⟨by simpa [v,perform,tailOps,Op.eval] using a,
        by simpa [v,perform,tailOps,Op.eval] using b,by simpa [v,perform,tailOps,Op.eval] using c⟩
    obtain ⟨t,z,gt,tt,at',bt,all⟩:=ih v av (fun j hj=>small j (by simp [hj]))
    refine ⟨t,(zu+(tailOps i).length)+z,.seq (.seq go (line_exec d u _)) gt,?_,at',?_,?_⟩
    · have ws : totalWeight (i::is)=((expression i).weight+2)+totalWeight is := by simp [totalWeight]
      rw [ws,Nat.add_mul,Nat.add_mul]
      change (zu+2)+z ≤ _
      omega
    · intro q hq;rw [bt q hq,mv,if_neg]
      have hi:=small i (by simp);unfold cell;omega
    · intro j hj;apply all
      by_cases eq:j=i
      · subst j;left;simp [mv]
      · rcases hj with e|e
        · left;rw [mv,if_neg];exact e
          unfold cell;omega
        · right;simpa [eq] using e

theorem descriptor_val (n k g j f : ℕ) (hj : j<6) (hf : f<3) :
    (descriptor j f).val n k g =
      if f=0 then (columns n k g j).start else if f=1 then (columns n k g j).stride else (columns n k g j).len := by
  interval_cases j <;> interval_cases f <;>
    simp [descriptor,record,Term.val,columns,BallCoverCatalog.addr] <;> ring

theorem prepare_run {n : ℕ} (d : Point n→Point n→ℝ) (k S : ℕ) (g : Gates) (roots : ℕ→ℕ) (s : Store)
    (hk : 0<k) (h : Columns n k S g roots s) :
    ∃ t z, Executes d prepare s t z ∧ z≤overhead*(1+n+k) ∧ Packed n k S g roots t := by
  obtain ⟨sn,sk,cnt,rows,gate,root,bit⟩:=h
  let u:=perform d s loadSize
  have a : Args n k g.size u := by
    exact ⟨by simpa [u,perform,loadSize,Op.eval] using sn,by simpa [u,perform,loadSize,Op.eval] using sk,
      by simpa [u,perform,loadSize,Op.eval] using cnt⟩
  obtain ⟨t,z,go,cost,args,keep,cols⟩:=list_run d k g.size (List.range 24) u a (fun i hi=>List.mem_range.mp hi)
  refine ⟨t,loadSize.length+z,.seq (line_exec d s _) go,?_,?_⟩
  · change 2+z ≤ (totalWeight (List.range 24)+2)*(1+n+k)
    rw [Nat.add_mul];omega
  · apply (packed_iff_gate_data n k S hk g roots t).2
    have get (j : ℕ) (hj : j<24) := cols j (Or.inr (List.mem_range.mpr hj))
    have cap := get 23 (by decide)
    have eq : (expression 23).val n k g.size=Encoding.capacity n g := by simp [expression,Term.val,Encoding.capacity];ring
    rw [eq] at cap
    refine ⟨args.1,args.2.1,cap,?_⟩
    intro j hj
    have jj:j<6:=by simp [jobs] at hj;omega
    have hd (f : ℕ) (hf : f<3) : t.imem (header j f)=
        ((if f=0 then (columns n k g.size j).start else if f=1 then (columns n k g.size j).stride else (columns n k g.size j).len:ℕ):ℤ) := by
      have z:=get (3*j+f) (by omega)
      have ce : cell (3*j+f)=header j f := by simp [cell,header];ring
      have ex : expression (3*j+f)=descriptor j f := by
        unfold expression
        rw [if_neg (by omega),show (3*j+f)/3=j by omega,show (3*j+f)%3=f by omega]
      rwa [ce,ex,descriptor_val _ _ _ _ _ jj hf] at z
    refine ⟨by simpa using hd 0 (by decide),by simpa using hd 1 (by decide),by simpa using hd 2 (by decide),?_⟩
    intro i hi
    have hold : t.imem (tape j i)=s.imem (word j i) := keep _ (by unfold tape;omega)
    rw [hold]
    interval_cases j
    · change i<2 at hi
      interval_cases i
      · exact cnt
      · exact rows
    · exact (gate i hi).1
    · exact (gate i hi).2.1
    · exact (gate i hi).2.2
    · exact root i hi
    · change i<g.size*n at hi
      have nn:0<n:=by by_contra! e;simp [show n=0 by omega] at hi
      have p : i/n<g.size := (Nat.div_lt_iff_lt_mul nn).2 hi
      have b:=bit _ p _ (Nat.mod_lt i nn)
      rwa [Nat.mul_comm (i/n) n, Nat.div_add_mod i n] at b

end StableMSR.Recovery.NativeWriter.Header


namespace StableMSR.Recovery.NativeWriter
open Compiler OracleQueries SingleCircuit SingleRAM WindowCSP
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem writer_of_columns
    (source : ∃ c D b : ℕ, ∀ e : ℚ, 0 < e → e < 1 → ∃ cmd : Cmd, GeneratesColumns e c D b cmd) :
    ∃ c D b : ℕ, 0<c ∧ 0<b ∧ ∀ e : ℚ, 0<e → e<1 → ∃ cmd : Cmd, NativeAssemblySpec e c D b cmd := by
  obtain ⟨c,D,b,src⟩:=source
  refine ⟨c+Header.overhead+256,D+4,b+75,by omega,by omega,?_⟩
  intro e he hl
  obtain ⟨p,P⟩:=src e he hl
  refine ⟨.seq p (.seq Header.prepare Scatter.format),?_⟩
  intro x s hk kn metric ready
  let a:=globalAssembly x (budget (e:ℝ)) (widthBound (e:ℝ))
  let E:=parameterEnvelope (e:ℝ)
  let L:=x.cap^(D+4)*x.n^((b+75)*E)
  have nn:2≤x.n:=by omega
  have cp:1≤x.cap:=by dsimp [World.cap];omega
  have mono (j t : ℕ) (j0 : j≤D+4) (t0 : t≤b+75) : x.cap^j*x.n^(t*E) ≤ L :=
    Nat.mul_le_mul (Nat.pow_le_pow_right cp j0) (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ t0))
  obtain ⟨u,z,run,time,cols⟩:=P x s hk kn metric ready
  obtain ⟨v,h,head,ht,pk⟩:=Header.prepare_run x.dist x.k x.rows a.gates a.roots u hk cols
  obtain ⟨t,out,fields⟩:=Scatter.format_exec x.dist x.k x.rows a.gates a.roots v hk pk
  let f:=82+42*a.gates.size+7*(a.gates.size*x.n)
  have resources:=global_assembly_resource_bound x e he hl nn
  have time' : z≤c*L:=by
    apply time.trans
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left c (mono D b (by omega) (by omega))
  have hh : h≤Header.overhead*L:=by
    have d : 1+x.n+x.k≤x.cap:=by dsimp [World.cap];omega
    have m:=mono 1 0 (by omega) (by omega)
    simp only [Nat.pow_one,Nat.zero_mul,Nat.pow_zero,Nat.mul_one] at m
    exact ht.trans (Nat.mul_le_mul_left _ (d.trans m))
  have ff : f≤256*L:=by
    apply resources.2.2.trans
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 256 (mono 3 75 (by omega) (by omega))
  refine ⟨t,z+(h+f),Encoding.capacity x.n a.gates,.seq run (.seq head out),?_,?_,fields.1,fields.2.1,?_,fields.2.2⟩
  · change z+(h+f) ≤ (c+Header.overhead+256)*x.cap^(D+4)*x.n^((b+75)*E)
    rw [Nat.mul_assoc,Nat.add_mul,Nat.add_mul]
    change z+(h+f) ≤ c*L+Header.overhead*L+256*L
    omega
  · change Encoding.capacity x.n a.gates ≤ (c+Header.overhead+256)*x.cap^(D+4)*x.n^((b+75)*E)
    rw [Nat.mul_assoc]
    apply resources.2.1.trans
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul (by omega) (mono 4 75 (by omega) (by omega))
  · change 1+5*(1+3*a.gates.size*x.n*x.n)<2+5*(1+3*a.gates.size*x.n*x.n)
    omega

end StableMSR.Recovery.NativeWriter

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 15000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleCodes
open StableMSR.Recovery.WindowProfiles (piece keys)
open StableMSR.Recovery.SingleWindows
open StableMSR.Recovery.SingleRAM
theorem solution :
    ∃ c D b : ℕ, 0 < c ∧ 0 < b ∧
      ∀ e : ℚ, 0 < e → e < 1 → ∃ cmd : Cmd, NativeAssemblySpec e c D b cmd := StableMSR.Recovery.NativeWriter.writer_of_columns StableMSR.Recovery.NativeWriter.native_assembly_gate_columns
