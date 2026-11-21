-- Prove2me | solution 1 for StableMSR.Recovery.FewBallRows.extend_by_short_rows
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T23:36:47.482923+00:00
-- url     : https://prove2.me/submissions/a938546e-074b-4992-a9ea-b63005034036

import Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_bounded_while_execution
import Theorems.Thm_StableMSR_Recovery_OracleQueries_bounded_oracle_expression_compiler
import Definitions.Def_StableMSR_FewBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
open Polynomial
private def divBody := Cmd.seq (.atom (.pointerSub 4 4 0)) (.atom (.pointerInc 8))
private def divLoop := Cmd.whileDo (.pointerLE 0 4) divBody
private def quotient := Cmd.seq (.atom (.pointerConst 8 0)) divLoop
private def DivKeeps (s t : Store) := t.imem=s.imem ∧ ∀j : ℕ,j ≠ 4 → j ≠ 8 → t.ptrs j=s.ptrs j
private lemma divideLoop {m : ℕ} (d : Point m→Point m→ℝ) (n : ℕ) (hn : 0 < n) (V : ℕ) :
    ∀(s : Store) (a : ℕ),s.ptrs 0=(n:ℤ) → s.ptrs 4=(V:ℤ) → s.ptrs 8=(a:ℤ) →
    ∃t z,Executes d divLoop s t z ∧ z ≤ 4*(V/n)+2 ∧ DivKeeps s t ∧
      t.ptrs 4=(V%n:ℕ) ∧ t.ptrs 8=(a+V/n:ℕ) := by
  induction V using Nat.strong_induction_on with
  | h V ih =>
    intro s a sn sv sa
    by_cases lt : V < n
    · refine ⟨s,2,.while_false ?_,by omega,⟨rfl,fun _ _ _=>rfl⟩,?_,?_⟩
      · change ¬s.ptrs 0 ≤ s.ptrs 4;rw [sn,sv];omega
      · simpa [Nat.mod_eq_of_lt lt] using sv
      · simpa [Nat.div_eq_of_lt lt] using sa
    · have ge : n ≤ V := by omega
      let u := (Op.pointerInc 8).eval d ((Op.pointerSub 4 4 0).eval d s)
      have u0 : u.ptrs 0=(n:ℤ) := by simp [u,Op.eval,Function.update,sn]
      have u4 : u.ptrs 4=(V-n:ℕ) := by simp [u,Op.eval,Function.update,sv,sn,Int.ofNat_sub ge]
      have u8 : u.ptrs 8=(a+1:ℕ) := by simp [u,Op.eval,Function.update,sa]
      obtain ⟨t,z,ez,tz,k,rem,qu⟩ := ih (V-n) (by omega) u (a+1) u0 u4 u8
      have eq := Nat.div_eq_sub_div hn ge
      refine ⟨t,_,Executes.while_true ?_ (.seq (.atom _ _) (.atom _ _)) ez,by omega,⟨k.1,?_⟩,?_,?_⟩
      · change s.ptrs 0 ≤ s.ptrs 4;rw [sn,sv];omega
      · intro j h4 h8
        simpa [u,Op.eval,h4,h8] using k.2 j h4 h8
      · simpa only [Nat.mod_eq_sub_mod ge] using rem
      · simp only [Nat.cast_add,Nat.cast_one] at qu ⊢;omega
private lemma doDiv {m : ℕ} (d : Point m→Point m→ℝ) (n V : ℕ) (hn : 0 < n)
    (s : Store) (sn : s.ptrs 0=(n:ℤ)) (sv : s.ptrs 4=(V:ℤ)) :
    ∃t z,Executes d quotient s t z ∧ z ≤ 4*V+3 ∧ DivKeeps s t ∧
      t.ptrs 4=(V%n:ℕ) ∧ t.ptrs 8=(V/n:ℕ) := by
  let u := (Op.pointerConst 8 0).eval d s
  obtain ⟨t,z,ez,tm,keep,rv,qv⟩ := divideLoop d n hn V u 0 (by simpa [u,Op.eval,Function.update] using sn)
    (by simpa [u,Op.eval,Function.update] using sv) (by simp [u,Op.eval])
  refine ⟨t,_,.seq (.atom _ _) ez,?_,⟨keep.1,fun j h4 h8=>by simpa [u,Op.eval,h8] using keep.2 j h4 h8⟩,rv,by simpa using qv⟩
  have := Nat.div_le_self V n
  omega
private def Frame (n k i : ℕ) (s : Store) := s.ptrs 0=(n:ℤ) ∧ s.ptrs 1=(k:ℤ) ∧
  s.ptrs 2=(i:ℤ) ∧ s.ptrs 5=((2*k:ℕ):ℤ)-1 ∧ s.ptrs 6=0
private def digitBody := Cmd.seq quotient (.seq (.atom (.integerStore 3 4)) (.seq (.atom (.pointerInc 3))
    (.seq (.atom (.pointerCopy 4 8)) (.atom (.pointerInc 7)))))
private def rowCode := Cmd.seq (.atom (.pointerCopy 4 2)) (.seq (.atom (.pointerConst 7 0))
    (.whileDo (.pointerLE 7 5) digitBody))
private lemma doRow {m : ℕ} (d : Point m→Point m→ℝ) (n k i : ℕ) (hn : 0 < n) (s : Store)
    (base : ℕ) (frame : Frame n k i s) (addr : s.ptrs 3=(base:ℤ)) :
    ∃t z,Executes d rowCode s t z ∧ z ≤ (2*k)*(4*i+10)+6 ∧ Frame n k i t ∧
      t.ptrs 3=((base+2*k:ℕ):ℤ) ∧ t.ptrs 4=(i/rows n k:ℕ) ∧
      (∀a < base,t.imem (a:ℤ)=s.imem (a:ℤ)) ∧
      ∀j < 2*k,t.imem ((base+j:ℕ):ℤ)=(digit n i j:ℤ) := by
  let A (j : ℕ) (v : Store) := Frame n k i v ∧ v.ptrs 3=((base+j:ℕ):ℤ) ∧
    v.ptrs 4=(i/n^j:ℕ) ∧ v.ptrs 7=(j:ℤ) ∧
    (∀a < base,v.imem (a:ℤ)=s.imem (a:ℤ)) ∧ ∀u < j,v.imem ((base+u:ℕ):ℤ)=(digit n i u:ℤ)
  let start := (Op.pointerConst 7 0).eval d ((Op.pointerCopy 4 2).eval d s)
  have init : A 0 start := by
    refine ⟨?_,?_,?_,?_,fun _ _=>rfl,by simp⟩
    · simpa [Frame,start,Op.eval,Function.update] using frame
    all_goals simp [start,Op.eval,Function.update,frame.2.2.1,addr]
  have lp : BoundedSum.LoopBound d digitBody (.pointerLE 7 5) A (2*k) (4*i+8) := by
    constructor
    · intro j v av
      change v.ptrs 7 ≤ v.ptrs 5 ↔ j < 2*k
      rw [av.2.2.2.1,av.1.2.2.2.1];omega
    · intro j hj v av
      obtain ⟨fr,pa,pv,pj,old,earlier⟩ := av
      obtain ⟨u,c,ec,tc,ku,rem,quo⟩ := doDiv d n (i/n^j) hn v fr.1 pv
      let w := (Op.pointerInc 7).eval d ((Op.pointerCopy 4 8).eval d ((Op.pointerInc 3).eval d ((Op.integerStore 3 4).eval d u)))
      have fru : Frame n k i u := by simpa [Frame,ku.2] using fr
      have ua := (ku.2 3 (by decide) (by decide)).trans pa
      have uj := (ku.2 7 (by decide) (by decide)).trans pj
      have hu : i/n^j ≤ i := Nat.div_le_self _ _
      refine ⟨w,_,Executes.seq ec (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _)))),by omega,?_,?_,?_,?_,?_,?_⟩
      · simpa [w,Frame,Op.eval,Function.update] using fru
      · simp [w,Op.eval,Function.update,ua];push_cast;ring
      · simpa [w,Op.eval,Function.update,Nat.div_div_eq_div_mul,pow_succ] using quo
      · simp [w,Op.eval,Function.update,uj]
      · intro a ha
        have ne : (a:ℤ) ≠ (base:ℤ)+(j:ℤ) := by omega
        simpa [w,Op.eval,ua,Function.update_of_ne ne,ku.1] using old a ha
      · intro l hl
        by_cases eq : l=j
        · subst l;simp [w,Op.eval,ua,rem,digit]
        · have ne : (base:ℤ)+(l:ℤ) ≠ (base:ℤ)+(j:ℤ) := by omega
          simpa [w,Op.eval,ua,Function.update_of_ne ne,ku.1] using earlier l (by omega)
  obtain ⟨t,z,ez,tz,last⟩ := BoundedSum.bounded_while_execution d digitBody (.pointerLE 7 5) A (2*k) _ lp 0 (Nat.zero_le _) start init
  refine ⟨t,_,.seq (.atom _ _) (.seq (.atom _ _) ez),?_,last.1,?_,last.2.2.1,last.2.2.2.2.1,last.2.2.2.2.2⟩
  · change z ≤ (2*k-0)*(4*i+10)+2 at tz
    simp only [Nat.sub_zero] at tz
    omega
  · exact last.2.1

private def changes : Op → Option ℕ
  | .pointerConst j _ | .pointerCopy j _ | .pointerInc j | .pointerDec j
  | .pointerAdd j _ _ | .pointerSub j _ _ | .integerLoad j _ => some j
  | _ => none
private def silent (i : ℕ) : Cmd → Prop
  | .skip => True
  | .atom op => changes op ≠ some i
  | .seq a b | .ite _ a b => silent i a ∧ silent i b
  | .whileDo _ a => silent i a
private lemma untouched {n : ℕ} {d : Point n→Point n→ℝ} {c : Cmd} {s t : Store} {z i : ℕ}
    (ex : Executes d c s t z) (h : silent i c) : t.ptrs i=s.ptrs i := by
  induction ex with
  | skip => rfl
  | atom op s => cases op <;> simp_all [silent,changes,Op.eval,Function.update] <;> grind
  | seq _ _ a b => exact (b h.2).trans (a h.1)
  | ite_true _ _ ih => exact ih h.1
  | ite_false _ _ ih => exact ih h.2
  | while_false => rfl
  | while_true _ _ _ a b => exact (b h).trans (a h)
private lemma stayRow {n : ℕ} {d : Point n→Point n→ℝ} {s t : Store} {z i : ℕ}
    (ex : Executes d rowCode s t z) (hi : 9 ≤ i) : t.ptrs i=s.ptrs i := by
  apply untouched ex
  simp [rowCode,digitBody,quotient,divLoop,divBody,silent,changes];omega
private def ops : List Op → Cmd
  | [] => .skip
  | a::l => .seq (.atom a) (ops l)
private noncomputable def afterOps {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) : List Op → Store
  | [] => s
  | a::l => afterOps d (a.eval d s) l
private lemma steps {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (l : List Op) :
    Executes d (ops l) s (afterOps d s l) l.length := by
  induction l generalizing s with
  | nil => exact .skip _
  | cons a l ih => simpa only [ops,afterOps,List.length_cons,Nat.add_comm 1] using
      (Executes.seq (.atom a s) (ih (a.eval d s)))
private lemma addressForm : Form (fun x _=>iv ((addr x.k x.rows 0:ℕ):ℤ)) := by
  have a := Form.total .blocks (Form.size .rows)
  have sum : Form (fun x _=>iv ((x.k*x.rows:ℕ):ℤ)) := by
    convert a using 1
    funext x e;apply Prod.ext <;> simp [iv,World.size,Prod.fst_sum,Prod.snd_sum]
  convert Form.bin .add (.const 3) (Form.bin .add sum sum) using 1
  funext x e;apply Prod.ext <;> simp [iv,Prim.val,addr] <;> ring
private def initOps (h : ℕ) : List Op :=
  [.pointerCopy 11 2,.pointerCopy 12 1,.pointerConst 6 0,.pointerConst 4 0,.pointerConst 2 0,
   .pointerAdd 9 1 1,.pointerConst 1 (h+1:ℕ),.pointerConst 5 (2*(h+1):ℕ),.pointerSub 9 9 5,
   .pointerDec 5,.pointerCopy 3 10,.pointerConst 7 1,.pointerConst 8 (h:ℤ),.integerStore 7 8,
   .pointerInc 7,.integerStore 7 11]
private def finishOps : List Op := [.pointerDec 2,.pointerAdd 2 2 11,.pointerCopy 1 12]
theorem solution : ∃p : Polynomial ℕ,∀h : ℕ,∃cmd : Cmd,∀(x : World) (s : Store),
    0 < x.n → h < x.k → x.k ≤ x.n → Ready x s →
    ∃t z,Executes x.dist cmd s t z ∧ z ≤ p.eval (x.cap + rows x.n (h+1)) ∧
    let y := worldOf x.k (x.rows + rows x.n (h+1)) x.dist t
    Ready y t ∧ y.mem 1=(h:ℤ) ∧ y.mem 2=(x.rows:ℤ) ∧
    (∀r < x.rows,∀j < x.k,center y r j=center x r j ∧ witness y r j=witness x r j) ∧
    (∀u < rows x.n (h+1),∀j ≤ h,center y (x.rows+u) j=(digit x.n u (2*j):ℤ) ∧
      witness y (x.rows+u) j=(digit x.n u (2*j+1):ℤ)) := by
  classical
  obtain ⟨p,hp⟩ := bounded_oracle_expression_compiler _ addressForm
  obtain ⟨locate,loc⟩ := hp 10 (fun _=>0) (by decide) (fun _=>by decide)
  refine ⟨p+(X+C 30)^4,?_⟩;intro h
  let stride : List Op := [.pointerAdd 3 3 9,.pointerInc 2]
  let body := Cmd.seq rowCode (ops stride)
  refine ⟨.seq locate (.seq (ops (initOps h)) (.seq (.whileDo (.pointerLE 4 6) body) (ops finishOps))),?_⟩
  intro x s hn hk hkn ready
  have pn : s.ptrs 0=(x.n:ℤ) := ready.1 .points
  have pk : s.ptrs 1=(x.k:ℤ) := ready.1 .blocks
  have pr : s.ptrs 2=(x.rows:ℤ) := ready.1 .rows
  obtain ⟨a,za,ea,keep,locv,ta⟩ := loc x s (fun _=>x.n) ready (fun _=>pn)
  let A := addr x.k x.rows 0
  let L := 2*x.k
  let D := 2*(h+1)
  let F := rows x.n (h+1)
  have ap : a.ptrs 10=(A:ℤ) := congrArg Prod.fst locv
  have an := (keep.1 0 (by decide)).1.trans pn
  have ak := (keep.1 1 (by decide)).1.trans pk
  have ar := (keep.1 2 (by decide)).1.trans pr
  let st := afterOps x.dist a (initOps h)
  have start := steps x.dist a (initOps h)
  have s1 : st.imem 1=(h:ℤ) := by simp [st,initOps,afterOps,Op.eval,Function.update]
  have s2 : st.imem 2=(x.rows:ℤ) := by simp [st,initOps,afterOps,Op.eval,Function.update,ar]
  have same (i : ℕ) (hi : 3 ≤ i) : st.imem (i:ℤ)=x.mem i := by
    have n1 : (i:ℤ)≠1 := by omega
    have n2 : (i:ℤ)≠2 := by omega
    simpa [st,initOps,afterOps,Op.eval,Function.update,n1,n2,keep.2] using ready.2 i
  let Inv (i : ℕ) (v : Store) := Frame x.n (h+1) i v ∧ v.ptrs 3=((A+i*L:ℕ):ℤ) ∧
    v.ptrs 4=(if i ≤ F then 0 else 1:ℤ) ∧ v.ptrs 9=(L:ℤ)-(D:ℤ) ∧
    v.ptrs 11=(x.rows:ℤ) ∧ v.ptrs 12=(x.k:ℤ) ∧
    (∀a < A,v.imem (a:ℤ)=st.imem (a:ℤ)) ∧
    ∀r < i,∀j < D,v.imem ((A+r*L+j:ℕ):ℤ)=(digit x.n r j:ℤ)
  have init : Inv 0 st := by
    simp [Inv,Frame,st,initOps,afterOps,Op.eval,Function.update,an,ak,ar,ap,L,D,two_mul]
  have pos : 0 < F := pow_pos hn _
  have dL : D ≤ L := by dsimp [D,L];omega
  have loop : BoundedSum.LoopBound x.dist body (.pointerLE 4 6) Inv (F+1) (D*(4*F+10)+8) := by
    constructor
    · intro i v av
      change v.ptrs 4 ≤ v.ptrs 6 ↔ _
      rw [av.2.2.1,av.1.2.2.2.2];by_cases hh : i ≤ F <;> simp [hh] <;> omega
    · intro i hi v av
      obtain ⟨fr,ad,_,gap,oldH,oldK,pre,prior⟩ := av
      obtain ⟨u,z,ez,tz,fu,ua,uq,old,row⟩ := doRow x.dist x.n (h+1) i hn v (A+i*L) fr ad
      let t := afterOps x.dist u stride
      have u9 := (stayRow ez (by decide : 9 ≤ 9)).trans gap
      have u11 := (stayRow ez (by decide : 9 ≤ 11)).trans oldH
      have u12 := (stayRow ez (by decide : 9 ≤ 12)).trans oldK
      have bnd := Nat.mul_le_mul_left D (show 4*i+10 ≤ 4*F+10 by omega)
      refine ⟨t,_,Executes.seq ez (steps _ _ _),by change z+2≤_;change z ≤ D*(4*i+10)+6 at tz;omega,
        ?_,?_,?_,?_,?_,?_,?_,?_⟩
      · obtain ⟨v0,v1,v2,v5,v6⟩ := fu
        simp [t,stride,afterOps,Frame,Op.eval,Function.update,v0,v1,v2,v5,v6]
      · change u.ptrs 3+u.ptrs 9=_
        rw [ua,u9];push_cast;dsimp [D];push_cast;ring
      · change u.ptrs 4=_
        change u.ptrs 4=(i/F:ℕ) at uq
        rcases lt_or_eq_of_le (by omega : i ≤ F) with lt|eq
        · simpa [Nat.div_eq_of_lt lt,show i+1 ≤ F by omega] using uq
        · subst i;simpa [Nat.div_self pos] using uq
      · exact u9
      · exact u11
      · exact u12
      · intro v hv;exact (old _ (by omega)).trans (pre v hv)
      · intro r hr j hj
        by_cases eq : r=i
        · subst r;exact row j hj
        · have lt : r < i := by omega
          have q := Nat.mul_le_mul_right L lt
          have q' := Nat.mul_le_mul_right L (show r+1 ≤ i by omega)
          rw [Nat.succ_mul] at q'
          exact (old _ (by omega)).trans (prior r lt j hj)
  obtain ⟨o,zo,eo,to',last⟩ := BoundedSum.bounded_while_execution _ _ _ Inv (F+1) _ loop 0 (by omega) st init
  let t := afterOps x.dist o finishOps
  obtain ⟨frame,_,_,_,oH,oK,pre,outs⟩ := last
  have A3 : 3 ≤ A := by simp [A,addr]
  refine ⟨t,_,Executes.seq ea (.seq start (.seq eo (steps _ _ _))),?_,⟨?_,fun _=>rfl⟩,
    (pre 1 (by omega)).trans s1,(pre 2 (by omega)).trans s2,?_,?_⟩
  · change za+(16+(zo+3))≤_
    change zo ≤ (F+1-0)*(D*(4*F+10)+8+2)+2 at to'
    simp only [Nat.sub_zero] at to'
    change zo ≤ (F+1)*(D*(4*F+10)+10)+2 at to'
    let M := x.cap+F
    have cap : x.cap ≤ M := by dsimp [M];omega
    have hF : F ≤ M := by dsimp [M];omega
    have hD : D ≤ 2*M := dL.trans (Nat.mul_le_mul_left 2 (show x.k ≤ M by dsimp [M,World.cap];omega))
    have prod := Nat.mul_le_mul hD (show 4*F+10 ≤ 4*M+10 by omega)
    have prod' := Nat.mul_le_mul (show F+1 ≤ M+1 by omega) (show D*(4*F+10)+10 ≤ 2*M*(4*M+10)+10 by omega)
    have pcap : p.eval x.cap ≤ p.eval M := by
      simp only [Polynomial.eval_eq_sum_range]
      exact Finset.sum_le_sum (fun i _=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_left cap i))
    change _ ≤ (p+(X+C 30)^4).eval M
    simp only [eval_add,eval_pow,eval_X,eval_C]
    have big : (M+1)*(2*M*(4*M+10)+10)+21 ≤ (M+30)^4 := by nlinarith [Nat.zero_le (M^4)]
    omega
  · intro ax;obtain ⟨on,_,oi,_,_⟩ := frame
    cases ax <;> simp [t,finishOps,afterOps,Op.eval,Function.update,Axis.reg,World.size,worldOf,on,oi,oH,oK,F]
    all_goals omega
  · intro r hr j hj
    have lim := Nat.mul_le_mul_right x.k (show r+1 ≤ x.rows by omega)
    rw [Nat.succ_mul] at lim
    have l1 : addr x.k r j+1 < A := by dsimp [addr,A];omega
    have low : 3 ≤ addr x.k r j := by simp [addr]
    exact ⟨(pre (addr x.k r j) (by omega)).trans (same _ low),
      (pre (addr x.k r j+1) l1).trans (same (addr x.k r j+1) (by omega))⟩
  · intro r hr j hj
    have one := outs r (by change r < F at hr;omega) (2*j) (by dsimp [D];omega)
    have two := outs r (by change r < F at hr;omega) (2*j+1) (by dsimp [D];omega)
    have ad : addr x.k (x.rows+r) j=A+r*L+2*j := by dsimp [addr,A,L];ring
    change t.imem ((addr x.k (x.rows+r) j:ℕ):ℤ)=_ ∧ t.imem ((addr x.k (x.rows+r) j+1:ℕ):ℤ)=_
    rw [ad,Nat.add_assoc (A+r*L) (2*j) 1];exact ⟨one,two⟩
