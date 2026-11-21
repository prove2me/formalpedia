-- Prove2me | solution 1 for StableMSR.Recovery.CartesianBallRows.cartesian_row_machine
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T20:34:04.334368+00:00
-- url     : https://prove2.me/submissions/b54dcdf5-f469-4b79-8c7e-59d73181dfdf

import Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_bounded_while_execution
import Definitions.Def_StableMSR_CartesianBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
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
    (frame : Frame n k i s) (addr : s.ptrs 3=((3+i*(2*k):ℕ):ℤ)) :
    ∃t z,Executes d rowCode s t z ∧ z ≤ (2*k)*(4*i+10)+6 ∧ Frame n k i t ∧
      t.ptrs 3=((3+(i+1)*(2*k):ℕ):ℤ) ∧ t.ptrs 4=(i/rows n k:ℕ) ∧
      (∀a < 3+i*(2*k),t.imem (a:ℤ)=s.imem (a:ℤ)) ∧
      ∀j < 2*k,t.imem ((3+i*(2*k)+j:ℕ):ℤ)=(digit n i j:ℤ) := by
  let base := 3+i*(2*k)
  let A (j : ℕ) (v : Store) := Frame n k i v ∧ v.ptrs 3=((base+j:ℕ):ℤ) ∧
    v.ptrs 4=(i/n^j:ℕ) ∧ v.ptrs 7=(j:ℤ) ∧
    (∀a < base,v.imem (a:ℤ)=s.imem (a:ℤ)) ∧ ∀u < j,v.imem ((base+u:ℕ):ℤ)=(digit n i u:ℤ)
  let start := (Op.pointerConst 7 0).eval d ((Op.pointerCopy 4 2).eval d s)
  have init : A 0 start := by
    refine ⟨?_,?_,?_,?_,fun _ _=>rfl,by simp⟩
    · simpa [Frame,start,Op.eval,Function.update] using frame
    all_goals simp [start,Op.eval,Function.update,frame.2.2.1,addr,base]
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
  · simpa only [base,Nat.succ_mul,Nat.add_assoc] using last.2.1

theorem solution : ∃a b : ℕ,0 < a ∧ 0 < b ∧ ∃cmd : Cmd,
    ∀ (n k : ℕ) (d : Point n→Point n→ℝ),1 ≤ k → k ≤ n →
      ∃s z,Executes d cmd (initialStore n k) s z ∧ z ≤ a*n^(b*(k+1)) ∧
        let x := worldOf k (rows n k) d s
        Ready x s ∧ pairs x := by
  classical
  let setup := Cmd.seq (.atom (.integerLoad 0 6)) (.seq (.atom (.pointerConst 1 1))
    (.seq (.atom (.integerLoad 1 1)) (.seq (.atom (.pointerConst 3 3))
    (.seq (.atom (.pointerAdd 5 1 1)) (.atom (.pointerDec 5))))))
  let body := Cmd.seq rowCode (.atom (.pointerInc 2))
  let guard := Cond.pointerLE 4 6
  refine ⟨100,6,by decide,by decide,.seq setup (.seq (.whileDo guard body) (.atom (.pointerDec 2))),?_⟩
  intro n k d hk hkn
  have hn : 0 < n := by omega
  let H := rows n k
  let L := 2*k
  let start := (Op.pointerDec 5).eval d ((Op.pointerAdd 5 1 1).eval d ((Op.pointerConst 3 3).eval d
    ((Op.integerLoad 1 1).eval d ((Op.pointerConst 1 1).eval d ((Op.integerLoad 0 6).eval d (initialStore n k))))))
  have ex0 : Executes d setup (initialStore n k) start 6 :=
    .seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _)))))
  let A (i : ℕ) (s : Store) := Frame n k i s ∧ s.ptrs 3=((3+i*L:ℕ):ℤ) ∧
    s.ptrs 4=(if i ≤ H then 0 else 1 : ℤ) ∧
    ∀r < i,∀l < L,s.imem ((3+r*L+l:ℕ):ℤ)=(digit n r l:ℤ)
  have init : A 0 start := by
    simp [A,Frame,start,Op.eval,Function.update,initialStore,two_mul]
  have hpos : 0 < H := pow_pos hn _
  have lp : BoundedSum.LoopBound d body guard A (H+1) (L*(4*H+10)+7) := by
    constructor
    · intro i s av
      change s.ptrs 4 ≤ s.ptrs 6 ↔ _
      rw [av.2.2.1,av.1.2.2.2.2]
      by_cases hh : i ≤ H <;> simp [hh] <;> omega
    · intro i hi s av
      obtain ⟨fr,addr,flag,prev⟩ := av
      obtain ⟨u,z,ez,tz,fu,ua,uq,old,row⟩ := doRow d n k i hn s fr addr
      let t := (Op.pointerInc 2).eval d u
      have mult := Nat.mul_le_mul_left L (show 4*i+10 ≤ 4*H+10 by omega)
      refine ⟨t,_,Executes.seq ez (.atom _ _),by dsimp [L] at mult ⊢;omega,?_,?_,?_,?_⟩
      · obtain ⟨p0,p1,p2,p5,p6⟩ := fu
        simp [Frame,t,Op.eval,Function.update,p0,p1,p2,p5,p6]
      · simpa [t,Op.eval,Function.update,L] using ua
      · change u.ptrs 4=_
        change u.ptrs 4=(i/H:ℕ) at uq
        rw [uq]
        rcases lt_or_eq_of_le (by omega : i ≤ H) with h|h
        · simp [Nat.div_eq_of_lt h,show i+1 ≤ H by omega]
        · subst i;simp [Nat.div_self hpos]
      · intro r hr j hj
        by_cases h : r=i
        · subst r;exact row j hj
        · have rlt : r < i := by omega
          have mul := Nat.mul_le_mul_right L (show r+1 ≤ i by omega)
          rw [Nat.succ_mul] at mul
          exact (old _ (by dsimp [L] at *;omega)).trans (prev r rlt j hj)
  obtain ⟨out,z,ez,tz,last⟩ := BoundedSum.bounded_while_execution d body guard A (H+1) _ lp 0 (Nat.zero_le _) start init
  let v := (Op.pointerDec 2).eval d out
  refine ⟨v,_,Executes.seq ex0 (.seq ez (.atom _ _)),?_,⟨?_,fun _=>rfl⟩,rfl,?_⟩
  · simp only [Nat.sub_zero] at tz
    have hN : n ≤ H := by
      simpa only [H,rows,pow_one] using Nat.pow_le_pow_right hn (show 1 ≤ 2*k by omega)
    have hL : L ≤ 2*H := by dsimp [L];omega
    have h₁ : L*(4*H+10) ≤ (2*H)*(14*H) := Nat.mul_le_mul hL (by omega)
    have h₂ : (H+1)*(L*(4*H+10)+7+2) ≤ (2*H)*((2*H)*(14*H)+9*H^2) :=
      Nat.mul_le_mul (by omega) (by nlinarith [Nat.one_le_pow 2 H hpos])
    have totalCost : 6+(z+1) ≤ 100*H^3 := by nlinarith [Nat.one_le_pow 3 H hpos]
    apply totalCost.trans
    apply Nat.mul_le_mul_left
    change (n^(2*k))^3 ≤ _
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hn (by omega)
  · intro ax
    obtain ⟨p0,p1,p2,p5,p6⟩ := last.1
    cases ax <;> simp [v,Op.eval,Axis.reg,World.size,worldOf,Function.update,p0,p1,p2,H]
  · intro r hr j hj
    change j < k at hj
    have ri : r < H+1 := by change r < H at hr;omega
    have p := last.2.2.2 r ri
    change out.imem ((addr k r j:ℕ):ℤ)=(digit n r (2*j):ℤ) ∧ out.imem ((addr k r j+1:ℕ):ℤ)=(digit n r (2*j+1):ℤ)
    have aeq : addr k r j=3+r*L+2*j := by dsimp [addr,L];ring
    rw [aeq,Nat.add_assoc (3+r*L) (2*j) 1]
    exact ⟨p (2*j) (by dsimp [L];omega),p (2*j+1) (by dsimp [L];omega)⟩
