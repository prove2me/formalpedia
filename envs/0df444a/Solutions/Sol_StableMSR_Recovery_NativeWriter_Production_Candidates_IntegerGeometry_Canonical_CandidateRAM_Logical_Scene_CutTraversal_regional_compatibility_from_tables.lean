-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.regional_compatibility_from_tables
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-26T03:14:39.037726+00:00
-- url     : https://prove2.me/submissions/b587c4e4-1c46-4c79-a6b3-d0817b4cd311

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_compute_block_family_compatibility
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_BlockRows_distinct_block_representatives
import Definitions.Def_StableMSR_RegionalMenuImage
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option maxHeartbeats 4100000
set_option maxRecDepth 35000
set_option autoImplicit false

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
private def useRow {n : ℕ} (own : Fin n→Fin n) (a : Fin n) (R : Finset ℕ) (C : ℕ→Cluster n) (j : ℕ) :=
  decide (j∈R) && Bits.touchesB own a (C j)
private lemma frameSlot {n i j : ℕ} (next : j<n) {t : ℕ} (bounds : i<t) : i*n+j<t*n := by
  calc i*n+j < i*n+n := Nat.add_lt_add_left next _
       _ = (i+1)*n := (Nat.succ_mul _ _).symm
       _ ≤ _ := Nat.mul_le_mul_right _ bounds

private lemma readFamily (n h : ℕ) (m : ℤ→ℤ) (W : Cluster n) (a : Fin n) (x : ℕ) (v z s : State)
    (menus : Scene.RegionalMenus m W h v z) (hx : x<sizes n h)
    (stable : ∀q<cursorAt (offsets n (sizes n h)) 11,s.heap q=z.heap q) :
    let M := sizes n h
    let layout := offsets n M
    let c := (SingleCodes.words n h)[x]?.getD 0
    let C := Scene.BlockRows.rowBlock m (Bits.win m W a) h c
    let R := Scene.BlockRows.representatives (Bits.win m W a) C
    let en := useRow (Bits.owner m (Bits.net m W)) a R C
    let row := (a.val*M+x)*n
    (∀i<n,(1 ≤ s.heap (cursorAt layout 6+(row+i)) ∧ 1 ≤ s.heap (cursorAt layout 8+(row+i))) ↔ en i=true) ∧
    (∀i<n,en i=true → ∀p:Fin n,s.heap (cursorAt layout 9+((row+i)*n+p.val))=if p∈C i then 1 else 0) := by
  dsimp only
  let M := sizes n h
  let layout := offsets n M
  let c := (SingleCodes.words n h)[x]?.getD 0
  let C := Scene.BlockRows.rowBlock m (Bits.win m W a) h c
  let R := Scene.BlockRows.representatives (Bits.win m W a) C
  let own := Bits.owner m (Bits.net m W)
  let row := (a.val*M+x)*n
  obtain ⟨reps,_,touch,bits,_⟩:=menus.tables a x hx
  change ∀q<cursorAt layout 11,s.heap q=z.heap q at stable
  have bounds (i : ℕ) (hi:i<n) : row+i<n*M*n := frameSlot hi (frameSlot hx a.isLt)
  have safe6 : cursorAt layout 6+n*M*n ≤ cursorAt layout 11 := by simp [layout,cursorAt,offsets];omega
  have safe8 : cursorAt layout 8+n*M*n ≤ cursorAt layout 11 := by simp [layout,cursorAt,offsets];omega
  have safe9 : cursorAt layout 9+n*M*n*n ≤ cursorAt layout 11 := by simp [layout,cursorAt,offsets];omega
  constructor
  · intro i hi
    have b:=bounds i hi
    change (1 ≤ s.heap (cursorAt layout 6+(row+i)) ∧ 1 ≤ s.heap (cursorAt layout 8+(row+i))) ↔ useRow own a R C i=true
    rw [stable _ (by omega),stable _ (by omega)]
    have rr : z.heap (cursorAt layout 6+(row+i))=(if i∈R then 1 else 0) := reps ⟨i,hi⟩
    rw [rr]
    by_cases hr : i∈R
    · have tt : z.heap (cursorAt layout 8+(row+i))=(if Bits.touchesB own a (C i) then 1 else 0) := touch i hr
      rw [tt];cases e : Bits.touchesB own a (C i) <;> simp [useRow,hr,e]
    · simp [hr,useRow]
  · intro i hi active p
    have b := frameSlot p.isLt (bounds i hi)
    change s.heap (cursorAt layout 9+((row+i)*n+p.val))=_
    rw [stable _ (by omega)]
    exact bits i (by exact of_decide_eq_true (Bool.and_eq_true_iff.mp active).1) p

private lemma semanticTest {n : ℕ} (own : Fin n→Fin n) (a b : Fin n) (P Q : List (Cluster n))
    (A B : ℕ→Cluster n) (RA RB : Finset ℕ)
    (rangeA : ∀i∈RA,i<n) (rangeB : ∀i∈RB,i<n) (PA : P.toFinset=RA.image A) (QB : Q.toFinset=RB.image B) :
    (List.range n).all (fun i=> !useRow own a RA A i || (List.range n).all (fun j=>
      !useRow own b RB B j || decide (Disjoint (A i) (B j) ∨ A i=B j)))=Bits.compat own a b P Q := by
  have reprA (C : Cluster n) : C∈P ↔ ∃i∈RA,A i=C := by
    rw [←List.mem_toFinset,PA,Finset.mem_image]
  have reprB (C : Cluster n) : C∈Q ↔ ∃i∈RB,B i=C := by
    rw [←List.mem_toFinset,QB,Finset.mem_image]
  apply Bool.eq_iff_iff.mpr
  simp only [Bits.compat,List.all_eq_true,List.mem_range,Bool.or_eq_true,Bool.not_eq_true',decide_eq_true_eq]
  constructor
  · intro all C hc D hd
    obtain ⟨i,hi,rfl⟩:= (reprA C).mp hc
    obtain ⟨j,hj,rfl⟩:= (reprB D).mp hd
    have h:=all i (rangeA i hi)
    cases ta : Bits.touchesB own a (A i) <;> cases tb : Bits.touchesB own b (B j) <;>
      simp_all [useRow]
    simpa [hj,tb] using h j (rangeB j hj)
  · intro all i hi
    by_cases hr : i∈RA
    · cases ta : Bits.touchesB own a (A i)
      · simp [useRow,hr,ta]
      · right;intro j hj
        by_cases hs : j∈RB
        · have h:=all (A i) ((reprA _).mpr ⟨i,hr,rfl⟩) (B j) ((reprB _).mpr ⟨j,hs,rfl⟩)
          cases tb : Bits.touchesB own b (B j) <;> simp_all [useRow]
        · simp [useRow,hs]
    · simp [useRow,hr]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open Scene.CutTraversal
theorem solution (n h : ℕ) (m : ℤ→ℤ) (W : Cluster n) (a b : Fin n) (x y : ℕ) (v z s : Logical.State)
    (menus : Scene.RegionalMenus m W h v z) :
    let M := sizes n h
    let o := offsets n M
    ∀ (_ : x<M) (_ : y<M), s.reg 6=1 → s.reg 64=(n:ℤ) → s.reg 70=(M:ℤ) →
      s.reg 203=(a.val:ℤ) → s.reg 204=(x:ℤ) → s.reg 205=(b.val:ℤ) → s.reg 206=(y:ℤ) →
      s.reg 77=(cursorAt o 6:ℤ) → s.reg 79=(cursorAt o 8:ℤ) → s.reg 80=(cursorAt o 9:ℤ) →
      (∀q<cursorAt o 11,s.heap q=z.heap q) →
    let c := (SingleCodes.words n h)[x]?.getD 0
    let k := (SingleCodes.words n h)[y]?.getD 0
    ∃t cost, Logical.Executes n m src_fits s t cost ∧ cost≤1000*(M+1)+1000*(n+1)^3 ∧
      t.reg 217=(if (Bits.normalized m W h).test a.val b.val c k then 1 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  dsimp only
  intro hx hy one size slots va wx vb wy rep touch matrix stable
  let M := sizes n h
  let o := offsets n M
  let c := (SingleCodes.words n h)[x]?.getD 0
  let k := (SingleCodes.words n h)[y]?.getD 0
  let U := Bits.win m W
  let own := Bits.owner m (Bits.net m W)
  let A := Scene.BlockRows.rowBlock m (U a) h c
  let B := Scene.BlockRows.rowBlock m (U b) h k
  let RA := Scene.BlockRows.representatives (U a) A
  let RB := Scene.BlockRows.representatives (U b) B
  obtain ⟨enA,bitA⟩:=readFamily n h m W a x v z s menus hx stable
  obtain ⟨enB,bitB⟩:=readFamily n h m W b y v z s menus hy stable
  obtain ⟨t,l,run,tm,flag,heap,out,cl⟩:=compute_block_family_compatibility n M a.val b.val x y (cursorAt o 6)
    (cursorAt o 8) (cursorAt o 9) m s (useRow own a RA A) (useRow own b RB B) A B one size slots va wx vb wy
    rep touch matrix enA enB bitA bitB
  obtain ⟨rA,pA,_,_⟩:=Scene.BlockRows.distinct_block_representatives m (U a) h c
  obtain ⟨rB,pB,_,_⟩:=Scene.BlockRows.distinct_block_representatives m (U b) h k
  have eq := semanticTest own a b (Bits.blocks m (U a) h c) (Bits.blocks m (U b) h k) A B RA RB rA rB pA pB
  rw [eq] at flag
  exact ⟨t,l,run,tm,by simpa [Bits.normalized,Bits.lookup,a.isLt,b.isLt,U,own,c,k] using flag,heap,out,cl⟩

#print axioms solution
