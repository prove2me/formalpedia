-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.rows_and_two_tables
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T20:59:07.926238+00:00
-- url     : https://prove2.me/submissions/8985669a-f490-46dc-ad96-f549ca61fb7e

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_five_geometry_tables
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Root_menu_and_separator_rows
import Definitions.Def_StableMSR_RegionalGeometryTables
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.RowComposition

lemma splice {n m} (ps:List Program) {s v t:State} {k b:ℕ} (tail:Program)
    (a:Executes n m (chain ps) s v k) (z:Executes n m tail v t b) :
    ∃j,Executes n m (ps.foldr Program.seq tail) s t j ∧ j+1=k+b := by
  induction ps generalizing s k with
  | nil => cases a; exact ⟨_,z,by omega⟩
  | cons p ps ih =>
    change Executes n m (.seq p (chain ps)) s v k at a
    cases a with
    | seq first rest =>
      obtain ⟨j,h,tm⟩ := ih rest
      exact ⟨_,.seq first h,by omega⟩

lemma joinMiddle {n m s v t k j} (a:Executes n m Scene.geometryPrefix s v k)
    (b:Executes n m Scene.menuAndRows v t j) :
    ∃l,Executes n m (chain (middleList.take 3)) s t l ∧ l≤k+j := by
  change Executes n m (.seq (chain ((listOf src_build_geometry).drop 24)) (chain ((middleList.take 3).drop 1))) v t j at b
  cases b with
  | seq menu rows =>
    obtain ⟨l,ex,tm⟩ := splice ((listOf src_build_geometry).take 24) (chain ((listOf src_build_geometry).drop 24)) a menu
    exact ⟨_,.seq ex rows,by omega⟩

/-- Both graph arrays already decode to the canonical integer instance at the end
of the geometry program. The remaining commands need only preserve their entries. -/
lemma geometryGraph (x:World) (m:Store) (r h:ℕ) (u v:State)
    (image: Scene.GeometryImage m.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) h u v) :
    let d:=integerData x.n x.mem m.imem r h
    let o:=offsets d.n (sizes d.n h)
    (∀j<d.n,1≤v.heap (cursorAt o 0+j) ↔ d.active j=true) ∧
    (∀j<d.n,∀z<d.n,1≤v.heap (cursorAt o 4+(j*d.n+z)) ↔ d.edge j z=true) := by
  dsimp only
  constructor
  · intro j hj
    let p:Fin x.n := ⟨j,hj⟩
    change (1 ≤ v.heap (cursorAt (offsets x.n (sizes x.n h)) 0+p.val)) ↔
      Bits.lookup (fun a : Fin x.n => decide (a ∈ Bits.net m.imem (Bits.piece x.n x.mem (r/x.n) (r%x.n)))) p.val false = true
    rw [image.active p]
    by_cases hp : p ∈ Bits.net m.imem (WindowProfiles.piece x (r/x.n) (r%x.n))
    · have same : p ∈ Bits.net m.imem (Bits.piece x.n x.mem (r/x.n) (r%x.n)) := hp
      simp [Bits.lookup,p.isLt,hp,same]
    · have same : p ∉ Bits.net m.imem (Bits.piece x.n x.mem (r/x.n) (r%x.n)) := hp
      simp [Bits.lookup,p.isLt,hp,same]
  · intro j hj z hz
    let p:Fin x.n := ⟨j,hj⟩
    let a:Fin x.n := ⟨z,hz⟩
    change (1 ≤ v.heap (cursorAt (offsets x.n (sizes x.n h)) 4+(p.val*x.n+a.val))) ↔
      Bits.lookup (fun i:Fin x.n => Bits.lookup (fun b:Fin x.n => decide (i≠b ∧ m.imem (address i b) ≤ 8*(unit x.n:ℤ) ∧ m.imem (address b i) ≤ 8*(unit x.n:ℤ))) a.val false) p.val false=true
    rw [image.edge p a]
    by_cases hpa : p≠a ∧ m.imem (address p a) ≤ 8*(unit x.n:ℤ) ∧ m.imem (address a p) ≤ 8*(unit x.n:ℤ) <;>
      simp [Bits.lookup,p.isLt,a.isLt,hpa]


theorem from_suffix (suffix : ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∀v:Logical.State, Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) u v →
    let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
    ∃t k,Logical.Executes x.n s.imem Scene.menuAndRows v t k ∧
      k ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      t.output=rowTape CandidateRAM.Naming.name d (widthBound (e:ℝ)) ∧
      (let o:=Logical.offsets d.n (Logical.sizes d.n (budget (e:ℝ)))
       (∀j<d.n,t.heap (Logical.cursorAt o 0+j)=v.heap (Logical.cursorAt o 0+j)) ∧
       (∀j<d.n,∀z<d.n,t.heap (Logical.cursorAt o 4+(j*d.n+z))=v.heap (Logical.cursorAt o 4+(j*d.n+z))))) :
∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
    ∃t k,Logical.Executes x.n s.imem (Logical.chain (Logical.middleList.take 3)) u t k ∧
      k ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      t.output=rowTape CandidateRAM.Naming.name d (widthBound (e:ℝ)) ∧
      (let o:=Logical.offsets d.n (Logical.sizes d.n (budget (e:ℝ)))
       (∀j<d.n,1 ≤ t.heap (Logical.cursorAt o 0+j) ↔ d.active j=true) ∧
       (∀j<d.n,∀v<d.n,1 ≤ t.heap (Logical.cursorAt o 4+(j*d.n+v)) ↔ d.edge j v=true)) := by
  obtain ⟨c,D,b,step⟩ := suffix
  refine ⟨c+2350,D+3,b,?_⟩
  intro e ep e1 x m hk hkn ready bounded r p row ptr valid key u start
  have hn : 0<x.n := by omega
  obtain ⟨v,k,geometry,kt,image⟩ :=
    Scene.five_geometry_tables x m r (budget (e:ℝ)) (widthBound (e:ℝ)) u hn valid ready start
  obtain ⟨t,j,tail,jt,output,frames⟩ := step e ep e1 x m hk hkn ready bounded r p row ptr valid key u start v image
  obtain ⟨charge,executed,time⟩ := joinMiddle geometry tail
  have graph := geometryGraph x m r (budget (e:ℝ)) u v image
  refine ⟨t,charge,executed,?_,output,?_⟩
  swap
  · constructor
    · intro j hj; rw [frames.1 j hj]; exact graph.1 j hj
    · intro j hj a ha; rw [frames.2 j hj a ha]; exact graph.2 j hj a ha
  let X := x.cap^(D+3)
  let F := x.n^(b*parameterEnvelope (e:ℝ))
  have nc : x.n+1 ≤ x.cap := by unfold World.cap; omega
  have c1 : 1≤x.cap := by omega
  have f1 : 1≤F := Nat.one_le_pow _ _ hn
  have cd : x.cap^D ≤ X := Nat.pow_le_pow_right c1 (by omega)
  have c3 : x.cap^3 ≤ X := Nat.pow_le_pow_right c1 (by omega)
  have cx : x.cap ≤ X := by
    calc x.cap = x.cap^1 := by simp
         _ ≤ X := Nat.pow_le_pow_right c1 (by omega)
  have n3 : (x.n+1)^3 ≤ X := (Nat.pow_le_pow_left nc 3).trans c3
  have xf : X ≤ X*F := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left X f1
  calc charge ≤ k+j := time
       _ ≤ (350*x.cap+2000*(x.n+1)^3)+c*x.cap^D*F := Nat.add_le_add kt jt
       _ ≤ (350*(X*F)+2000*(X*F))+(c*X)*F :=
         Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (cx.trans xf)) (Nat.mul_le_mul_left _ (n3.trans xf)))
           (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ cd))
       _ = (c+2350)*x.cap^(D+3)*F := by dsimp [X]; ring

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.RowComposition
theorem solution :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
    ∃t k,Logical.Executes x.n s.imem (Logical.chain (Logical.middleList.take 3)) u t k ∧
      k ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      t.output=rowTape CandidateRAM.Naming.name d (widthBound (e:ℝ)) ∧
      (let o:=Logical.offsets d.n (Logical.sizes d.n (budget (e:ℝ)))
       (∀j<d.n,1 ≤ t.heap (Logical.cursorAt o 0+j) ↔ d.active j=true) ∧
       (∀j<d.n,∀v<d.n,1 ≤ t.heap (Logical.cursorAt o 4+(j*d.n+v)) ↔ d.edge j v=true)) := RowComposition.from_suffix Root.menu_and_separator_rows
