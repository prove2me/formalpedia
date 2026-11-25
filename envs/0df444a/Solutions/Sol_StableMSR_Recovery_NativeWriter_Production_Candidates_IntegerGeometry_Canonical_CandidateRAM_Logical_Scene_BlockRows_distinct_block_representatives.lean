-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.distinct_block_representatives
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-25T04:49:37.967664+00:00
-- url     : https://prove2.me/submissions/034e5aa1-8363-4b88-b285-11b3f64d140c

import Definitions.Def_StableMSR_VertexBlockRows
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
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows
private lemma rep_mem {n : ℕ} {W : Cluster n} {C : ℕ → Cluster n} {i : ℕ} :
    i ∈ representatives W C ↔
      (∃ p ∈ W, p.val = i) ∧ ∀ q ∈ W, q.val < i → C q.val ≠ C i := by
  simp only [representatives, Finset.mem_filter, Finset.mem_image]

private lemma first_of_seed {n : ℕ} {W : Cluster n} {C : ℕ → Cluster n} (p : Fin n) (hp : p ∈ W) :
    ∃ i ∈ representatives W C, i ≤ p.val ∧ C i = C p.val := by
  classical
  let S := (W.image Fin.val).filter (fun i => C i = C p.val)
  have hpS : p.val ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,rfl⟩
  let a := S.min' ⟨_,hpS⟩
  have ha : a ∈ S := Finset.min'_mem _ _
  obtain ⟨haW,haC⟩ := Finset.mem_filter.mp ha
  refine ⟨a,rep_mem.mpr ⟨Finset.mem_image.mp haW,?_⟩,Finset.min'_le _ _ hpS,haC⟩
  intro q hq lt eq
  have hqS : q.val ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨q,hq,rfl⟩,eq.trans haC⟩
  exact (Nat.not_le_of_lt lt) (Finset.min'_le _ _ hqS)

lemma least_earlier {n : ℕ} {W : Cluster n} {C : ℕ → Cluster n} (p : Fin n) (hp : p ∈ W) :
    p.val ∈ representatives W C ↔ ¬∃ i ∈ representatives W C, i < p.val ∧ C i = C p.val := by
  constructor
  · rintro current ⟨i,hi,lt,eq⟩
    obtain ⟨q,hq,rfl⟩ := (rep_mem.mp hi).1
    exact (rep_mem.mp current).2 q hq lt eq
  · intro none
    obtain ⟨i,hi,le,eq⟩ := first_of_seed (C:=C) p hp
    have same : i=p.val := by
      by_contra ne
      exact none ⟨i,hi,by omega,eq⟩
    simpa only [← same] using hi

lemma families
    {n : ℕ} (m : ℤ → ℤ) (W : Cluster n) (h c : ℕ) :
    let C := rowBlock m W h c
    let R := representatives W C
    (∀ i ∈ R, i < n) ∧
    (Bits.blocks m W h c).toFinset = R.image C ∧
    (∀ i ∈ R, ∀ j ∈ R, C i = C j → i = j) ∧
    (∀ p ∈ W, p.val ∈ R ↔ ¬∃ i ∈ R, i < p.val ∧ C i = C p.val)
    := by
  classical
  let C := rowBlock m W h c
  let R := representatives W C
  change (∀ i ∈ R, i < n) ∧ (Bits.blocks m W h c).toFinset = R.image C ∧
    (∀ i ∈ R, ∀ j ∈ R, C i=C j → i=j) ∧ _
  have atPoint (q : Fin n) : C q.val = Bits.block m W h c q := by
    simp [C,rowBlock,Bits.lookup,q.isLt]
  refine ⟨?_,?_,?_,fun p hp => least_earlier p hp⟩
  · intro i hi
    obtain ⟨q,_,rfl⟩ := (rep_mem.mp hi).1
    exact q.isLt
  · ext A
    simp only [Bits.blocks,List.mem_toFinset,List.mem_eraseDups,List.mem_map,Finset.mem_sort,Finset.mem_image]
    constructor
    · rintro ⟨q,hq,rfl⟩
      obtain ⟨i,hi,_,eq⟩ := first_of_seed (C:=C) q hq
      exact ⟨i,hi,eq.trans (atPoint q)⟩
    · rintro ⟨i,hi,rfl⟩
      obtain ⟨q,hq,rfl⟩ := (rep_mem.mp hi).1
      exact ⟨q,hq,(atPoint q).symm⟩
  · intro i hi j hj eq
    have neq (a b : ℕ) (ha : a ∈ R) (hb : b ∈ R) (lt : a<b) : C a ≠ C b := by
      obtain ⟨q,hq,rfl⟩ := (rep_mem.mp ha).1
      exact (rep_mem.mp hb).2 q hq lt
    rcases lt_trichotomy i j with lt|e|gt
    · exact False.elim (neq i j hi hj lt eq)
    · exact e
    · exact False.elim (neq j i hj hi gt eq.symm)

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows
theorem solution
    {n : ℕ} (m : ℤ → ℤ) (W : Cluster n) (h c : ℕ) :
    let C := rowBlock m W h c
    let R := representatives W C
    (∀ i ∈ R, i < n) ∧
    (Bits.blocks m W h c).toFinset = R.image C ∧
    (∀ i ∈ R, ∀ j ∈ R, C i = C j → i = j) ∧
    (∀ p ∈ W, p.val ∈ R ↔ ¬∃ i ∈ R, i < p.val ∧ C i = C p.val)
 := StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.families m W h c
