-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.emit_canonical_owned_literals
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-26T03:42:08.569824+00:00
-- url     : https://prove2.me/submissions/c78cacfc-d459-4a5c-9bca-7ba869ed6e15

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_scan_owned_literal_rows
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Enumeration_component_and_literal_scans
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
private def pointBit {n : ℕ} (C : Cluster n) (i : ℕ) := if h:i<n then decide ((⟨i,h⟩ : Fin n)∈C) else false
private def minIndex {n : ℕ} (C : Cluster n) := if e:C.Nonempty then (C.min' e).val else n
private def ownerIndex {n : ℕ} (own : Fin n→Fin n) (i : ℕ) := if hi:i<n then (own ⟨i,hi⟩).val else n

private lemma tuple_mem {n : ℕ} (C : Cluster n) (i : ℕ) : i∈Bits.listed C ↔ ∃p∈C,p.val=i := by
  simp [Bits.listed]
private lemma tuple_sorted {n : ℕ} (C : Cluster n) : (Bits.listed C).Pairwise (· < ·) :=
  List.Pairwise.map Fin.val (fun _ _ h=>h) C.sortedLT_sort.pairwise
private lemma literal_mask {n : ℕ} (C : Cluster n) : (List.range n).filter (pointBit C)=Bits.listed C := by
  apply (List.pairwise_lt_range.filter _).eq_of_mem_iff (tuple_sorted C)
  intro i;rw [List.mem_filter,tuple_mem,List.mem_range]
  by_cases hi:i<n
  · simp [pointBit,hi];constructor
    · intro h;exact ⟨⟨i,hi⟩,h,rfl⟩
    · rintro ⟨⟨j,hj⟩,h,rfl⟩;exact h
  · simp [hi];rintro p hp rfl;exact hi p.isLt
private lemma canonical_mask {n : ℕ} (C : Cluster n) : pointList (Bits.listed C)=Bits.listed C := by
  apply (Finset.sortedLT_sort _).pairwise.eq_of_mem_iff (tuple_sorted C)
  simp [pointList]
private lemma tuple_injective {n : ℕ} : Function.Injective (@Bits.listed n) := by
  intro C D eq;ext p
  have member (S : Cluster n) : p.val∈Bits.listed S ↔ p∈S := by
    rw [tuple_mem];constructor
    · rintro ⟨q,h,same⟩;exact Fin.ext same ▸ h
    · intro h; exact ⟨p,h,rfl⟩
  rw [←member C,eq,member]
private lemma tuple_first {n : ℕ} (C : Cluster n) (hn:C.Nonempty) : (Bits.listed C).headD n=(C.min' hn).val := by
  have hlen : 0<C.sort.length := by rw [Finset.length_sort];exact Finset.card_pos.mpr hn
  have h:=C.sorted_zero_eq_min'_aux hlen hn
  unfold Bits.listed
  cases eq : C.sort with
  | nil => simp [eq] at hlen
  | cons q tail =>
    have hh : q=C.min' hn := by simpa [List.get_eq_getElem,eq] using h
    simp [hh]
private lemma chooseMap {α β : Type} (f : α→β) (p : α→Bool) (xs : List α) :
    xs.filterMap (fun q=>if p q then some (f q) else none)=(xs.filter p).map f := by
  induction xs with
  | nil => rfl
  | cons q xs ih=>cases e:p q <;> simp [e,ih]
private lemma distinctErase {α : Type} [DecidableEq α] (xs : List α) : xs.eraseDups.Nodup := by
  have aux (ys acc : List α) (h : acc.Nodup) : (List.eraseDupsBy.loop (· == ·) ys acc).Nodup := by
    induction ys generalizing acc with
    | nil => simpa [List.eraseDupsBy.loop] using h
    | cons a ys ih =>
      unfold List.eraseDupsBy.loop
      split
      · exact ih _ h
      · apply ih;apply List.nodup_cons.mpr;refine ⟨?_,h⟩
        rename_i no;intro ha;have yes := List.any_eq_true.mpr ⟨a,ha,beq_self_eq_true a⟩
        simp_all
  exact aux xs [] (by simp)
private lemma eqBucket {α : Type} (xs ys : List α) (nx : xs.Nodup) (ny : ys.Nodup)
    (same : ∀x,x∈xs ↔ x∈ys) (unique : ∀x∈ys,∀y∈ys,x=y) : xs=ys := by
  apply List.Perm.eq_of_pairwise (le:=fun _ _=>True)
  · intro x y hx hy _ _;exact unique x ((same _).mp hx) y hy
  · exact List.pairwise_of_forall_mem_list fun _ _ _ _=>trivial
  · exact List.pairwise_of_forall_mem_list fun _ _ _ _=>trivial
  · exact (List.perm_ext_iff_of_nodup nx ny).mpr same

private lemma ownedGroups {n : ℕ} (m : ℤ→ℤ) (U : Cluster n) (h c : ℕ) (own : Fin n→Fin n) (v : Fin n)
    (feas : Bits.feasible U (Bits.blocks m U h c)=true) :
    let C := Scene.BlockRows.rowBlock m U h c
    let R := Scene.BlockRows.representatives U C
    (List.range n).flatMap (fun i=> if ownerIndex own i=v.val then
      (List.range n).filterMap (fun q=>if decide (q∈R) && minIndex (C q)==i then
        some (Instr.lit ((List.range n).filter (pointBit (C q)))) else none) else []) =
      (blockList (((Bits.blocks m U h c).filter (Bits.holdsB own v)).map Bits.listed)).map Instr.lit := by
  dsimp only
  let C:=Scene.BlockRows.rowBlock m U h c
  let R:=Scene.BlockRows.representatives U C
  let family:=Bits.blocks m U h c
  let owned:=family.filter (Bits.holdsB own v)
  let rows:=owned.map Bits.listed
  obtain ⟨bounded,cover,inject,_⟩:=Scene.BlockRows.distinct_block_representatives m U h c
  change ∀i∈R,i<n at bounded
  have repr (D : Cluster n) : D∈family ↔ ∃i∈R,C i=D := by
    change D∈Bits.blocks m U h c ↔ _
    rw [←List.mem_toFinset,cover,Finset.mem_image]
  have good : (∀D∈family,D.Nonempty) ∧ (∀D∈family,∀B∈family,D=B ∨ Disjoint D B) := by
    simp only [Bits.feasible,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,Bool.or_eq_true] at feas
    exact feas.1
  have rn (q : ℕ) (hq:q∈R) : (C q).Nonempty := good.1 _ ((repr _).mpr ⟨q,hq,rfl⟩)
  have rowMem (a : List ℕ) : a∈rows ↔ ∃q∈R,ownerIndex own (minIndex (C q))=v.val ∧ Bits.listed (C q)=a := by
    constructor
    · intro ha;obtain ⟨D,hD,rfl⟩:=List.mem_map.mp ha
      obtain ⟨hf,held⟩:=List.mem_filter.mp hD
      obtain ⟨q,hq,rfl⟩:=(repr _).mp hf
      refine ⟨q,hq,?_,rfl⟩
      have he:=rn q hq
      simpa [ownerIndex,minIndex,he,Bits.holdsB,Fin.ext_iff] using held
    · rintro ⟨q,hq,ho,rfl⟩
      apply List.mem_map.mpr;refine ⟨C q,List.mem_filter.mpr ⟨(repr _).mpr ⟨q,hq,rfl⟩,?_⟩,rfl⟩
      simpa [ownerIndex,minIndex,rn q hq,Bits.holdsB,Fin.ext_iff] using ho
  have head (q : ℕ) (hq:q∈R) : (Bits.listed (C q)).headD n=minIndex (C q) := by
    simpa only [minIndex,dif_pos (rn q hq)] using tuple_first (C q) (rn q hq)
  have distinct : rows.Nodup := List.Nodup.map tuple_injective
    (List.Nodup.filter _ (show family.Nodup from distinctErase _))
  have boundedH : ∀a∈rows,a.headD n<n := by
    intro a ha;obtain ⟨q,hq,_,rfl⟩:=(rowMem _).mp ha
    simpa only [head q hq,minIndex,dif_pos (rn q hq)] using ((C q).min' (rn q hq)).isLt
  have separated : ∀a∈rows,∀b∈rows,a≠b → ∀p∈a,p∉b := by
    intro a ha b hb ne p hp hp'
    obtain ⟨q,hq,_,rfl⟩:=(rowMem _).mp ha
    obtain ⟨k,hk,_,rfl⟩:=(rowMem _).mp hb
    obtain ⟨u,hu,rfl⟩:=(tuple_mem _ _).mp hp
    obtain ⟨w,hw,same⟩:=(tuple_mem _ _).mp hp'
    rcases good.2 _ ((repr _).mpr ⟨q,hq,rfl⟩) _ ((repr _).mpr ⟨k,hk,rfl⟩) with e|dis
    · exact ne (congrArg Bits.listed e)
    · exact Finset.disjoint_left.mp dis hu (Fin.ext same ▸ hw)
  have minMem (a : List ℕ) (ha:a∈rows) : a.headD n∈a := by
    cases a with
    | nil => have h:=boundedH [] ha;simp at h
    | cons b bs=>simp
  have norm : rows.map pointList=rows := by
    conv_rhs => rw [←List.map_id rows]
    apply List.map_congr_left;intro a ha
    obtain ⟨q,hq,_,rfl⟩:=(rowMem _).mp ha
    exact canonical_mask _
  have ord:=CandidateRAM.Enumeration.component_and_literal_scans.2 n rows boundedH separated
  change _=(blockList rows).map Instr.lit
  unfold blockList;rw [norm,←ord,List.map_flatMap]
  apply List.flatMap_congr;intro i hi
  let ys:=rows.filter (fun a=>a.headD n==i)
  let pred:=fun q=>decide (q∈R) && minIndex (C q)==i
  by_cases HV : ownerIndex own i=v.val
  · simp only [HV,if_true]
    change (List.range n).filterMap (fun q=>if pred q then some (Instr.lit ((List.range n).filter (pointBit (C q)))) else none)=ys.map Instr.lit
    rw [chooseMap]
    let xs:=((List.range n).filter pred).map (fun q=>Bits.listed (C q))
    have maskMap : (((List.range n).filter pred).map (fun q=>Instr.lit ((List.range n).filter (pointBit (C q)))))=xs.map Instr.lit := by
      simp [xs,List.map_map,literal_mask,Function.comp_def]
    rw [maskMap];congr 1
    have fmem (q:ℕ) : q∈(List.range n).filter pred ↔ q<n ∧ q∈R ∧ minIndex (C q)=i := by simp [pred]
    apply eqBucket
    · apply List.Nodup.map_on _ (List.nodup_range.filter _)
      intro x hx y hy eq; exact inject _ (fmem x |>.mp hx).2.1 _ (fmem y |>.mp hy).2.1 (tuple_injective eq)
    · exact distinct.filter _
    · intro a;constructor
      · intro ha;obtain ⟨q,hq,rfl⟩:=List.mem_map.mp ha
        obtain ⟨_,hr,hm⟩:=(fmem _).mp hq
        exact List.mem_filter.mpr ⟨(rowMem _).mpr ⟨q,hr,hm ▸ HV,rfl⟩,beq_iff_eq.mpr ((head q hr).trans hm)⟩
      · intro ha;obtain ⟨hr,eq⟩:=List.mem_filter.mp ha
        obtain ⟨q,hq,_,rfl⟩:=(rowMem _).mp hr
        exact List.mem_map.mpr ⟨q,(fmem _).mpr ⟨bounded q hq,hq,(head q hq).symm.trans (beq_iff_eq.mp eq)⟩,rfl⟩
    · intro a ha b hb;obtain ⟨aa,ea⟩:=List.mem_filter.mp ha;obtain ⟨bb,eb⟩:=List.mem_filter.mp hb
      by_contra ne
      have e : a.headD n=b.headD n := (beq_iff_eq.mp ea).trans (beq_iff_eq.mp eb).symm
      exact separated a aa b bb ne _ (minMem a aa) (e ▸ minMem b bb)
  · have empty : ys=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr;intro a ha
      obtain ⟨hr,eq⟩:=List.mem_filter.mp ha;obtain ⟨q,hq,hv,rfl⟩:=(rowMem _).mp hr
      have e : minIndex (C q)=i := (head q hq).symm.trans (beq_iff_eq.mp eq)
      exact HV (e ▸ hv)
    change (if ownerIndex own i=v.val then _ else [])=ys.map Instr.lit
    simp [HV,empty]

private lemma linearIndex {n q j T : ℕ} (hq:q<T) (hj:j<n) : q*n+j<T*n := by
  calc q*n+j < q*n+n := Nat.add_lt_add_left hj _
       _ = (q+1)*n := (Nat.succ_mul _ _).symm
       _ ≤ _ := Nat.mul_le_mul_right _ hq

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open Scene.CutTraversal
theorem solution {n : ℕ} (m : ℤ→ℤ) (W : Cluster n) (h : ℕ) (v : Fin n) (j : ℕ) (u g z s : Logical.State)
    (geo : Scene.GeometryImage m W h u g) (menus : Scene.RegionalMenus m W h g z) :
    let M:=sizes n h
    let o:=offsets n M
    ∀ (_ : j<M), 1 ≤ s.heap (cursorAt o 10+(v.val*M+j)) →
    s.reg 6=1 → s.reg 64=(n:ℤ) → s.reg 70=(M:ℤ) → s.reg 226=(v.val:ℤ) → s.reg 227=(j:ℤ) →
    s.reg 72=(cursorAt o 1:ℤ) → s.reg 77=(cursorAt o 6:ℤ) → s.reg 78=(cursorAt o 7:ℤ) → s.reg 80=(cursorAt o 9:ℤ) →
    s.closed=false → s.reg 82=(s.output.length:ℤ) → (∀i<cursorAt o 11,s.heap i=z.heap i) →
    let code:=(SingleCodes.words n h)[j]?.getD 0
    ∃t k, Logical.Executes n m (chain ((listOf src_trial).take 5)) s t k ∧ k ≤ 500*(M+1)+500*(n+1)^4 ∧
      t.heap=s.heap ∧ t.closed=false ∧ t.reg 82=(t.output.length:ℤ) ∧
      t.output=s.output++((arrange (Bits.normalized m W h)).owned v.val code).map Instr.lit := by
  dsimp only
  intro hj ok one size slots vertex word optr rptr lptr mptr ready count stable
  let M:=sizes n h
  let o:=offsets n M
  let U:=Bits.win m W v
  let c:=(SingleCodes.words n h)[j]?.getD 0
  let own:=Bits.owner m (Bits.net m W)
  let C:=Scene.BlockRows.rowBlock m U h c
  let R:=Scene.BlockRows.representatives U C
  let row:=(v.val*M+j)*n
  have slot : v.val*M+j<n*M := linearIndex v.isLt hj
  have bounds (q:ℕ) (hq:q<n) : row+q<n*M*n := linearIndex slot hq
  have end1 : cursorAt o 1+n ≤ cursorAt o 5 := by simp [o,cursorAt,offsets] <;> omega
  have end5 : cursorAt o 5 ≤ cursorAt o 11 := by simp [o,cursorAt,offsets] <;> omega
  have end6 : cursorAt o 6+n*M*n ≤ cursorAt o 11 := by simp [o,cursorAt,offsets] <;> omega
  have end7 : cursorAt o 7+n*M*n ≤ cursorAt o 11 := by simp [o,cursorAt,offsets] <;> omega
  have end9 : cursorAt o 9+n*M*n*n ≤ cursorAt o 11 := by simp [o,cursorAt,offsets] <;> omega
  have end10 : cursorAt o 10+n*M ≤ cursorAt o 11 := by simp [o,cursorAt,offsets] <;> omega
  change ∀i<cursorAt o 11,s.heap i=z.heap i at stable
  change 1 ≤ s.heap (cursorAt o 10+(v.val*M+j)) at ok
  obtain ⟨mark,mn,_,bm,fit⟩:=menus.tables v j hj
  have feasible : Bits.feasible U (Bits.blocks m U h c)=true := by
    rw [stable _ (by omega)] at ok
    change z.heap (cursorAt o 10+(v.val*M+j))=(if Bits.feasible U (Bits.blocks m U h c) then 1 else 0) at fit
    rw [fit] at ok;split at ok <;> simp_all
  obtain ⟨rangeR,cover,_,_⟩:=Scene.BlockRows.distinct_block_representatives m U h c
  have nonempty (q:ℕ) (hq:q∈R) : (C q).Nonempty := by
    have mem : C q ∈ Bits.blocks m U h c := by
      rw [←List.mem_toFinset,cover];exact Finset.mem_image.mpr ⟨q,hq,rfl⟩
    have fe:=feasible;simp only [Bits.feasible,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at fe
    exact fe.1.1 _ mem
  obtain ⟨t,k,run,tm,heap,cl,ct,out⟩:=scan_owned_literal_rows n M v.val j (cursorAt o 1) (cursorAt o 6)
    (cursorAt o 7) (cursorAt o 9) m s (ownerIndex own) (fun q=>minIndex (C q)) (fun q=>decide (q∈R)) (fun q=>pointBit (C q))
    one size slots vertex word optr rptr lptr mptr ready count (by
      intro q hq; rw [stable _ (by omega)]
      have hgeo : z.heap (cursorAt o 1+q)=g.heap (cursorAt o 1+q) := menus.geometry _ (by change _<cursorAt o 5;omega)
      rw [hgeo];simpa [ownerIndex,hq,own] using geo.owner ⟨q,hq⟩) (by
      intro q hq;have b:=bounds q hq;rw [stable _ (by change cursorAt o 6+(row+q)<_;omega)]
      simpa only [decide_eq_true_eq] using mark ⟨q,hq⟩) (by
      intro q hq hr;have b:=bounds q hq;have hm : q∈R:=of_decide_eq_true hr
      rw [stable _ (by change cursorAt o 7+(row+q)<_;omega)]
      simpa only [minIndex,dif_pos (nonempty q hm)] using mn q hm (nonempty q hm)) (by
      intro q hq hr p hp;have b:=linearIndex (bounds q hq) hp
      rw [stable _ (by change cursorAt o 9+((row+q)*n+p)<_;omega)]
      simpa [pointBit,hp] using bm q (of_decide_eq_true hr) ⟨p,hp⟩)
  have ordered:=ownedGroups m U h c own v feasible
  rw [ordered] at out
  exact ⟨t,k,run,tm,heap,cl,ct,by simpa [arrange,Bits.normalized,Bits.lookup,v.isLt,U,own,c] using out⟩

#print axioms solution
