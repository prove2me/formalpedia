-- Prove2me | solution 1 for StableMSR.Recovery.Supplement.OrderStream.rank_order_is_permutation
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T18:11:47.170041+00:00
-- url     : https://prove2.me/submissions/7147bbe1-5825-49a0-85f1-71ed1827a92f

import Definitions.Def_StableMSR_PolynomialOrderStream
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial
open StableMSR.Recovery.Supplement StableMSR.Recovery.Supplement.OrderStream
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
open scoped Classical
private lemma cast_list (l : List ℕ) :
    (l : List ℤ)=l.map (fun x : ℕ=>(x:ℤ)) := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg (List.cons (x:ℤ)) ih
private lemma rank_strict (m c : ℕ) (x y : Fin m) (h : score m c x.val < score m c y.val) :
    rank m c x.val < rank m c y.val := by
  apply Finset.card_lt_card
  apply Finset.ssubset_def.mpr
  refine ⟨?_,?_⟩
  · intro a ha
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,lt_trans (Finset.mem_filter.mp ha).2 h⟩
  · intro sub
    have bad := sub (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr x.isLt,h⟩)
    exact (lt_irrefl _) (Finset.mem_filter.mp bad).2
private lemma rank_bound (m c : ℕ) (x : Fin m) : rank m c x.val < m := by
  change ((Finset.range m).filter _).card < m
  conv_rhs => rw [← Finset.card_range m]
  apply Finset.card_lt_card
  refine Finset.ssubset_def.mpr ⟨Finset.filter_subset _ _,?_⟩
  intro sub
  exact (lt_irrefl _) (Finset.mem_filter.mp (sub (Finset.mem_range.mpr x.isLt))).2
private lemma key_inj (m c : ℕ) : Function.Injective (fun x : Fin m=>score m c x.val) := by
  intro x y he
  apply Fin.ext
  have h := congrArg (·%m) he
  simpa [score,Nat.add_mod,Nat.mod_eq_of_lt x.isLt,Nat.mod_eq_of_lt y.isLt] using h
private lemma rank_inj (m c : ℕ) : Function.Injective (fun x : Fin m=>rank m c x.val) := by
  intro x y e
  rcases lt_trichotomy (score m c x.val) (score m c y.val) with h|h|h
  · exact False.elim (ne_of_lt (rank_strict m c x y h) e)
  · exact key_inj m c h
  · exact False.elim (ne_of_lt (rank_strict m c y x h) e.symm)
private noncomputable def ranks (m c : ℕ) : Fin m ≃ Fin m := by
  let f (x : Fin m) : Fin m := ⟨rank m c x.val,rank_bound m c x⟩
  have inj : Function.Injective f := fun _ _ eq => rank_inj m c (congrArg Fin.val eq)
  exact Equiv.ofBijective f ⟨inj,Finite.surjective_of_injective inj⟩
private lemma ranks_val (m c : ℕ) (x : Fin m) : ((ranks m c) x).val = rank m c x.val := rfl
private lemma read_rank (m c : ℕ) (j : Fin m) : atRank m c j.val=((ranks m c).symm j).val := by
  let x := (ranks m c).symm j
  have yes : rank m c x.val=j.val := congrArg Fin.val ((ranks m c).apply_symm_apply j)
  have only (y : ℕ) (mem : y∈Finset.range m) : rank m c y=j.val ↔ y=x.val := by
    constructor
    · intro e
      exact congrArg Fin.val (@rank_inj m c ⟨y,Finset.mem_range.mp mem⟩ x (e.trans yes.symm))
    · rintro rfl;exact yes
  unfold atRank
  calc
    _=∑ y ∈ Finset.range m, if y=x.val then y else 0 := Finset.sum_congr rfl (fun i hi=>by simp only [only i hi])
    _=_ := by simp [x.isLt];rfl
private lemma row_ofFn (m c : ℕ) :
    row m c = List.ofFn (fun i : Fin m=>(((ranks m c).symm i).val:ℤ)) := by
  apply List.ext_getElem (by simp [row])
  intro j hj hj'
  have lt : j < m := by simpa [row] using hj
  simpa [row] using congrArg (fun a : ℕ => (a:ℤ)) (read_rank m c ⟨j,lt⟩)

theorem solution (m c : ℕ) : (row m c).Perm ((List.range m).map (fun i=>(i:ℤ))) ∧
    ∀ x < m, ∀ y < m, (row m c).idxOf (x:ℤ) < (row m c).idxOf (y:ℤ) ↔ score m c x < score m c y := by
  classical
  let e := ranks m c
  have rhs : (List.range m).map (fun i=>(i:ℤ))=(List.range m).map (fun i : ℕ=>(i:ℤ)) := by
    change List.map (fun i : ℤ=>i) ((List.range m):List ℤ)=_
    exact (List.map_id ((List.range m):List ℤ)).trans (cast_list (List.range m))
  rw [rhs]
  have ndRange : ((List.range m).map (fun i : ℕ=>(i:ℤ))).Nodup :=
    List.Nodup.map (fun a b h=> Int.ofNat.inj h) List.nodup_range
  have both : (row m c).Perm ((List.range m).map (fun i : ℕ=>(i:ℤ))) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · rw [row_ofFn]
      exact List.nodup_ofFn_ofInjective (by intro i j eq;apply e.symm.injective;apply Fin.ext;exact Int.ofNat.inj eq)
    · exact ndRange
    · ext a
      simp only [List.mem_toFinset]
      rw [row_ofFn]
      simp only [List.mem_ofFn,List.mem_map,List.mem_range]
      constructor
      · rintro ⟨i,rfl⟩;exact ⟨_,((ranks m c).symm i).isLt,rfl⟩
      · rintro ⟨i,hi,rfl⟩
        exact ⟨e ⟨i,hi⟩,by change ((e.symm (e ⟨i,hi⟩)).val:ℤ)=(i:ℤ);simp⟩
  have index (x : Fin m) : (row m c).idxOf (x.val:ℤ)=rank m c x.val := by
    have nd := both.nodup_iff.mpr ndRange
    have len : (row m c).length=m := by simp [row]
    let i : Fin (row m c).length := ⟨(e x).val,by rw [len];exact (e x).isLt⟩
    have cell : (row m c)[i.val]=(x.val:ℤ) := by
      have val := congrArg (fun a : ℕ=>(a:ℤ)) (read_rank m c (e x))
      simpa [row,i,e] using val
    rw [← cell]
    exact List.get_idxOf nd i
  refine ⟨both,?_⟩
  intro x hx y hy
  rw [index ⟨x,hx⟩,index ⟨y,hy⟩]
  constructor
  · intro lt
    rcases lt_trichotomy (score m c x) (score m c y) with h|h|h
    · exact h
    · have eq := @key_inj m c ⟨x,hx⟩ ⟨y,hy⟩ h
      have := congrArg (fun i : Fin m => rank m c i.val) eq
      omega
    · have := rank_strict m c ⟨y,hy⟩ ⟨x,hx⟩ h;omega
  · exact rank_strict m c ⟨x,hx⟩ ⟨y,hy⟩

