-- Prove2me | solution 1 for StableMSR.Recovery.Supplement.OrderStream.polynomial_family_fraction
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T18:11:57.739807+00:00
-- url     : https://prove2.me/submissions/fdc4b4b7-7be7-4d8d-a2b8-1d223b98ea6d

import Theorems.Thm_StableMSR_Recovery_polynomial_minwise
import Theorems.Thm_StableMSR_Recovery_Supplement_OrderStream_field_size_spec
import Theorems.Thm_StableMSR_Recovery_Supplement_OrderStream_rank_order_is_permutation
import Definitions.Def_StableMSR_PolynomialOrderStream
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial
open StableMSR.Recovery.Supplement StableMSR.Recovery.Supplement.OrderStream
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
open scoped Classical
private noncomputable def coefEquiv (q l : ℕ) [NeZero q] :
    Fin (q^l) ≃ (Fin l→ZMod q) :=
  finFunctionFinEquiv.symm.trans ((Equiv.refl (Fin l)).arrowCongr (ZMod.finEquiv q).toEquiv)
private lemma finCast (q : ℕ) [NeZero q] (i : Fin q) :
    (ZMod.finEquiv q i)=(i.val : ZMod q) := by
  cases q with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ q =>
    apply Fin.ext
    exact (Nat.mod_eq_of_lt i.isLt).symm
private lemma coeff (q l : ℕ) [NeZero q] (c : Fin (q^l)) (i : Fin l) :
    coefEquiv q l c i=((c.val / q^i.val %q : ℕ) : ZMod q) := by
  exact finCast q (finFunctionFinEquiv.symm c i)
private lemma digitHashValue (q l : ℕ) [NeZero q] (c : Fin (q^l)) (x : ℕ) :
    hash q l c.val x=(∑ i : Fin l, coefEquiv q l c i * (x:ZMod q)^i.val).val := by
  unfold OrderStream.hash
  rw [← ZMod.val_natCast]
  apply congrArg ZMod.val
  push_cast
  simp only [coeff]
  exact (Fin.sum_univ_eq_sum_range (fun i=>((c.val/q^i%q:ℕ):ZMod q)*(x:ZMod q)^i) l).symm
private lemma countList {α : Type} (n : ℕ) (f : ℕ→α) (p : α→Prop) [DecidablePred p] :
    (((List.range n).map f).filter (fun a=>decide (p a))).length=
      ((Finset.univ : Finset (Fin n)).filter (fun i=>p (f i.val))).card := by
  classical
  let ls := (List.finRange n).filter (fun i=>decide (p (f i.val)))
  have nd : ls.Nodup := List.filter_sublist.nodup (List.nodup_finRange n)
  have seteq : ls.toFinset=(Finset.univ.filter (fun i : Fin n=>p (f i.val))) := by
    ext i;simp [ls]
  rw [← seteq,List.toFinset_card_of_nodup nd]
  have e : (List.range n).map f=(List.finRange n).map (fun i=>f i.val) := by
    apply List.ext_getElem (by simp);intro i h1 h2;simp
  rw [e,List.filter_map,List.length_map]
  rfl

private lemma key_lt (m c : ℕ) {x y : ℕ} (hx : x < m) (hy : y < m) :
    score m c x < score m c y ↔
    hash (fieldSize m) degreeCount c x < hash (fieldSize m) degreeCount c y ∨
      hash (fieldSize m) degreeCount c x=hash (fieldSize m) degreeCount c y ∧ x < y := by
  unfold score
  let u := hash (fieldSize m) degreeCount c x
  let v := hash (fieldSize m) degreeCount c y
  change u*m+x < v*m+y ↔ u < v ∨ u=v ∧ x < y
  rcases lt_trichotomy u v with h|h|h
  · have b := Nat.mul_le_mul_right m (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at b
    omega
  · rw [h];omega
  · have b := Nat.mul_le_mul_right m (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at b
    omega

theorem solution (m : ℕ) : (family m).length=count m ∧ PermutationFamily m (family m) ∧
    ∀T : Finset ℕ,T⊆Finset.range m → T.Nonempty → ∀z∈T,
      firstFraction (family m) T z ≤ 3/(2*(T.card:ℝ)) := by
  classical
  let q := fieldSize m
  obtain ⟨prime,big,room,upper⟩ := field_size_spec m
  letI : Fact q.Prime := ⟨prime⟩
  have fl : (family m).length=count m := by simp [family]
  have cn : 0 < count m := pow_pos prime.pos _
  refine ⟨fl,⟨fun e=>by rw [← fl,e] at cn;exact Nat.lt_irrefl 0 cn,?_⟩,?_⟩
  · intro π mem
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp mem
    exact (rank_order_is_permutation m c).1
  intro T sub non z hz
  let S := Finset.univ.filter (fun i : Fin m=>i.val∈T)
  let zz : Fin m := ⟨z,Finset.mem_range.mp (sub hz)⟩
  have sz : zz∈S := by simpa [S,zz] using hz
  have card : S.card=T.card := by
    apply Finset.card_bij (fun (i : Fin m) _=>i.val)
    · intro i hi;exact (Finset.mem_filter.mp hi).2
    · intro a _ b _ e;exact Fin.ext e
    · intro y hy;exact ⟨⟨y,Finset.mem_range.mp (sub hy)⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩,rfl⟩
  let H := fun (a : Fin degreeCount→ZMod q) (i : Fin m) => (∑ j : Fin degreeCount, a j*(i.val:ZMod q)^j.val).val
  let wins := fun a : Fin degreeCount→ZMod q => ∀ y∈S, y ≠ zz → H a zz < H a y ∨ (H a zz=H a y ∧ zz < y)
  have matchH (c : Fin (count m)) (i : Fin m) :
      hash q degreeCount c.val i.val=H (coefEquiv q degreeCount c) i := digitHashValue _ _ c i.val
  have test (c : Fin (count m)) : FirstIn T z (row m c.val) ↔ wins (coefEquiv q degreeCount c) := by
    constructor
    · intro h y hy ne
      have neq : y.val ≠ z := fun e=>ne (Fin.ext e)
      have pos := h y.val (Finset.mem_filter.mp hy).2 neq
      have cmp := ((rank_order_is_permutation m c.val).2 _ zz.isLt _ y.isLt).mp pos
      have lex := (key_lt m c.val zz.isLt y.isLt).mp cmp
      rw [← matchH c zz,← matchH c y]
      exact lex
    · intro h y hy ne
      let yy : Fin m := ⟨y,Finset.mem_range.mp (sub hy)⟩
      have cmp := h yy (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩) (fun e=>ne (congrArg Fin.val e))
      apply ((rank_order_is_permutation m c.val).2 _ zz.isLt _ yy.isLt).mpr
      apply (key_lt m c.val zz.isLt yy.isLt).mpr
      rw [← matchH c zz,← matchH c yy] at cmp
      exact cmp
  have tally : ((family m).filter (fun π=>decide (FirstIn T z π))).length=
      ((Finset.univ : Finset (Fin degreeCount→ZMod q)).filter wins).card := by
    rw [family,countList]
    apply Finset.card_equiv (coefEquiv q degreeCount)
    intro c
    constructor
    · intro h;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(test c).mp (Finset.mem_filter.mp h).2⟩
    · intro h;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(test c).mpr (Finset.mem_filter.mp h).2⟩
  have prob := polynomial_minwise q m big room S zz sz
  change (((Finset.univ : Finset (Fin degreeCount→ZMod q)).filter wins).card:ℝ)/(q:ℝ)^degreeCount ≤ 3/(2*(S.card:ℝ)) at prob
  unfold firstFraction
  rw [tally,fl]
  rw [card] at prob
  simpa only [count,Nat.cast_pow] using prob

