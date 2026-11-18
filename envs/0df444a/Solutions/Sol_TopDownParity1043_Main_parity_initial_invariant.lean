-- Prove2me | solution 1 for TopDownParity1043.Main.parity_initial_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:39:01.290475+00:00
-- url     : https://prove2.me/submissions/45c6b9b3-ffb1-4f35-8d72-f06575665b3d

import Mathlib
import Definitions.Def_TopDownParity1043_Main_KW
import Definitions.Def_TopDownParity1043_Main_Limit

set_option autoImplicit false
open TopDownParity1043.Main

private noncomputable def cubeParity {V : Type} [Fintype V] (x : V → Bool) : Bool :=
  decide (Odd ((Finset.univ.filter fun i => x i = true).card))

private def flipBit {V : Type} [DecidableEq V] (i : V) (x : V → Bool) : V → Bool :=
  Function.update x i (!x i)

private theorem flip_involutive {V : Type} [DecidableEq V] (i : V) (x : V → Bool) :
    flipBit i (flipBit i x) = x := by
  funext j
  by_cases hj : j = i <;> simp [flipBit,hj]

private theorem flip_parity {V : Type} [Fintype V] [DecidableEq V]
    (i : V) (x : V → Bool) : cubeParity (flipBit i x) = !cubeParity x := by
  classical
  let A := (Finset.univ.erase i).filter (fun j => x j = true)
  have hbase : (Finset.univ : Finset V) = insert i (Finset.univ.erase i) := by simp
  have hcount : (Finset.univ.filter fun j => x j = true).card = A.card + if x i then 1 else 0 := by
    conv_lhs => rw [hbase,Finset.filter_insert]
    have hiA : i ∉ A := by simp [A]
    cases hx : x i <;> simp [hx,A,Finset.card_insert_of_notMem hiA]
  have hrest : ((Finset.univ.erase i).filter fun j => flipBit i x j = true) = A := by
    apply Finset.filter_congr
    intro j hj
    simp only [Finset.mem_erase] at hj
    simp [flipBit,Function.update_of_ne hj.1]
  have hcount' : (Finset.univ.filter fun j => flipBit i x j = true).card = A.card + if x i then 0 else 1 := by
    conv_lhs => rw [hbase,Finset.filter_insert]
    rw [hrest]
    have hiA : i ∉ A := by simp [A]
    cases hx : x i <;> simp [flipBit,hx,Finset.card_insert_of_notMem hiA]
  unfold cubeParity
  rw [hcount,hcount']
  have hmod : A.card % 2 = 0 ∨ A.card % 2 = 1 := by omega
  rcases hmod with hmod | hmod <;> cases hx : x i <;> simp [hx,Nat.odd_iff,Nat.add_mod,hmod]

private theorem flip_subcube {V : Type} [Fintype V] [DecidableEq V]
    (i : V) (x y : V → Bool) (P : Finset V) (hi : i ∈ P)
    (hy : InSubcube x P y) : InSubcube x P (flipBit i y) := by
  intro j hj
  have hji : j ≠ i := by intro he; subst j; exact hj hi
  simpa only [flipBit,Function.update_of_ne hji] using hy j hj

open Classical in
private theorem parity_fibre_equal {V : Type} [Fintype V] [DecidableEq V]
    (x : V → Bool) (P : Finset V) (hP : P.Nonempty) (b : Bool) :
    (Finset.univ.filter fun y : V → Bool => InSubcube x P y ∧ cubeParity y = b).card =
      (Finset.univ.filter fun y : V → Bool => InSubcube x P y ∧ cubeParity y = !b).card := by
  classical
  obtain ⟨i,hi⟩ := hP
  apply Finset.card_bij (fun y hy => flipBit i y)
  · intro y hy
    obtain ⟨_,hsub,hpar⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,flip_subcube i x y P hi hsub,by rw [flip_parity,hpar]⟩
  · intro y hy z hz he
    have hh := congrArg (flipBit i) he
    simpa only [flip_involutive] using hh
  · intro z hz
    obtain ⟨_,hsub,hpar⟩ := Finset.mem_filter.mp hz
    refine ⟨flipBit i z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,flip_subcube i x z P hi hsub,?_⟩,
      flip_involutive i z⟩
    rw [flip_parity,hpar]
    simp

private def subcubeEquiv {V : Type} [Fintype V] [DecidableEq V]
    (x : V → Bool) (S : Finset V) :
    {y : V → Bool // InSubcube x S y} ≃ (S → Bool) where
  toFun y := project S y.1
  invFun z := ⟨fun i => if hi : i ∈ S then z ⟨i,hi⟩ else x i, by
    intro i hi
    simp [hi]⟩
  left_inv y := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · simp [hi, project]
    · simpa [hi] using (y.2 i hi).symm
  right_inv z := by
    funext i
    simp [project, i.2]

open Classical in
private theorem subcube_card {V : Type} [Fintype V] [DecidableEq V]
    (x : V → Bool) (S : Finset V) :
    (Finset.univ.filter (InSubcube x S)).card = 2 ^ S.card := by
  classical
  rw [← Fintype.card_subtype, Fintype.card_congr (subcubeEquiv x S)]
  simp

open Classical in
private theorem parity_fibre_count {V : Type} [Fintype V] [DecidableEq V]
    (x : V → Bool) (P : Finset V) (hP : P.Nonempty) (b : Bool) :
    ((Finset.univ.filter fun y : V → Bool => InSubcube x P y ∧ cubeParity y = b).card : ℝ) =
      (2 : ℝ)^((P.card : ℝ)-1) := by
  classical
  let A := Finset.univ.filter (InSubcube x P)
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun y => cubeParity y = b)
  have hnot : A.filter (fun y => ¬cubeParity y = b) = A.filter (fun y => cubeParity y = !b) := by
    apply Finset.filter_congr
    intro y hy
    cases b <;> cases cubeParity y <;> simp
  rw [hnot] at hsplit
  have hfilter : ∀ c : Bool, A.filter (fun y => cubeParity y = c) =
      Finset.univ.filter (fun y => InSubcube x P y ∧ cubeParity y = c) := by
    intro c
    exact Finset.filter_filter _ _ _
  simp_rw [hfilter] at hsplit
  rw [← parity_fibre_equal x P hP b, show A.card = 2^P.card from subcube_card x P] at hsplit
  have heq : 2*((Finset.univ.filter fun y : V → Bool => InSubcube x P y ∧ cubeParity y = b).card : ℝ) =
      (2 : ℝ)^P.card := by exact_mod_cast (show 2*(Finset.univ.filter fun y => InSubcube x P y ∧ cubeParity y = b).card = 2^P.card by omega)
  rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast]
  linarith

private theorem weight_nonneg {V : Type} [Fintype V] [DecidableEq V]
    (p : Bias) (R : Finset V) : 0 ≤ setWeight p R := by
  unfold setWeight
  exact mul_nonneg (pow_nonneg p.property.1 _) (pow_nonneg (sub_nonneg.mpr p.property.2) _)

private theorem weight_sum {V : Type} [Fintype V] [DecidableEq V] (p : Bias) :
    ∑ R : Finset V, setWeight p R = 1 := by
  simp only [setWeight, Fintype.sum_pow_mul_eq_add_pow, add_sub_cancel, one_pow]

private theorem prob_nonneg {V : Type} [Fintype V] [DecidableEq V]
    (p : Bias) (E : Finset V → Prop) : 0 ≤ setProb p E := by
  classical
  apply Finset.sum_nonneg
  intro R hR
  split_ifs <;> positivity [weight_nonneg p R]

private theorem prob_le_one {V : Type} [Fintype V] [DecidableEq V]
    (p : Bias) (E : Finset V → Prop) : setProb p E ≤ 1 := by
  classical
  calc
    _ ≤ ∑ R : Finset V, setWeight p R := by
      apply Finset.sum_le_sum
      intro R hR
      split_ifs
      · exact le_rfl
      · exact weight_nonneg p R
    _ = 1 := weight_sum p


private theorem deficit_count_iff {V : Type} [Fintype V] [DecidableEq V]
    (t : ℕ) (X : Finset (V → Bool)) (hX : X.Nonempty) (k : ℝ) :
    setDeficit t X ≤ k ↔ (2 : ℝ) ^ ((t : ℝ)-k) ≤ X.card := by
  have hxpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  unfold setDeficit
  rw [← Real.le_logb_iff_rpow_le (by norm_num) hxpos]
  constructor <;> intro h <;> linarith

private theorem prob_nonempty {V : Type} [Fintype V] [DecidableEq V] (p : Bias) :
    setProb p (fun P : Finset V => P.Nonempty) = 1-(1-(p : ℝ))^(Fintype.card V) := by
  classical
  have hzero : setProb p (fun P : Finset V => P = ∅) = setWeight p (∅ : Finset V) := by
    unfold setProb
    rw [Finset.sum_eq_single (∅ : Finset V)]
    · simp
    · intro R hR hne
      exact if_neg hne
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hcomp : setProb p (fun P : Finset V => P.Nonempty) +
      setProb p (fun P : Finset V => P = ∅) = 1 := by
    unfold setProb
    rw [← Finset.sum_add_distrib]
    convert weight_sum (V := V) p using 1
    apply Finset.sum_congr rfl
    intro P hP
    by_cases he : P = ∅
    · simp [he]
    · simp [he,Finset.nonempty_iff_ne_empty.mpr he]
  rw [hzero] at hcomp
  simpa [setWeight] using (eq_sub_iff_add_eq.mpr hcomp)

private theorem prob_nonempty_lower {V : Type} [Fintype V] [DecidableEq V]
    (p : Bias) (hp : 2 ≤ (Fintype.card V : ℝ)*(p : ℝ)) :
    (3 : ℝ)/4 ≤ setProb p (fun P : Finset V => P.Nonempty) := by
  rw [prob_nonempty]
  have hone : 1-(p : ℝ) ≤ Real.exp (-(p : ℝ)) := by linarith [Real.add_one_le_exp (-(p : ℝ))]
  have hpow := pow_le_pow_left₀ (sub_nonneg.mpr p.property.2) hone (Fintype.card V)
  rw [← Real.exp_nat_mul] at hpow
  have hmon : Real.exp ((Fintype.card V : ℝ)*(-(p : ℝ))) ≤ Real.exp (-2) :=
    Real.exp_le_exp.mpr (by linarith)
  have he2 : 4 ≤ Real.exp (2 : ℝ) := by
    have hh := Real.add_one_le_exp (1 : ℝ)
    rw [show (2 : ℝ) = 1+1 by norm_num,Real.exp_add]
    nlinarith
  have hprod : Real.exp (-2 : ℝ)*Real.exp (2 : ℝ) = 1 := by rw [← Real.exp_add]; norm_num
  have hexp : Real.exp (-2 : ℝ) ≤ 1/4 := by
    nlinarith [mul_nonneg (Real.exp_nonneg (-2)) (sub_nonneg.mpr he2)]
  linarith

private theorem parity_point_limit {V : Type} [Fintype V] [DecidableEq V]
    (p : Bias) (hp : 2 ≤ (Fintype.card V : ℝ)*(p : ℝ)) (b : Bool) (x : V → Bool) :
    IsPKLimit p 1 (Finset.univ.filter fun y => cubeParity y = b) x := by
  classical
  apply (prob_nonempty_lower p hp).trans
  unfold setProb
  apply Finset.sum_le_sum
  intro P hP
  by_cases hn : P.Nonempty
  · have heq : fibre (Finset.univ.filter fun y : V → Bool => cubeParity y = b) x P =
        (Finset.univ.filter fun y => InSubcube x P y ∧ cubeParity y = b) := by
      ext y
      simp only [fibre,Finset.mem_filter,Finset.mem_univ,true_and]
      tauto
    have hh := parity_fibre_count x P hn b
    have hgood : (2 : ℝ)^((P.card : ℝ)-1) ≤
        (fibre (Finset.univ.filter fun y => cubeParity y = b) x P).card := by rw [heq,hh]
    simp [hn,hgood]
  · simp only [if_neg hn]
    split_ifs
    · exact weight_nonneg p P
    · exact le_rfl

private theorem parity_deficit {V : Type} [Fintype V] [DecidableEq V]
    (hn : 0 < Fintype.card V) (b : Bool) :
    SetDeficitLE (Finset.univ.filter fun y : V → Bool => cubeParity y = b) 1 := by
  classical
  have hP : (Finset.univ : Finset V).Nonempty := Finset.card_pos.mp (by simpa using hn)
  have hc := parity_fibre_count (fun _ : V => false) Finset.univ hP b
  simp only [InSubcube,Finset.mem_univ,not_true_eq_false,IsEmpty.forall_iff,implies_true,true_and,
    Finset.card_univ] at hc
  have hpos : 0 < (Finset.univ.filter fun y : V → Bool => cubeParity y = b).card := by
    have hh : (0 : ℝ) < (Finset.univ.filter fun y : V → Bool => cubeParity y = b).card := by
      rw [hc]
      positivity
    exact_mod_cast hh
  refine ⟨Finset.card_pos.mp hpos, ?_⟩
  apply (deficit_count_iff (Fintype.card V) _ (Finset.card_pos.mp hpos) 1).mpr
  exact hc.ge

theorem solution (n : ℕ) (hn : 0 < n) (p : Bias)
    (hp : 2 ≤ (n : ℝ)*(p : ℝ)) :
    SetDeficitLE (Finset.univ.filter fun x : Fin n → Bool => parity n x = false) 1 ∧
    SetDeficitLE (Finset.univ.filter fun x : Fin n → Bool => parity n x = true) 1 ∧
    LeftLimit p 1 (Finset.univ.filter fun x : Fin n → Bool => parity n x = false)
      (Finset.univ.filter fun x : Fin n → Bool => parity n x = true) ∧
    RightLimit p 1 (Finset.univ.filter fun x : Fin n → Bool => parity n x = false)
      (Finset.univ.filter fun x : Fin n → Bool => parity n x = true) := by
  have hfalse := parity_deficit (V := Fin n) (by simpa using hn) false
  have htrue := parity_deficit (V := Fin n) (by simpa using hn) true
  refine ⟨hfalse,htrue,?_,?_⟩
  · intro x hx
    exact parity_point_limit p (by simpa using hp) true x
  · intro y hy
    exact parity_point_limit p (by simpa using hp) false y








