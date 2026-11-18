-- Prove2me | solution 1 for TopDownParity1043.Main.strong_mirror_coupled
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:26:21.60193+00:00
-- url     : https://prove2.me/submissions/6a5f8622-3eaf-408c-aff0-872b331678d9

import Mathlib
import Definitions.Def_TopDownParity1043_Main_Limit
import Theorems.Thm_TopDownParity1043_Main_robust_return_estimate

set_option autoImplicit false
open TopDownParity1043.Main

private theorem deficit_count_iff {V : Type} [Fintype V] [DecidableEq V]
    (t : ℕ) (X : Finset (V → Bool)) (hX : X.Nonempty) (k : ℝ) :
    setDeficit t X ≤ k ↔ (2 : ℝ) ^ ((t : ℝ)-k) ≤ X.card := by
  have hxpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  unfold setDeficit
  rw [← Real.le_logb_iff_rpow_le (by norm_num) hxpos]
  constructor <;> intro h <;> linarith


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

private theorem guiding_exists {V : Type} [Fintype V] [DecidableEq V]
    (Y : Finset (V → Bool)) (k : ℝ) (hk : 0 ≤ k)
    (x : V → Bool) (P : Finset V) :
    ∃ G : Finset (V → Bool),
      (∀ y ∈ G, InSubcube x P y) ∧
      G.card = ⌈(2 : ℝ)^((P.card : ℝ)-k)⌉₊ ∧
      ((2 : ℝ)^((P.card : ℝ)-k) ≤ (fibre Y x P).card → G ⊆ Y) := by
  classical
  let t := ⌈(2 : ℝ)^((P.card : ℝ)-k)⌉₊
  by_cases hgood : (2 : ℝ)^((P.card : ℝ)-k) ≤ (fibre Y x P).card
  · have ht : t ≤ (fibre Y x P).card := Nat.ceil_le.mpr hgood
    obtain ⟨G,hG,hcard⟩ := Finset.exists_subset_card_eq ht
    refine ⟨G, ?_, hcard, fun _ => hG.trans (Finset.filter_subset _ _)⟩
    intro y hy
    exact (Finset.mem_filter.mp (hG hy)).2
  · let A := Finset.univ.filter (InSubcube x P)
    have ht : t ≤ A.card := by
      apply Nat.ceil_le.mpr
      rw [show A.card = 2^P.card from subcube_card x P]
      push_cast
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    obtain ⟨G,hG,hcard⟩ := Finset.exists_subset_card_eq ht
    exact ⟨G, fun y hy => (Finset.mem_filter.mp (hG hy)).2, hcard, fun hh => (hgood hh).elim⟩

private noncomputable def guiding {V : Type} [Fintype V] [DecidableEq V]
    (Y : Finset (V → Bool)) (k : ℝ) (hk : 0 ≤ k)
    (x : V → Bool) (P : Finset V) : Finset (V → Bool) :=
  Classical.choose (guiding_exists Y k hk x P)

private theorem guiding_mem {V : Type} [Fintype V] [DecidableEq V]
    (Y : Finset (V → Bool)) (k : ℝ) (hk : 0 ≤ k)
    (x : V → Bool) (P : Finset V) (y : V → Bool) (hy : y ∈ guiding Y k hk x P) :
    InSubcube x P y := (Classical.choose_spec (guiding_exists Y k hk x P)).1 y hy

private theorem guiding_card {V : Type} [Fintype V] [DecidableEq V]
    (Y : Finset (V → Bool)) (k : ℝ) (hk : 0 ≤ k)
    (x : V → Bool) (P : Finset V) :
    (guiding Y k hk x P).card = ⌈(2 : ℝ)^((P.card : ℝ)-k)⌉₊ :=
  (Classical.choose_spec (guiding_exists Y k hk x P)).2.1

private theorem guiding_in_Y {V : Type} [Fintype V] [DecidableEq V]
    (Y : Finset (V → Bool)) (k : ℝ) (hk : 0 ≤ k)
    (x : V → Bool) (P : Finset V)
    (hgood : (2 : ℝ)^((P.card : ℝ)-k) ≤ (fibre Y x P).card) :
    guiding Y k hk x P ⊆ Y :=
  (Classical.choose_spec (guiding_exists Y k hk x P)).2.2 hgood

private theorem guiding_card_pos {V : Type} [Fintype V] [DecidableEq V]
    (Y : Finset (V → Bool)) (k : ℝ) (hk : 0 ≤ k)
    (x : V → Bool) (P : Finset V) : 0 < (guiding Y k hk x P).card := by
  rw [guiding_card]
  exact Nat.one_le_ceil_iff.mpr (by positivity)

private theorem guiding_card_lower {V : Type} [Fintype V] [DecidableEq V]
    (Y : Finset (V → Bool)) (k : ℝ) (hk : 0 ≤ k)
    (x : V → Bool) (P : Finset V) :
    (2 : ℝ)^((P.card : ℝ)-k) ≤ (guiding Y k hk x P).card := by
  rw [guiding_card]
  exact Nat.le_ceil _

private noncomputable def guideWeight {V : Type} [Fintype V] [DecidableEq V]
    (Y : Finset (V → Bool)) (k : ℝ) (hk : 0 ≤ k)
    (x : V → Bool) (P : Finset V) (y : V → Bool) : ℝ := by
  classical
  exact if y ∈ guiding Y k hk x P then ((guiding Y k hk x P).card : ℝ)⁻¹ else 0

private theorem guideWeight_nonneg {V : Type} [Fintype V] [DecidableEq V]
    (Y : Finset (V → Bool)) (k : ℝ) (hk : 0 ≤ k)
    (x : V → Bool) (P : Finset V) (y : V → Bool) :
    0 ≤ guideWeight Y k hk x P y := by
  classical
  unfold guideWeight
  split_ifs <;> positivity

private theorem guideWeight_sum {V : Type} [Fintype V] [DecidableEq V]
    (Y : Finset (V → Bool)) (k : ℝ) (hk : 0 ≤ k)
    (x : V → Bool) (P : Finset V) :
    ∑ y : V → Bool, guideWeight Y k hk x P y = 1 := by
  classical
  have hc : (guiding Y k hk x P).card ≠ 0 := ne_of_gt (guiding_card_pos Y k hk x P)
  simp [guideWeight, Finset.sum_ite_mem, hc]

private theorem guideWeight_sum_le_one {V : Type} [Fintype V] [DecidableEq V]
    (Y A : Finset (V → Bool)) (k : ℝ) (hk : 0 ≤ k)
    (x : V → Bool) (P : Finset V) :
    ∑ y ∈ A, guideWeight Y k hk x P y ≤ 1 := by
  calc
    _ ≤ ∑ y : V → Bool, guideWeight Y k hk x P y := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intro y hy hyA; exact guideWeight_nonneg Y k hk x P y)
    _ = 1 := guideWeight_sum Y k hk x P

private noncomputable def guideLaw {V : Type} [Fintype V] [DecidableEq V]
    (X Y : Finset (V → Bool)) (p : Bias) (k : ℝ) (hk : 0 ≤ k)
    (y : V → Bool) : ℝ :=
  (∑ x ∈ X, ∑ P : Finset V, setWeight p P * guideWeight Y k hk x P y) / X.card

private theorem guideLaw_nonneg {V : Type} [Fintype V] [DecidableEq V]
    (X Y : Finset (V → Bool)) (p : Bias) (k : ℝ) (hk : 0 ≤ k)
    (y : V → Bool) : 0 ≤ guideLaw X Y p k hk y := by
  unfold guideLaw
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro x hx
  apply Finset.sum_nonneg
  intro P hP
  exact mul_nonneg (weight_nonneg p P) (guideWeight_nonneg Y k hk x P y)

private theorem guideLaw_sum_exchange {V : Type} [Fintype V] [DecidableEq V]
    (X Y A : Finset (V → Bool)) (p : Bias) (k : ℝ) (hk : 0 ≤ k) :
    (∑ y ∈ A, guideLaw X Y p k hk y) =
      (∑ x ∈ X, ∑ P : Finset V, setWeight p P *
        ∑ y ∈ A, guideWeight Y k hk x P y) / X.card := by
  unfold guideLaw
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  rw [Finset.mul_sum]

private theorem guideLaw_sum {V : Type} [Fintype V] [DecidableEq V]
    (X Y : Finset (V → Bool)) (hX : X.Nonempty) (p : Bias) (k : ℝ) (hk : 0 ≤ k) :
    ∑ y : V → Bool, guideLaw X Y p k hk y = 1 := by
  rw [guideLaw_sum_exchange]
  simp only [guideWeight_sum, mul_one, weight_sum, Finset.sum_const, nsmul_eq_mul,
    mul_one, div_self (show (X.card : ℝ) ≠ 0 by exact_mod_cast ne_of_gt hX.card_pos)]

private theorem guideWeight_column {V : Type} [Fintype V] [DecidableEq V]
    (X Y : Finset (V → Bool)) (k : ℝ) (hk : 0 ≤ k)
    (P : Finset V) (y : V → Bool) :
    ∑ x ∈ X, guideWeight Y k hk x P y ≤ (2 : ℝ)^k := by
  classical
  let t := ⌈(2 : ℝ)^((P.card : ℝ)-k)⌉₊
  let A := X.filter fun x => y ∈ guiding Y k hk x P
  have hcard : A.card ≤ 2 ^ P.card := by
    calc
      _ ≤ (Finset.univ.filter (InSubcube y P)).card := by
        apply Finset.card_le_card
        intro x hx
        have hxy := guiding_mem Y k hk x P y (Finset.mem_filter.mp hx).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro i hi
        exact (hxy i hi).symm
      _ = _ := subcube_card y P
  have ht : (2 : ℝ)^((P.card : ℝ)-k) ≤ t := Nat.le_ceil _
  have htpos : (0 : ℝ) < t := (by positivity : (0 : ℝ) < (2 : ℝ)^((P.card : ℝ)-k)).trans_le ht
  have hsum : (∑ x ∈ X, guideWeight Y k hk x P y) = (A.card : ℝ) / t := by
    simp only [guideWeight, guiding_card]
    rw [← Finset.sum_filter]
    simp [A,t,div_eq_mul_inv]
  rw [hsum]
  apply (div_le_iff₀ htpos).mpr
  calc
    (A.card : ℝ) ≤ (2 : ℝ)^P.card := by exact_mod_cast hcard
    _ = (2 : ℝ)^k * 2^((P.card : ℝ)-k) := by
      rw [← Real.rpow_add (by norm_num)]
      simp
    _ ≤ (2 : ℝ)^k * t := mul_le_mul_of_nonneg_left ht (by positivity)

private theorem guideLaw_cap {V : Type} [Fintype V] [DecidableEq V]
    (X Y : Finset (V → Bool)) (hX : X.Nonempty) (p : Bias)
    (k : ℝ) (hk : 0 ≤ k) (hdef : setDeficit (Fintype.card V) X ≤ k)
    (y : V → Bool) :
    guideLaw X Y p k hk y ≤ (2 : ℝ)^(2*k-(Fintype.card V : ℝ)) := by
  classical
  have hxpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hsize := (deficit_count_iff (Fintype.card V) X hX k).mp hdef
  unfold guideLaw
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  apply (div_le_iff₀ hxpos).mpr
  calc
    _ ≤ ∑ P : Finset V, setWeight p P * (2 : ℝ)^k := by
      apply Finset.sum_le_sum
      intro P hP
      exact mul_le_mul_of_nonneg_left (guideWeight_column X Y k hk P y) (weight_nonneg p P)
    _ = (2 : ℝ)^k := by rw [← Finset.sum_mul, weight_sum, one_mul]
    _ = (2 : ℝ)^(2*k-(Fintype.card V : ℝ)) * 2^((Fintype.card V : ℝ)-k) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring
    _ ≤ (2 : ℝ)^(2*k-(Fintype.card V : ℝ)) * X.card :=
      mul_le_mul_of_nonneg_left hsize (by positivity)

private theorem guideWeight_mass {V : Type} [Fintype V] [DecidableEq V]
    (Y A : Finset (V → Bool)) (k : ℝ) (hk : 0 ≤ k)
    (x : V → Bool) (P : Finset V) :
    (∑ y ∈ A, guideWeight Y k hk x P y) =
      ((A ∩ guiding Y k hk x P).card : ℝ) / (guiding Y k hk x P).card := by
  classical
  unfold guideWeight
  rw [← Finset.sum_filter]
  simp [Finset.filter_mem_eq_inter, div_eq_mul_inv]

private theorem guideLaw_Y_mass {V : Type} [Fintype V] [DecidableEq V]
    (X Y : Finset (V → Bool)) (hX : X.Nonempty) (p : Bias)
    (k : ℝ) (hk : 0 ≤ k) (hlimit : LeftLimit p k X Y) :
    (3 : ℝ)/4 ≤ ∑ y ∈ Y, guideLaw X Y p k hk y := by
  classical
  rw [guideLaw_sum_exchange]
  have hxpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hrow : ∀ x ∈ X, (3 : ℝ)/4 ≤ ∑ P : Finset V,
      setWeight p P * ∑ y ∈ Y, guideWeight Y k hk x P y := by
    intro x hx
    apply (hlimit x hx).trans
    unfold setProb
    apply Finset.sum_le_sum
    intro P hP
    by_cases hg : (2 : ℝ)^((P.card : ℝ)-k) ≤ (fibre Y x P).card
    · rw [if_pos hg, guideWeight_mass, Finset.inter_eq_right.mpr (guiding_in_Y Y k hk x P hg)]
      rw [div_self (show ((guiding Y k hk x P).card : ℝ) ≠ 0 by
        exact_mod_cast ne_of_gt (guiding_card_pos Y k hk x P)), mul_one]
    · rw [if_neg hg]
      exact mul_nonneg (weight_nonneg p P) (Finset.sum_nonneg (fun y hy => guideWeight_nonneg Y k hk x P y))
  apply (le_div_iff₀ hxpos).mpr
  calc
    (3 : ℝ)/4 * X.card = ∑ _ ∈ X, (3 : ℝ)/4 := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum hrow

private noncomputable def badReturn {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (Q : Finset V) (k : ℝ) (y : V → Bool) : Prop :=
  ((fibre X y Q).card : ℝ) < (2 : ℝ)^((Q.card : ℝ)-194*k)

private noncomputable def robustGood {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (x : V → Bool) (P Q : Finset V) (k : ℝ) : Prop := by
  classical
  exact ((Finset.univ.filter fun y : V → Bool => InSubcube x P y ∧ badReturn X Q k y).card : ℝ) ≤
      (2 : ℝ)^((P.card : ℝ)-k-6)

open Classical in
private theorem guide_bad_fraction {V : Type} [Fintype V] [DecidableEq V]
    (X Y : Finset (V → Bool)) (k : ℝ) (hk : 0 ≤ k)
    (x : V → Bool) (P Q : Finset V) (hgood : robustGood X x P Q k) :
    (∑ y ∈ Finset.univ.filter (badReturn X Q k), guideWeight Y k hk x P y) ≤ (1 : ℝ)/64 := by
  classical
  rw [guideWeight_mass]
  have hc : ((Finset.univ.filter (badReturn X Q k) ∩ guiding Y k hk x P).card : ℝ) ≤
      (2 : ℝ)^((P.card : ℝ)-k-6) := by
    apply le_trans _ hgood
    exact_mod_cast Finset.card_le_card (show
      (Finset.univ.filter (badReturn X Q k) ∩ guiding Y k hk x P) ⊆
        (Finset.univ.filter fun y => InSubcube x P y ∧ badReturn X Q k y) from by
      intro y hy
      obtain ⟨hyB,hyG⟩ := Finset.mem_inter.mp hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        guiding_mem Y k hk x P y hyG, (Finset.mem_filter.mp hyB).2⟩)
  have hpow : (2 : ℝ)^((P.card : ℝ)-k-6) = (1/64 : ℝ)*2^((P.card : ℝ)-k) := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num)]
    norm_num [Real.rpow_neg]
    ring
  apply (div_le_iff₀ (show (0 : ℝ) < (guiding Y k hk x P).card by
    exact_mod_cast guiding_card_pos Y k hk x P)).mpr
  exact hc.trans (hpow.trans_le (mul_le_mul_of_nonneg_left (guiding_card_lower Y k hk x P) (by norm_num)))

private theorem guideLaw_weight_exchange {V : Type} [Fintype V] [DecidableEq V]
    (X Y : Finset (V → Bool)) (p : Bias) (k : ℝ) (hk : 0 ≤ k) (f : (V → Bool) → ℝ) :
    (∑ y : V → Bool, guideLaw X Y p k hk y * f y) =
      (∑ x ∈ X, ∑ P : Finset V, setWeight p P *
        ∑ y : V → Bool, guideWeight Y k hk x P y * f y) / X.card := by
  unfold guideLaw
  simp only [Finset.sum_mul, div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  simp only [Finset.mul_sum, mul_assoc]

open Classical in
private theorem guide_bad_exchange {V : Type} [Fintype V] [DecidableEq V]
    (X Y : Finset (V → Bool)) (q : Bias) (k : ℝ) (hk : 0 ≤ k)
    (x : V → Bool) (P : Finset V) :
    (∑ y : V → Bool, guideWeight Y k hk x P y * setProb q (fun Q => badReturn X Q k y)) =
      ∑ Q : Finset V, setWeight q Q *
        ∑ y ∈ Finset.univ.filter (badReturn X Q k), guideWeight Y k hk x P y := by
  classical
  unfold setProb
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Q hQ
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y hy
  split_ifs <;> ring

private theorem guideLaw_bad_bound {V : Type} [Fintype V] [DecidableEq V]
    (X Y : Finset (V → Bool)) (hX : X.Nonempty)
    (k : ℝ) (hk : 1 ≤ k) (hdef : setDeficit (Fintype.card V) X ≤ k)
    (p q s r : Bias) (hs : (s : ℝ) = (p : ℝ)+(q : ℝ)-(p : ℝ)*(q : ℝ))
    (hsr : (s : ℝ)*(r : ℝ) = (p : ℝ)*(1-(q : ℝ)))
    (hr : (r : ℝ) ≤ (32768*k)⁻¹) :
    (∑ y : V → Bool, guideLaw X Y p k (by linarith) y *
      setProb q (fun Q => badReturn X Q k y)) ≤ (1 : ℝ)/16 := by
  classical
  have hk0 : 0 ≤ k := by linarith
  have hxpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hrobust : (31 : ℝ)/32 ≤ (∑ x ∈ X, ∑ P : Finset V,
      setWeight p P * setProb q (fun Q => robustGood X x P Q k)) / X.card :=
    robust_return_estimate V X hX k hk hdef p q s r hs hsr hr
  have hpoint : ∀ x : V → Bool, ∀ P Q : Finset V,
      (∑ y ∈ Finset.univ.filter (badReturn X Q k), guideWeight Y k hk0 x P y) ≤
        65/64 - (if robustGood X x P Q k then (1 : ℝ) else 0) := by
    intro x P Q
    split_ifs with hg
    · have hh := guide_bad_fraction X Y k hk0 x P Q hg
      linarith
    · have hh := guideWeight_sum_le_one Y (Finset.univ.filter (badReturn X Q k)) k hk0 x P
      linarith
  rw [guideLaw_weight_exchange]
  simp_rw [guide_bad_exchange]
  have hineq :
      (∑ x ∈ X, ∑ P : Finset V, setWeight p P *
        ∑ Q : Finset V, setWeight q Q *
          ∑ y ∈ Finset.univ.filter (badReturn X Q k), guideWeight Y k hk0 x P y) / X.card ≤
      (∑ x ∈ X, ∑ P : Finset V, setWeight p P *
        ∑ Q : Finset V, setWeight q Q *
          (65/64 - if robustGood X x P Q k then (1 : ℝ) else 0)) / X.card := by
    apply div_le_div_of_nonneg_right _ hxpos.le
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro P hP
    apply mul_le_mul_of_nonneg_left _ (weight_nonneg p P)
    apply Finset.sum_le_sum
    intro Q hQ
    exact mul_le_mul_of_nonneg_left (hpoint x P Q) (weight_nonneg q Q)
  have hinner : ∀ x P,
      (∑ Q : Finset V, setWeight q Q *
        (65/64 - if robustGood X x P Q k then (1 : ℝ) else 0)) =
      65/64 - setProb q (fun Q => robustGood X x P Q k) := by
    intro x P
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, weight_sum, one_mul,
      mul_ite, mul_one, mul_zero, setProb]
  simp_rw [hinner] at hineq
  have houter : ∀ x,
      (∑ P : Finset V, setWeight p P *
        (65/64 - setProb q (fun Q => robustGood X x P Q k))) =
      65/64 - ∑ P : Finset V, setWeight p P * setProb q (fun Q => robustGood X x P Q k) := by
    intro x
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, weight_sum, one_mul]
  simp_rw [houter] at hineq
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, sub_div, mul_div_cancel_left₀ _ hxpos.ne'] at hineq
  linarith

private theorem prob_bad_good {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (q : Bias) (k : ℝ) (y : V → Bool) :
    setProb q (fun Q => badReturn X Q k y) +
      setProb q (fun Q => (2 : ℝ)^((Q.card : ℝ)-194*k) ≤ (fibre X y Q).card) = 1 := by
  classical
  unfold setProb badReturn
  rw [← Finset.sum_add_distrib]
  convert weight_sum (V := V) q using 1
  apply Finset.sum_congr rfl
  intro Q hQ
  by_cases hg : (2 : ℝ)^((Q.card : ℝ)-194*k) ≤ (fibre X y Q).card
  · simp [hg,not_lt.mpr hg]
  · simp [hg,lt_of_not_ge hg]

open Classical in
private theorem guideLaw_nonlimit_mass {V : Type} [Fintype V] [DecidableEq V]
    (X Y : Finset (V → Bool)) (p q : Bias) (k : ℝ) (hk : 0 ≤ k)
    (hbad : (∑ y : V → Bool, guideLaw X Y p k hk y *
      setProb q (fun Q => badReturn X Q k y)) ≤ (1 : ℝ)/16) :
    (∑ y ∈ Finset.univ.filter (fun y => ¬IsPKLimit q (194*k) X y),
      guideLaw X Y p k hk y) ≤ (1 : ℝ)/4 := by
  classical
  have hpoint : ∀ y : V → Bool,
      (if ¬IsPKLimit q (194*k) X y then guideLaw X Y p k hk y else 0) ≤
        4*(guideLaw X Y p k hk y * setProb q (fun Q => badReturn X Q k y)) := by
    intro y
    by_cases hn : ¬IsPKLimit q (194*k) X y
    · rw [if_pos hn]
      have he := prob_bad_good X q k y
      have hh : setProb q (fun Q => (2 : ℝ)^((Q.card : ℝ)-194*k) ≤ (fibre X y Q).card) < 3/4 :=
        lt_of_not_ge hn
      have hb : 1/4 ≤ setProb q (fun Q => badReturn X Q k y) := by linarith
      have hm := mul_le_mul_of_nonneg_left hb (guideLaw_nonneg X Y p k hk y)
      nlinarith
    · rw [if_neg hn]
      exact mul_nonneg (by norm_num) (mul_nonneg (guideLaw_nonneg X Y p k hk y) (prob_nonneg q _))
  rw [Finset.sum_filter]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun y hy => hpoint y)
  rw [← Finset.mul_sum] at hh
  linarith

theorem solution (V : Type) [Fintype V] [DecidableEq V]
    (X Y : Finset (V → Bool)) (k : ℝ) (hk : 1 ≤ k)
    (p q s r : Bias)
    (hX : SetDeficitLE X k) (hlimit : LeftLimit p k X Y)
    (hs : (s : ℝ) = (p : ℝ)+(q : ℝ)-(p : ℝ)*(q : ℝ))
    (hsr : (s : ℝ)*(r : ℝ) = (p : ℝ)*(1-(q : ℝ)))
    (hr : (r : ℝ) ≤ (32768*k)⁻¹) :
    ∃ Y' : Finset (V → Bool), Y' ⊆ Y ∧ SetDeficitLE Y' (2*k+2) ∧
      RightLimit q (194*k) X Y' := by
  classical
  have hk0 : 0 ≤ k := by linarith
  let μ := guideLaw X Y p k hk0
  let Y' := Y.filter (fun y => IsPKLimit q (194*k) X y)
  let B := Finset.univ.filter (fun y : V → Bool => ¬IsPKLimit q (194*k) X y)
  have hbad := guideLaw_bad_bound X Y hX.1 k hk hX.2 p q s r hs hsr hr
  have hB : (∑ y ∈ B, μ y) ≤ (1 : ℝ)/4 :=
    guideLaw_nonlimit_mass X Y p q k hk0 hbad
  have hY : (3 : ℝ)/4 ≤ ∑ y ∈ Y, μ y := guideLaw_Y_mass X Y hX.1 p k hk0 hlimit
  have hsplit : (∑ y ∈ Y', μ y) +
      (∑ y ∈ Y.filter (fun y => ¬IsPKLimit q (194*k) X y), μ y) = ∑ y ∈ Y, μ y :=
    Finset.sum_filter_add_sum_filter_not Y (fun y => IsPKLimit q (194*k) X y) μ
  have hsub : (Y.filter (fun y => ¬IsPKLimit q (194*k) X y)) ⊆ B := by
    intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
  have hB' : (∑ y ∈ Y.filter (fun y => ¬IsPKLimit q (194*k) X y), μ y) ≤ 1/4 := by
    apply le_trans _ hB
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro y hy hyY
    exact guideLaw_nonneg X Y p k hk0 y
  have hmass : (1 : ℝ)/4 ≤ ∑ y ∈ Y', μ y := by linarith
  have hY' : Y'.Nonempty := by
    by_contra he
    have hz : Y' = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    norm_num [hz] at hmass
  refine ⟨Y', Finset.filter_subset _ _, ⟨hY', ?_⟩, ?_⟩
  · apply (deficit_count_iff (Fintype.card V) Y' hY' (2*k+2)).mpr
    have hcap : (∑ y ∈ Y', μ y) ≤ (Y'.card : ℝ) * (2 : ℝ)^(2*k-(Fintype.card V : ℝ)) := by
      calc
        _ ≤ ∑ _ ∈ Y', (2 : ℝ)^(2*k-(Fintype.card V : ℝ)) := by
          apply Finset.sum_le_sum
          intro y hy
          exact guideLaw_cap X Y hX.1 p k hk0 hX.2 y
        _ = _ := by simp
    have hp : 0 < (2 : ℝ)^(2*k-(Fintype.card V : ℝ)) := by positivity
    have heq : (2 : ℝ)^((Fintype.card V : ℝ)-(2*k+2)) *
        (2 : ℝ)^(2*k-(Fintype.card V : ℝ)) = 1/4 := by
      rw [← Real.rpow_add (by norm_num)]
      rw [show (Fintype.card V : ℝ)-(2*k+2)+(2*k-(Fintype.card V : ℝ)) = -2 by ring]
      norm_num [Real.rpow_neg]
    nlinarith
  · intro y hy
    exact (Finset.mem_filter.mp hy).2



