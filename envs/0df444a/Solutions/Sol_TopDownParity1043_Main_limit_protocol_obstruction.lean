-- Prove2me | solution 1 for TopDownParity1043.Main.limit_protocol_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:34:02.526068+00:00
-- url     : https://prove2.me/submissions/94c6f4d6-0329-4a21-860b-9d41b3357c76

import Mathlib
import Definitions.Def_TopDownParity1043_Main_KW
import Definitions.Def_TopDownParity1043_Main_Limit
import Theorems.Thm_TopDownParity1043_Main_strong_mirror_coupled
import Theorems.Thm_TopDownParity1043_Main_random_set_restriction

set_option autoImplicit false
open TopDownParity1043.Main

private theorem deficit_count_iff {V : Type} [Fintype V] [DecidableEq V]
    (t : ℕ) (X : Finset (V → Bool)) (hX : X.Nonempty) (k : ℝ) :
    setDeficit t X ≤ k ↔ (2 : ℝ) ^ ((t : ℝ)-k) ≤ X.card := by
  have hxpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  unfold setDeficit
  rw [← Real.le_logb_iff_rpow_le (by norm_num) hxpos]
  constructor <;> intro h <;> linarith

private theorem mirror_linear {V : Type} [Fintype V] [DecidableEq V]
    (X Y : Finset (V → Bool)) (k : ℝ) (hk : 1 ≤ k)
    (p : Bias) (hp : 0 < (p : ℝ)) (hb : 32768*k*(p : ℝ) ≤ 1/2)
    (hX : SetDeficitLE X k) (hlimit : LeftLimit p k X Y) :
    ∃ q : Bias, 0 < (q : ℝ) ∧ (q : ℝ) = 32768*k*(p : ℝ) ∧
      ∃ Y' : Finset (V → Bool), Y' ⊆ Y ∧ SetDeficitLE Y' (2*k+2) ∧
        RightLimit q (194*k) X Y' := by
  have hk0 : 0 < k := by linarith
  let q : Bias := ⟨32768*k*(p : ℝ), ⟨by positivity, by linarith⟩⟩
  have hq : 0 < (q : ℝ) := by dsimp [q]; positivity
  let s : Bias := ⟨(p : ℝ)+(q : ℝ)-(p : ℝ)*(q : ℝ), by
    constructor
    · nlinarith [p.property.1, p.property.2, q.property.1, q.property.2]
    · nlinarith [mul_nonneg (sub_nonneg.mpr p.property.2) (sub_nonneg.mpr q.property.2)]⟩
  have hspos : 0 < (s : ℝ) := by
    have hsq : (q : ℝ) ≤ (s : ℝ) := by
      dsimp [s]
      nlinarith [mul_nonneg p.property.1 (sub_nonneg.mpr q.property.2)]
    exact hq.trans_le hsq
  let r : Bias := ⟨(p : ℝ)*(1-(q : ℝ))/(s : ℝ), by
    constructor
    · exact div_nonneg (mul_nonneg p.property.1 (sub_nonneg.mpr q.property.2)) hspos.le
    · apply (div_le_one hspos).mpr
      dsimp [s]
      linarith [q.property.1]⟩
  have hsr : (s : ℝ)*(r : ℝ) = (p : ℝ)*(1-(q : ℝ)) := by
    dsimp [r]
    field_simp
  have hr : (r : ℝ) ≤ (32768*k)⁻¹ := by
    change (p : ℝ)*(1-(q : ℝ))/(s : ℝ) ≤ (32768*k)⁻¹
    apply (div_le_iff₀ hspos).mpr
    have hsq : (q : ℝ) ≤ (s : ℝ) := by
      dsimp [s]
      nlinarith [mul_nonneg p.property.1 (sub_nonneg.mpr q.property.2)]
    have hh : (32768*k)⁻¹ * (q : ℝ) = (p : ℝ) := by
      dsimp [q]
      field_simp
    have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (32768*k)⁻¹ by positivity)
    rw [hh] at hmul
    nlinarith [mul_nonneg p.property.1 q.property.1]
  refine ⟨q,hq,rfl, ?_⟩
  exact strong_mirror_coupled V X Y k hk p q s r hX hlimit rfl hsr hr

private theorem message_class {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (k : ℝ) (hX : SetDeficitLE X k)
    (m b : ℕ) (hb : b ≤ 2^m) (msg : (V → Bool) → Fin b) :
    ∃ j : Fin b, SetDeficitLE (X.filter fun x => msg x = j) (k+m) := by
  classical
  obtain ⟨x,hx⟩ := hX.1
  have ht : (Finset.univ : Finset (Fin b)).Nonempty := ⟨msg x,Finset.mem_univ _⟩
  have hcount := (deficit_count_iff (Fintype.card V) X hX.1 k).mp hX.2
  have hm : (b : ℝ) ≤ (2 : ℝ)^m := by exact_mod_cast hb
  have hnum : (Finset.univ : Finset (Fin b)).card •
      ((2 : ℝ)^((Fintype.card V : ℝ)-(k+m))) ≤ (X.card : ℝ) := by
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc
      _ ≤ (2 : ℝ)^m * 2^((Fintype.card V : ℝ)-(k+m)) :=
        mul_le_mul_of_nonneg_right hm (by positivity)
      _ = (2 : ℝ)^((Fintype.card V : ℝ)-k) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
        congr 1
        ring
      _ ≤ _ := hcount
  obtain ⟨j,hj,hcard⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := X) (t := (Finset.univ : Finset (Fin b))) (f := msg)
    (fun x hx => Finset.mem_univ _) ht hnum
  have hpos : 0 < (X.filter fun x => msg x = j).card := by
    have hh : (0 : ℝ) < (X.filter fun x => msg x = j).card :=
      (show (0 : ℝ) < (2 : ℝ)^((Fintype.card V : ℝ)-(k+m)) by positivity).trans_le hcard
    exact_mod_cast hh
  refine ⟨j,⟨Finset.card_pos.mp hpos, ?_⟩⟩
  exact (deficit_count_iff (Fintype.card V) _ (Finset.card_pos.mp hpos) (k+m)).mpr hcard

private theorem coordinate_prob {V : Type} [Fintype V] [DecidableEq V]
    (p : Bias) (i : V) : setProb p (fun P : Finset V => i ∈ P) = (p : ℝ) := by
  classical
  let S : Finset V := {i}
  have hS : Fintype.card S = 1 := by simp [S]
  have hU : (Finset.univ : Finset (Finset S)) = {∅,Finset.univ} := by
    ext R
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases he : R = ∅
    · exact Or.inl he
    · right
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      simp only [Finset.card_univ,hS]
      omega
  have hmap : (Finset.univ : Finset S).map (Function.Embedding.subtype _) = S := by
    ext j
    constructor
    · intro hj
      obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hj
      exact v.2
    · intro hj
      exact Finset.mem_map.mpr ⟨⟨j,hj⟩,Finset.mem_univ _,rfl⟩
  have he := random_set_restriction V p S (fun R => if i ∈ R then (1 : ℝ) else 0)
  have hleft : (∑ T : Finset V, setWeight p T * (if i ∈ T ∩ S then (1 : ℝ) else 0)) =
      setProb p (fun P : Finset V => i ∈ P) := by
    unfold setProb
    apply Finset.sum_congr rfl
    intro T hT
    by_cases hi : i ∈ T <;> simp [S,hi]
  rw [hleft] at he
  rw [he, hU]
  have hne : (∅ : Finset S) ≠ Finset.univ := by
    intro hh
    have hc := congrArg Finset.card hh
    simp [hS] at hc
  rw [Finset.sum_pair hne]
  simp [hmap,S,setWeight,hS]

private theorem limit_coordinate_obstruction {V : Type} [Fintype V] [DecidableEq V]
    (X Y : Finset (V → Bool)) (hX : X.Nonempty) (p : Bias) (k : ℝ)
    (hp : (p : ℝ) ≤ 1/2) (hlimit : LeftLimit p k X Y)
    (i : V) (hopp : ∀ x ∈ X, ∀ y ∈ Y, x i ≠ y i) : False := by
  classical
  obtain ⟨x,hx⟩ := hX
  have hmass := hlimit x hx
  have hle : setProb p (fun P => (2 : ℝ)^((P.card : ℝ)-k) ≤ (fibre Y x P).card) ≤
      setProb p (fun P : Finset V => i ∈ P) := by
    unfold setProb
    apply Finset.sum_le_sum
    intro P hP
    by_cases hg : (2 : ℝ)^((P.card : ℝ)-k) ≤ (fibre Y x P).card
    · have hpos : 0 < (fibre Y x P).card := by
        have hh : (0 : ℝ) < (fibre Y x P).card :=
          (show (0 : ℝ) < (2 : ℝ)^((P.card : ℝ)-k) by positivity).trans_le hg
        exact_mod_cast hh
      obtain ⟨y,hy⟩ := Finset.card_pos.mp hpos
      obtain ⟨hyY,hxy⟩ := Finset.mem_filter.mp hy
      have hi : i ∈ P := by
        by_contra hn
        exact hopp x hx y hyY (hxy i hn).symm
      simp [hg,hi]
    · simp only [if_neg hg]
      split_ifs
      · unfold setWeight
        positivity [p.property.1, p.property.2]
      · exact le_rfl
  rw [coordinate_prob] at hle
  change (3 : ℝ)/4 ≤ _ at hmass
  linarith

private theorem limit_mono_k {V : Type} [Fintype V] [DecidableEq V]
    (p : Bias) (k l : ℝ) (hkl : k ≤ l) (Y : Finset (V → Bool)) (x : V → Bool)
    (h : IsPKLimit p k Y x) : IsPKLimit p l Y x := by
  classical
  apply h.trans
  unfold setProb
  apply Finset.sum_le_sum
  intro P hP
  by_cases hg : (2 : ℝ)^((P.card : ℝ)-k) ≤ (fibre Y x P).card
  · have hh : (2 : ℝ)^((P.card : ℝ)-l) ≤ (fibre Y x P).card := by
      apply le_trans _ hg
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    simp [hg,hh]
  · simp only [if_neg hg]
    split_ifs
    · unfold setWeight
      positivity [p.property.1,p.property.2]
    · exact le_rfl

private theorem select_alice {V : Type} [Fintype V] [DecidableEq V]
    (X Y : Finset (V → Bool)) (k : ℝ) (hk : 1 ≤ k)
    (hX : SetDeficitLE X k) (hY : SetDeficitLE Y k)
    (p : Bias) (hp : 0 < (p : ℝ)) (hb : 32768*k*(p : ℝ) ≤ 1/2)
    (hl : LeftLimit p k X Y ∨ RightLimit p k X Y)
    (m b : ℕ) (hm : (m : ℝ) ≤ k) (hbmsg : b ≤ 2^m) (msg : (V → Bool) → Fin b) :
    ∃ q : Bias, 0 < (q : ℝ) ∧ (q : ℝ) ≤ 32768*k*(p : ℝ) ∧
      ∃ j : Fin b, ∃ X' : Finset (V → Bool), X' ⊆ X ∧
        SetDeficitLE X' (196*k) ∧ SetDeficitLE Y (196*k) ∧
        LeftLimit q (196*k) X' Y ∧ ∀ x ∈ X', msg x = j := by
  classical
  have hk0 : 0 ≤ k := by linarith
  have hprep : ∃ q : Bias, 0 < (q : ℝ) ∧ (q : ℝ) ≤ 32768*k*(p : ℝ) ∧
      ∃ X₀ : Finset (V → Bool), X₀ ⊆ X ∧ SetDeficitLE X₀ (194*k) ∧
        LeftLimit q (194*k) X₀ Y := by
    rcases hl with hl | hr
    · refine ⟨p,hp,?_,X,Finset.Subset.refl _,⟨hX.1,hX.2.trans (by linarith)⟩,?_⟩
      · nlinarith
      · intro x hx
        exact limit_mono_k p k (194*k) (by linarith) Y x (hl x hx)
    · obtain ⟨q,hq,hqeq,X₀,hsub,hD,hL⟩ := mirror_linear Y X k hk p hp hb hY hr
      exact ⟨q,hq,hqeq.le,X₀,hsub,⟨hD.1,hD.2.trans (by linarith)⟩,hL⟩
  obtain ⟨q,hq,hqb,X₀,hsub,hD,hL⟩ := hprep
  obtain ⟨j,hj⟩ := message_class X₀ (194*k) hD m b hbmsg msg
  refine ⟨q,hq,hqb,j,X₀.filter (fun x => msg x = j),
    (Finset.filter_subset _ _).trans hsub,⟨hj.1,hj.2.trans (by linarith)⟩,
    ⟨hY.1,hY.2.trans (by linarith)⟩,?_,?_⟩
  · intro x hx
    exact limit_mono_k q (194*k) (196*k) (by linarith) Y x (hL x (Finset.mem_filter.mp hx).1)
  · intro x hx
    exact (Finset.mem_filter.mp hx).2

private noncomputable def budget (t : ℕ) (k : ℝ) : ℝ :=
  (32768*(196 : ℝ)^t*k)^t

private theorem budget_one (t : ℕ) (k : ℝ) (hk : 1 ≤ k) : 1 ≤ budget t k := by
  apply one_le_pow₀
  have hh : 1 ≤ (196 : ℝ)^t := one_le_pow₀ (by norm_num)
  nlinarith

private theorem budget_step (t : ℕ) (k : ℝ) (hk : 1 ≤ k) :
    32768*k ≤ budget (t+1) k := by
  have hpow : 1 ≤ (196 : ℝ)^(t+1) := one_le_pow₀ (by norm_num)
  have hbase : 1 ≤ 32768*(196 : ℝ)^(t+1)*k := by nlinarith
  have ht : 1 ≤ (32768*(196 : ℝ)^(t+1)*k)^t := one_le_pow₀ hbase
  unfold budget
  rw [pow_succ]
  nlinarith

private theorem budget_child (t : ℕ) (k : ℝ) (hk : 1 ≤ k)
    (p q : Bias) (hq : (q : ℝ) ≤ 32768*k*(p : ℝ)) :
    budget t (196*k)*(q : ℝ) ≤ budget (t+1) k*(p : ℝ) := by
  let a := 32768*(196 : ℝ)^(t+1)*k
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hpow : 1 ≤ (196 : ℝ)^(t+1) := one_le_pow₀ (by norm_num)
  have hbase : 32768*k ≤ a := by dsimp [a]; nlinarith
  have hchild : budget t (196*k) = a^t := by
    unfold budget a
    congr 1
    rw [pow_succ]
    ring
  rw [hchild]
  calc
    a^t*(q : ℝ) ≤ a^t*(32768*k*(p : ℝ)) :=
      mul_le_mul_of_nonneg_left hq (pow_nonneg ha _)
    _ ≤ a^t*(a*(p : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbase p.property.1) (pow_nonneg ha _)
    _ = budget (t+1) k*(p : ℝ) := by
      unfold budget
      rw [pow_succ]
      dsimp [a]
      ring

private theorem leaf_impossible {V : Type} [Fintype V] [DecidableEq V]
    (X Y : Finset (V → Bool)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (p : Bias) (k : ℝ) (hp : (p : ℝ) ≤ 1/2)
    (hl : LeftLimit p k X Y ∨ RightLimit p k X Y)
    (o : Option V) (hsolve : SolvesKW (.leaf o) X Y) : False := by
  obtain ⟨x,hx⟩ := hX
  obtain ⟨y,hy⟩ := hY
  cases o with
  | none =>
    obtain ⟨i,hi,hneq⟩ := hsolve x hx y hy
    simp [Protocol.run] at hi
  | some i =>
    have hopp : ∀ x ∈ X, ∀ y ∈ Y, x i ≠ y i := by
      intro x hx y hy
      obtain ⟨j,hj,hneq⟩ := hsolve x hx y hy
      have he : i = j := Option.some.inj hj
      simpa only [← he] using hneq
    rcases hl with hl | hr
    · exact limit_coordinate_obstruction X Y ⟨x,hx⟩ p k hp hl i hopp
    · exact limit_coordinate_obstruction Y X ⟨y,hy⟩ p k hp hr i (fun y hy x hx => (hopp x hx y hy).symm)

private theorem adversary {V : Type} [Fintype V] [DecidableEq V]
    (t m : ℕ) (X Y : Finset (V → Bool)) (k : ℝ) (hk : 1 ≤ k)
    (hm : (m : ℝ) ≤ k) (hX : SetDeficitLE X k) (hY : SetDeficitLE Y k)
    (p : Bias) (hp : 0 < (p : ℝ)) (hb : budget t k*(p : ℝ) ≤ 1/2)
    (hl : LeftLimit p k X Y ∨ RightLimit p k X Y)
    (P : Protocol (V → Bool) (V → Bool) V) (hrounds : P.rounds ≤ t)
    (hcost : P.CostBounded m) (hsolve : SolvesKW P X Y) : False := by
  have hpbound : (p : ℝ) ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_right (budget_one t k hk) p.property.1
    nlinarith
  induction t generalizing X Y k p P with
  | zero =>
    cases P with
    | leaf o => exact leaf_impossible X Y hX.1 hY.1 p k hpbound hl o hsolve
    | alice b msg next => simp [Protocol.rounds] at hrounds
    | bob b msg next => simp [Protocol.rounds] at hrounds
  | succ t ih =>
    have hmirror : 32768*k*(p : ℝ) ≤ 1/2 :=
      (mul_le_mul_of_nonneg_right (budget_step t k hk) p.property.1).trans hb
    cases P with
    | leaf o => exact leaf_impossible X Y hX.1 hY.1 p k hpbound hl o hsolve
    | alice b msg next =>
      obtain ⟨q,hq,hqb,j,X',hsub,hX',hY',hlim,hmsg⟩ :=
        select_alice X Y k hk hX hY p hp hmirror hl m b hm hcost.1 msg
      have hchild : (next j).rounds ≤ t := by
        have hh := Finset.le_sup (f := fun j : Fin b => (next j).rounds) (Finset.mem_univ j)
        change 1 + Finset.univ.sup (fun j : Fin b => (next j).rounds) ≤ t+1 at hrounds
        omega
      have hsolve' : SolvesKW (next j) X' Y := by
        intro x hx y hy
        simpa only [Protocol.run, hmsg x hx] using hsolve x (hsub hx) y hy
      exact ih X' Y (196*k) (by linarith) (by linarith) hX' hY' q hq
        ((budget_child t k hk p q hqb).trans hb) (Or.inl hlim) (next j) hchild (hcost.2 j) hsolve'
        (by nlinarith [q.property.1])
    | bob b msg next =>
      have hlswap : LeftLimit p k Y X ∨ RightLimit p k Y X := by
        rcases hl with hl | hr
        · exact Or.inr hl
        · exact Or.inl hr
      obtain ⟨q,hq,hqb,j,Y',hsub,hY',hX',hlim,hmsg⟩ :=
        select_alice Y X k hk hY hX p hp hmirror hlswap m b hm hcost.1 msg
      have hchild : (next j).rounds ≤ t := by
        have hh := Finset.le_sup (f := fun j : Fin b => (next j).rounds) (Finset.mem_univ j)
        change 1 + Finset.univ.sup (fun j : Fin b => (next j).rounds) ≤ t+1 at hrounds
        omega
      have hsolve' : SolvesKW (next j) X Y' := by
        intro x hx y hy
        simpa only [Protocol.run, hmsg y hy] using hsolve x hx y (hsub hy)
      exact ih X Y' (196*k) (by linarith) (by linarith) hX' hY' q hq
        ((budget_child t k hk p q hqb).trans hb) (Or.inr hlim) (next j) hchild (hcost.2 j) hsolve'
        (by nlinarith [q.property.1])

theorem solution (V : Type) [Fintype V] [DecidableEq V]
    (t m : ℕ) (X Y : Finset (V → Bool)) (k : ℝ) (hk : 1 ≤ k)
    (hm : (m : ℝ) ≤ k) (hX : SetDeficitLE X k) (hY : SetDeficitLE Y k)
    (p : Bias) (hp : 0 < (p : ℝ))
    (hb : (32768*(196 : ℝ)^t*k)^t*(p : ℝ) ≤ 1/2)
    (hl : LeftLimit p k X Y ∨ RightLimit p k X Y) :
    ¬HasProtocol (X : Set (V → Bool)) (Y : Set (V → Bool)) t m := by
  rintro ⟨P,hrounds,hcost,hsolve⟩
  exact adversary t m X Y k hk hm hX hY p hp hb hl P hrounds hcost hsolve
