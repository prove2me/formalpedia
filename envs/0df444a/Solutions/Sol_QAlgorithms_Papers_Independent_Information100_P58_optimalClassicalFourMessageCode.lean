-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P58.optimalClassicalFourMessageCode
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:56:45.295603+00:00
-- url     : https://prove2.me/submissions/96b24158-4bfb-49bf-9a9c-5c1658531d5b

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

noncomputable section

namespace P58C

open QAlgorithms.Papers.Independent.Information100.P58

lemma univ_fs : (Finset.univ : Finset (Finset (Fin 4))) = {∅, {0}, {1}, {2}, {3}, {0,1}, {0,2},
    {0,3}, {1,2}, {1,3}, {2,3}, {0,1,2}, {0,1,3}, {0,2,3}, {1,2,3}, {0,1,2,3}} := by
  decide

lemma sum16 (f : Finset (Fin 4) → ℝ) : ∑ S, f S =
    f ∅ + (f {0} + (f {1} + (f {2} + (f {3} + (f {0,1} + (f {0,2} + (f {0,3} + (f {1,2} +
    (f {1,3} + (f {2,3} + (f {0,1,2} + (f {0,1,3} + (f {0,2,3} + (f {1,2,3} +
    f {0,1,2,3})))))))))))))) := by
  rw [univ_fs]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]

lemma cards : ({0,1} : Finset (Fin 4)).card = 2 ∧ ({0,2} : Finset (Fin 4)).card = 2 ∧
    ({0,3} : Finset (Fin 4)).card = 2 ∧ ({1,2} : Finset (Fin 4)).card = 2 ∧
    ({1,3} : Finset (Fin 4)).card = 2 ∧ ({2,3} : Finset (Fin 4)).card = 2 ∧
    ({0,1,2} : Finset (Fin 4)).card = 3 ∧ ({0,1,3} : Finset (Fin 4)).card = 3 ∧
    ({0,2,3} : Finset (Fin 4)).card = 3 ∧ ({1,2,3} : Finset (Fin 4)).card = 3 ∧
    ({0,1,2,3} : Finset (Fin 4)).card = 4 := by decide

/-- The target value, expanded. -/
def tgt (p : ℝ) : ℝ :=
  p^4/4 + 2*(1-p)*p^3 + (11/2)*(1-p)^2*p^2 + 4*(1-p)^3*p + (1-p)^4

lemma target_eq (p : ℝ) : dimensionSuccess 4 2 p 4 - (1/2)*p^2*(1-p)^2 = tgt p := by
  simp only [dimensionSuccess, binomialWeight, Finset.sum_range_succ, Finset.sum_range_zero, tgt]
  norm_num [Nat.choose]
  ring

set_option maxRecDepth 100000 in
lemma comp_card : ∀ (S : Finset (Fin 4)) (m : Fin 4), (compatible repeatedParity S m).card =
    (if S = ∅ then 4 else if S.card = 1 ∨ S = {0,3} then 2 else 1) := by decide

lemma part3 (p : ℝ) (m : Fin 4) :
    deterministicIndividual p repeatedParity m = tgt p := by
  unfold deterministicIndividual
  simp only [comp_card]
  rw [sum16]
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := cards
  simp (config := {decide := true}) only [patternWeight, if_true, if_false, c1, c2, c3, c4, c5,
    c6, c7, c8, c9, c10, c11, Finset.card_singleton, Finset.card_empty]
  norm_num [tgt]
  ring

/-! ### Upper bound -/

def D (xs : Fin 4 → Word 4 2) (S : Finset (Fin 4)) : ℕ :=
  (Finset.univ.image (fun m => received (xs m) S)).card

lemma dec_bound (dec : Output 4 2 → Distribution (Fin 4)) (xs : Fin 4 → Word 4 2)
    (S : Finset (Fin 4)) : ∑ m, (dec (received (xs m) S)).val m ≤ D xs S := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := Finset.univ.image (fun m => received (xs m) S)) (g := fun m => received (xs m) S)
    (fun m _ => Finset.mem_image_of_mem _ (Finset.mem_univ m))]
  rw [D, Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro y _
  calc ∑ m ∈ Finset.univ.filter (fun m => received (xs m) S = y),
        (dec (received (xs m) S)).val m
      = ∑ m ∈ Finset.univ.filter (fun m => received (xs m) S = y), (dec y).val m :=
        Finset.sum_congr rfl (fun m hm => by rw [(Finset.mem_filter.1 hm).2])
    _ ≤ ∑ m, (dec y).val m :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun m _ _ => (dec y).2.1 m)
    _ = ((1 : ℕ) : ℝ) := by rw [(dec y).2.2]; simp

lemma pw_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Fin 4)) :
    0 ≤ patternWeight 4 p S :=
  mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg hp0 _)

lemma ind_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (C : ClassicalCode 4 2 4) :
    ∃ xs : Fin 4 → Word 4 2,
      ∑ m, classicalIndividual p C m ≤ ∑ S, patternWeight 4 p S * D xs S := by
  let F : Fin 4 → Word 4 2 → ℝ := fun m x =>
    ∑ S, patternWeight 4 p S * (C.decoder (received x S)).val m
  have hF : ∀ m, classicalIndividual p C m = ∑ x, (C.encoder m).val x * F m x := by
    intro m
    simp only [classicalIndividual, F, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun S _ => by ring))
  choose xs hxs using fun m => Finset.exists_max_image Finset.univ (F m) Finset.univ_nonempty
  refine ⟨xs, ?_⟩
  have h1 : ∀ m, classicalIndividual p C m ≤ F m (xs m) := by
    intro m
    rw [hF]
    calc ∑ x, (C.encoder m).val x * F m x ≤ ∑ x, (C.encoder m).val x * F m (xs m) :=
          Finset.sum_le_sum (fun x _ =>
            mul_le_mul_of_nonneg_left ((hxs m).2 x (Finset.mem_univ _)) ((C.encoder m).2.1 x))
      _ = F m (xs m) := by rw [← Finset.sum_mul, (C.encoder m).2.2, one_mul]
  calc ∑ m, classicalIndividual p C m ≤ ∑ m, F m (xs m) := Finset.sum_le_sum (fun m _ => h1 m)
    _ = ∑ S, patternWeight 4 p S * ∑ m, (C.decoder (received (xs m) S)).val m := by
        simp only [F, Finset.mul_sum]; rw [Finset.sum_comm]
    _ ≤ ∑ S, patternWeight 4 p S * D xs S :=
        Finset.sum_le_sum (fun S _ =>
          mul_le_mul_of_nonneg_left (dec_bound _ _ _) (pw_nonneg p hp0 hp1 S))

lemma D_le4 (xs : Fin 4 → Word 4 2) (S : Finset (Fin 4)) : D xs S ≤ 4 :=
  Finset.card_image_le.trans (by simp)

lemma D_empty (xs : Fin 4 → Word 4 2) : D xs ∅ ≤ 1 := by
  apply Finset.card_le_one.2
  intro a ha b hb
  obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨m', -, rfl⟩ := Finset.mem_image.1 hb
  funext i; simp [received]

lemma D_single (xs : Fin 4 → Word 4 2) (i : Fin 4) : D xs {i} ≤ 2 := by
  have : (Finset.univ.image fun m => received (xs m) {i}) =
      (Finset.univ.image fun m => xs m i).image
        (fun b => fun j => if j = i then some b else none) := by
    rw [Finset.image_image]
    congr 1
    funext m j
    by_cases h : j = i
    · subst h; simp [received]
    · simp [received, h]
  rw [D, this]
  exact Finset.card_image_le.trans ((Finset.card_le_univ _).trans (by simp))

/-- Number of distinct value pairs of two columns. -/
def Pc (a b : Fin 4 → Fin 2) : ℕ := (Finset.univ.image (fun m => (a m, b m))).card

lemma D_pair (xs : Fin 4 → Word 4 2) (i j : Fin 4) (hij : i ≠ j) :
    D xs {i, j} ≤ Pc (fun m => xs m i) (fun m => xs m j) := by
  have : (Finset.univ.image fun m => received (xs m) {i, j}) =
      (Finset.univ.image fun m => (xs m i, xs m j)).image
        (fun ab => fun k => if k = i then some ab.1 else if k = j then some ab.2 else none) := by
    rw [Finset.image_image]
    congr 1
    funext m k
    by_cases h : k = i
    · subst h; simp [received]
    · by_cases h' : k = j
      · subst h'; simp [received, h]
      · simp [received, h, h']
  rw [D, this]
  exact Finset.card_image_le

def bal (a : Fin 4 → Fin 2) : Prop := (Finset.univ.filter (fun m => a m = 1)).card = 2

instance (a : Fin 4 → Fin 2) : Decidable (bal a) := by unfold bal; infer_instance

def key (a : Fin 4 → Fin 2) : Fin 4 → Fin 2 := if a 0 = 0 then a else fun m => a m + 1

def K : Finset (Fin 4 → Fin 2) := {![0,0,1,1], ![0,1,0,1], ![0,1,1,0]}

set_option maxRecDepth 100000 in
lemma Pc_le4 : ∀ a b : Fin 4 → Fin 2, Pc a b ≤ 4 := by decide

set_option maxRecDepth 100000 in
lemma Pc_unbalL : ∀ a b : Fin 4 → Fin 2, ¬ bal a → Pc a b ≤ 3 := by decide

set_option maxRecDepth 100000 in
lemma Pc_unbalR : ∀ a b : Fin 4 → Fin 2, ¬ bal b → Pc a b ≤ 3 := by decide

set_option maxRecDepth 100000 in
lemma Pc_key : ∀ a b : Fin 4 → Fin 2, bal a → bal b → key a = key b → Pc a b ≤ 2 := by decide

set_option maxRecDepth 100000 in
lemma key_mem : ∀ a : Fin 4 → Fin 2, bal a → key a ∈ K := by decide

lemma K_card : K.card = 3 := by decide

lemma pair22 (a : Fin 4 → Fin 4 → Fin 2) :
    Pc (a 0) (a 1) + Pc (a 0) (a 2) + Pc (a 0) (a 3) + Pc (a 1) (a 2) + Pc (a 1) (a 3) +
      Pc (a 2) (a 3) ≤ 22 := by
  have h01 := Pc_le4 (a 0) (a 1); have h02 := Pc_le4 (a 0) (a 2)
  have h03 := Pc_le4 (a 0) (a 3); have h12 := Pc_le4 (a 1) (a 2)
  have h13 := Pc_le4 (a 1) (a 3); have h23 := Pc_le4 (a 2) (a 3)
  by_cases hb : ∀ i, bal (a i)
  · obtain ⟨x, -, y, -, hxy, hk⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.univ) (t := K) (f := fun i => key (a i)) (by rw [K_card]; simp)
      (fun i _ => key_mem _ (hb i))
    have e1 := Pc_key _ _ (hb x) (hb y) hk
    have e2 := Pc_key _ _ (hb y) (hb x) hk.symm
    fin_cases x <;> fin_cases y <;> simp at hxy e1 e2 <;> omega
  · push Not at hb
    obtain ⟨i, hi⟩ := hb
    have hL : ∀ b, Pc (a i) b ≤ 3 := fun b => Pc_unbalL _ b hi
    have hR : ∀ b, Pc b (a i) ≤ 3 := fun b => Pc_unbalR b _ hi
    fin_cases i <;> simp at hL hR
    · have := hL (a 1); have := hL (a 2); have := hL (a 3); omega
    · have := hR (a 0); have := hL (a 2); have := hL (a 3); omega
    · have := hR (a 0); have := hR (a 1); have := hL (a 3); omega
    · have := hR (a 0); have := hR (a 1); have := hR (a 2); omega

lemma total_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (xs : Fin 4 → Word 4 2) :
    ∑ S, patternWeight 4 p S * D xs S ≤ 4 * tgt p := by
  have hq : 0 ≤ 1 - p := by linarith
  have w0 : 0 ≤ p ^ 4 := by positivity
  have w1 : 0 ≤ (1 - p) * p ^ 3 := by positivity
  have w2 : 0 ≤ (1 - p) ^ 2 * p ^ 2 := by positivity
  have w3 : 0 ≤ (1 - p) ^ 3 * p := by positivity
  have w4 : 0 ≤ (1 - p) ^ 4 := by positivity
  have d0 : (D xs ∅ : ℝ) ≤ 1 := by exact_mod_cast D_empty xs
  have d1 : ∀ i, (D xs {i} : ℝ) ≤ 2 := fun i => by exact_mod_cast D_single xs i
  have d4 : ∀ S, (D xs S : ℝ) ≤ 4 := fun S => by exact_mod_cast D_le4 xs S
  have hp : (D xs {0,1} + D xs {0,2} + D xs {0,3} + D xs {1,2} + D xs {1,3} + D xs {2,3} : ℝ)
      ≤ 22 := by
    have := pair22 (fun i m => xs m i)
    have a1 := D_pair xs 0 1 (by decide); have a2 := D_pair xs 0 2 (by decide)
    have a3 := D_pair xs 0 3 (by decide); have a4 := D_pair xs 1 2 (by decide)
    have a5 := D_pair xs 1 3 (by decide); have a6 := D_pair xs 2 3 (by decide)
    exact_mod_cast (by omega : D xs {0,1} + D xs {0,2} + D xs {0,3} + D xs {1,2} + D xs {1,3} +
      D xs {2,3} ≤ 22)
  rw [sum16]
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := cards
  simp only [patternWeight, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, Finset.card_singleton,
    Finset.card_empty]
  norm_num
  have := mul_le_mul_of_nonneg_left d0 w0
  have := mul_le_mul_of_nonneg_left hp w2
  have := mul_le_mul_of_nonneg_left (d1 0) w1
  have := mul_le_mul_of_nonneg_left (d1 1) w1
  have := mul_le_mul_of_nonneg_left (d1 2) w1
  have := mul_le_mul_of_nonneg_left (d1 3) w1
  have := mul_le_mul_of_nonneg_left (d4 {0,1,2}) w3
  have := mul_le_mul_of_nonneg_left (d4 {0,1,3}) w3
  have := mul_le_mul_of_nonneg_left (d4 {0,2,3}) w3
  have := mul_le_mul_of_nonneg_left (d4 {1,2,3}) w3
  have := mul_le_mul_of_nonneg_left (d4 {0,1,2,3}) w4
  unfold tgt
  nlinarith


/-! ### The attaining code -/

def Tset (y : Output 4 2) : Finset (Fin 4) :=
  Finset.univ.filter (fun j => received (repeatedParity j) (support y) = y)

def encStar (m : Fin 4) : Distribution (Word 4 2) :=
  ⟨fun x => if x = repeatedParity m then 1 else 0, fun x => by dsimp only; split_ifs <;> norm_num,
    by simp⟩

def decStar (y : Output 4 2) : Distribution (Fin 4) :=
  ⟨fun j => if Tset y = ∅ then 1 / 4 else if j ∈ Tset y then 1 / ((Tset y).card : ℝ) else 0,
    fun j => by dsimp only; split_ifs <;> positivity,
    by
      by_cases h : Tset y = ∅
      · simp [h]
      · simp only [h, if_false]
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        have : ((Tset y).card : ℝ) ≠ 0 := by
          exact_mod_cast (Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 h)).ne'
        field_simp⟩

def Cstar : ClassicalCode 4 2 4 := ⟨encStar, decStar⟩

lemma support_received (x : Word 4 2) (S : Finset (Fin 4)) : support (received x S) = S := by
  ext i; by_cases h : i ∈ S <;> simp [support, received, h]

lemma Tset_received (m : Fin 4) (S : Finset (Fin 4)) :
    Tset (received (repeatedParity m) S) = compatible repeatedParity S m := by
  ext j
  simp only [Tset, compatible, support_received, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h i hi
    have := congrFun h i
    simpa [received, hi] using this
  · intro h
    funext i
    by_cases hi : i ∈ S
    · simp [received, hi, h i hi]
    · simp [received, hi]

lemma Cstar_ind (p : ℝ) (m : Fin 4) : classicalIndividual p Cstar m = tgt p := by
  rw [← part3 p m]
  unfold classicalIndividual deterministicIndividual
  refine Finset.sum_congr rfl (fun S _ => ?_)
  simp only [Cstar, encStar, decStar, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Tset_received]
  have hm : m ∈ compatible repeatedParity S m := by simp [compatible]
  have hne : compatible repeatedParity S m ≠ ∅ := Finset.nonempty_iff_ne_empty.1 ⟨m, hm⟩
  simp only [hne, hm, if_false, if_true]
  ring

end P58C

open QAlgorithms.Papers.Independent.Information100.P58 in
theorem solution (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) :
    classicalOptimum 4 2 4 p false = dimensionSuccess 4 2 p 4 - (1/2)*p^2*(1-p)^2 ∧
    classicalOptimum 4 2 4 p true = dimensionSuccess 4 2 p 4 - (1/2)*p^2*(1-p)^2 ∧
    ∀ m, deterministicIndividual p repeatedParity m =
      dimensionSuccess 4 2 p 4 - (1/2)*p^2*(1-p)^2 := by
  rw [P58C.target_eq]
  have hsum : ∀ C : ClassicalCode 4 2 4, ∑ m, classicalIndividual p C m ≤ 4 * P58C.tgt p := by
    intro C
    obtain ⟨xs, hxs⟩ := P58C.ind_le p hp0 hp1 C
    exact hxs.trans (P58C.total_le p hp0 hp1 xs)
  have hstar : ∀ m, classicalIndividual p P58C.Cstar m = P58C.tgt p := P58C.Cstar_ind p
  refine ⟨?_, ?_, P58C.part3 p⟩
  · apply IsGreatest.csSup_eq
    refine ⟨⟨P58C.Cstar, ?_⟩, ?_⟩
    · simp only [Bool.false_eq_true, if_false, classicalAverage, hstar]
      simp
    · rintro v ⟨C, rfl⟩
      simp only [Bool.false_eq_true, if_false, classicalAverage]
      have := hsum C
      push_cast
      linarith
  · apply IsGreatest.csSup_eq
    refine ⟨⟨P58C.Cstar, ?_⟩, ?_⟩
    · simp only [if_true, hstar, ciInf_const]
    · rintro v ⟨C, rfl⟩
      simp only [if_true]
      have hi : ∀ m, (⨅ m, classicalIndividual p C m) ≤ classicalIndividual p C m :=
        fun m => ciInf_le (Set.finite_range _).bddBelow m
      have := hsum C
      simp only [Fin.sum_univ_four] at this
      linarith [hi 0, hi 1, hi 2, hi 3]
