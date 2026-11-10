-- Prove2me | solution 1 for PigeonholeDesignAudit.Lower.lemma_4_all_finite_partitions
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T12:00:20.860292+00:00
-- url     : https://prove2.me/submissions/57e9e699-5c45-49f5-a09d-165da8467cba

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting

set_option autoImplicit false


namespace PHDLower

/-- `false` (control) counts `+1`, `true` (treated) counts `-1`. -/
def sg (b : Bool) : ℝ := if b then -1 else 1

lemma sg_sq (b : Bool) : sg b ^ 2 = 1 := by cases b <;> simp [sg]

lemma sg_not (b : Bool) : sg (!b) = - sg b := by cases b <;> simp [sg]

/-- flip coordinate `a` of a coin vector. -/
def flip {T : ℕ} (a : Fin T) (ω : Fin T → Bool) : Fin T → Bool :=
  Function.update ω a (!ω a)

lemma flip_invol {T : ℕ} (a : Fin T) : Function.Involutive (flip a) := by
  intro ω
  funext t
  by_cases h : t = a
  · subst h; simp [flip]
  · simp [flip, Function.update_of_ne h]

lemma sum_mul_sg_eq_zero {T : ℕ} (a : Fin T) (g : (Fin T → Bool) → ℝ)
    (hg : ∀ ω, g (flip a ω) = g ω) :
    ∑ ω, g ω * sg (ω a) = 0 := by
  have h := Equiv.sum_comp (flip_invol a).toPerm (fun ω => g ω * sg (ω a))
  simp only [Function.Involutive.coe_toPerm] at h
  have h2 : ∀ ω, g (flip a ω) * sg (flip a ω a) = - (g ω * sg (ω a)) := by
    intro ω; rw [hg]; simp [flip, sg_not]
  simp_rw [h2, Finset.sum_neg_distrib] at h
  linarith

/-- The signed sum `X_S(ω) = ∑_{t∈S} c t * sg (ω t)`. -/
noncomputable def X {T : ℕ} (c : Fin T → ℝ) (S : Finset (Fin T)) (ω : Fin T → Bool) : ℝ :=
  ∑ t ∈ S, c t * sg (ω t)

lemma X_flip {T : ℕ} (c : Fin T → ℝ) (S : Finset (Fin T)) (a : Fin T) (ha : a ∉ S)
    (ω : Fin T → Bool) : X c S (flip a ω) = X c S ω := by
  unfold X
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have : t ≠ a := fun h => ha (h ▸ ht)
  simp [flip, Function.update_of_ne this]

lemma card_coins (T : ℕ) : (∑ _ω : Fin T → Bool, (1 : ℝ)) = 2 ^ T := by
  simp

lemma moments {T : ℕ} (c : Fin T → ℝ) (S : Finset (Fin T)) :
    (∑ ω, X c S ω ^ 2 = 2 ^ T * ∑ t ∈ S, c t ^ 2) ∧
    (2 ^ T * ∑ ω, X c S ω ^ 4 ≤ 3 * (∑ ω, X c S ω ^ 2) ^ 2) := by
  induction S using Finset.induction_on with
  | empty => simp [X]
  | @insert a S ha ih =>
    obtain ⟨h2, h4⟩ := ih
    have hX : ∀ ω, X c (insert a S) ω = X c S ω + c a * sg (ω a) := by
      intro ω; unfold X; rw [Finset.sum_insert ha]; ring
    have z1 : ∑ ω, (X c S ω * c a) * sg (ω a) = 0 :=
      sum_mul_sg_eq_zero a _ (fun ω => by rw [X_flip c S a ha])
    have z3 : ∑ ω, (X c S ω ^ 3 * c a) * sg (ω a) = 0 :=
      sum_mul_sg_eq_zero a _ (fun ω => by rw [X_flip c S a ha])
    have z1' : ∑ ω, (X c S ω * c a ^ 3) * sg (ω a) = 0 :=
      sum_mul_sg_eq_zero a _ (fun ω => by rw [X_flip c S a ha])
    have e2 : ∀ ω, X c (insert a S) ω ^ 2
        = X c S ω ^ 2 + 2 * ((X c S ω * c a) * sg (ω a)) + c a ^ 2 := by
      intro ω; rw [hX]; have := sg_sq (ω a)
      linear_combination (c a ^ 2) * this
    have e4 : ∀ ω, X c (insert a S) ω ^ 4
        = X c S ω ^ 4 + 4 * ((X c S ω ^ 3 * c a) * sg (ω a))
          + 6 * c a ^ 2 * X c S ω ^ 2 + 4 * ((X c S ω * c a ^ 3) * sg (ω a)) + c a ^ 4 := by
      intro ω; rw [hX]; have hs := sg_sq (ω a)
      linear_combination
        (6 * X c S ω ^ 2 * c a ^ 2 + 4 * X c S ω * c a ^ 3 * sg (ω a)
          + c a ^ 4 * (sg (ω a) ^ 2 + 1)) * hs
    have s2 : ∑ ω, X c (insert a S) ω ^ 2 = ∑ ω, X c S ω ^ 2 + 2 ^ T * c a ^ 2 := by
      simp_rw [e2, Finset.sum_add_distrib, ← Finset.mul_sum, z1]
      simp
    have s4 : ∑ ω, X c (insert a S) ω ^ 4
        = ∑ ω, X c S ω ^ 4 + 6 * c a ^ 2 * ∑ ω, X c S ω ^ 2 + 2 ^ T * c a ^ 4 := by
      simp_rw [e4, Finset.sum_add_distrib, ← Finset.mul_sum, z3, z1']
      simp
    refine ⟨?_, ?_⟩
    · rw [s2, h2, Finset.sum_insert ha]; ring
    · rw [s4, s2]
      have hN : (0 : ℝ) ≤ 2 ^ T := by positivity
      have hM : 0 ≤ ∑ ω, X c S ω ^ 2 := Finset.sum_nonneg (fun ω _ => sq_nonneg _)
      have hc : 0 ≤ c a ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg (mul_nonneg hN hN) (pow_nonneg hc 2), mul_nonneg hN (mul_nonneg hc hM)]

/-- Khintchine lower bound with explicit constant: `∑_ω |X| ≥ 2^T * √(3V)/3`, `V = ∑ c²`. -/
theorem khintchine {T : ℕ} (c : Fin T → ℝ) (S : Finset (Fin T)) :
    2 ^ T * (Real.sqrt (3 * ∑ t ∈ S, c t ^ 2) / 3) ≤ ∑ ω, |X c S ω| := by
  obtain ⟨h2, h4⟩ := moments c S
  set V := ∑ t ∈ S, c t ^ 2 with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun t _ => sq_nonneg _)
  have hN : (0 : ℝ) < 2 ^ T := by positivity
  rcases hV0.lt_or_eq with hVpos | hVz
  · set m := Real.sqrt (3 * V) with hm
    have hm0 : 0 < m := Real.sqrt_pos.mpr (by linarith)
    have hm2 : m ^ 2 = 3 * V := Real.sq_sqrt (by linarith)
    -- pointwise: 2 m^3 |x| ≥ 3 m^2 x^2 - x^4
    have pw : ∀ ω, 3 * m ^ 2 * X c S ω ^ 2 - X c S ω ^ 4 ≤ 2 * m ^ 3 * |X c S ω| := by
      intro ω
      set y := |X c S ω|
      have hy : 0 ≤ y := abs_nonneg _
      have hy2 : X c S ω ^ 2 = y ^ 2 := (sq_abs _).symm
      have hy4 : X c S ω ^ 4 = y ^ 4 := by
        rw [show X c S ω ^ 4 = (X c S ω ^ 2) ^ 2 by ring, hy2]; ring
      have key : 0 ≤ y * (y - m) ^ 2 * (y + 2 * m) :=
        mul_nonneg (mul_nonneg hy (sq_nonneg _)) (by linarith)
      have id : y * (y - m) ^ 2 * (y + 2 * m) = y ^ 4 - 3 * m ^ 2 * y ^ 2 + 2 * m ^ 3 * y := by ring
      rw [hy2, hy4]; linarith
    have sum_pw : 3 * m ^ 2 * (∑ ω, X c S ω ^ 2) - ∑ ω, X c S ω ^ 4
        ≤ 2 * m ^ 3 * ∑ ω, |X c S ω| := by
      have := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => pw ω)
      simpa [Finset.sum_sub_distrib, Finset.mul_sum] using this
    rw [h2] at sum_pw h4
    -- 2^T * M4 ≤ 3 (2^T V)^2  ⇒  M4 ≤ 3 * 2^T * V^2
    have h4' : ∑ ω, X c S ω ^ 4 ≤ 3 * 2 ^ T * V ^ 2 := by
      have : 2 ^ T * ∑ ω, X c S ω ^ 4 ≤ 2 ^ T * (3 * 2 ^ T * V ^ 2) := by nlinarith
      exact le_of_mul_le_mul_left this hN
    -- 2 m^3 Σ|X| ≥ 3 m^2 2^T V - 3 2^T V^2 = 2^T V (3 m^2 - 3V) = 2^T V * 2 m^2 ... = 2 m^3 * (2^T m/3)
    have goal : 2 * m ^ 3 * (2 ^ T * (m / 3)) ≤ 2 * m ^ 3 * ∑ ω, |X c S ω| := by
      have e : 2 * m ^ 3 * (2 ^ T * (m / 3)) = 3 * m ^ 2 * (2 ^ T * V) - 3 * 2 ^ T * V ^ 2 := by
        have : V = m ^ 2 / 3 := by linarith
        rw [this]; ring
      linarith
    have hm3 : 0 < 2 * m ^ 3 := by positivity
    exact le_of_mul_le_mul_left goal hm3
  · rw [← hVz]; simp
    exact Finset.sum_nonneg (fun ω _ => abs_nonneg _)

end PHDLower



namespace PHDLower

open PigeonholeDesign.Upper

lemma pa_succ_cases {ι : Type*} [DecidableEq ι] (T : ℕ) (cell : ℕ → ι) (coin : ℕ → Bool) (n : ℕ) :
    ∃ b, prefixAssign T cell coin (n + 1) = prefixAssign T cell coin n ++ [b] ∧
      ((prefixAssign T cell coin n).count false = T / 2 → b = true) ∧
      ((prefixAssign T cell coin n).count false ≠ T / 2 →
        (prefixAssign T cell coin n).count true = T / 2 → b = false) := by
  refine ⟨_, rfl, ?_, ?_⟩
  · intro h; simp [h]
  · intro h1 h2; simp [h1, h2]

lemma pa_length {ι : Type*} [DecidableEq ι] (T : ℕ) (cell : ℕ → ι) (coin : ℕ → Bool) (n : ℕ) :
    (prefixAssign T cell coin n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨b, hb, -, -⟩ := pa_succ_cases T cell coin n
    rw [hb, List.length_append, ih]; rfl

lemma count_ff_add_tt (L : List Bool) : L.count false + L.count true = L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => cases a <;> simp <;> omega

lemma pa_counts_le {ι : Type*} [DecidableEq ι] (T : ℕ) (hT : Even T) (cell : ℕ → ι)
    (coin : ℕ → Bool) (n : ℕ) (hn : n ≤ T) :
    (prefixAssign T cell coin n).count false ≤ T / 2 ∧
      (prefixAssign T cell coin n).count true ≤ T / 2 := by
  induction n with
  | zero => simp [prefixAssign]
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih (by omega)
    obtain ⟨b, hb, hb1, hb2⟩ := pa_succ_cases T cell coin n
    have hs := count_ff_add_tt (prefixAssign T cell coin n)
    rw [pa_length] at hs
    obtain ⟨r, hr⟩ := hT
    rw [hb]
    by_cases c0 : (prefixAssign T cell coin n).count false = T / 2
    · have := hb1 c0; subst this
      simp only [List.count_append, List.count_singleton]
      simp
      omega
    · by_cases c1 : (prefixAssign T cell coin n).count true = T / 2
      · have := hb2 c0 c1; subst this
        simp only [List.count_append]
        simp
        omega
      · simp only [List.count_append]
        cases b <;> simp <;> omega

lemma card_getD_eq_count (b : Bool) :
    ∀ (L : List Bool),
      (Finset.univ.filter (fun t : Fin L.length => L.getD t false = b)).card = L.count b := by
  intro L
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [Finset.card_filter] at ih ⊢
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ]
    rw [ih, List.count_cons]
    cases a <;> cases b <;> simp <;> omega

lemma card_getD_eq_count' (b : Bool) (L : List Bool) (N : ℕ) (hN : L.length = N) :
    (Finset.univ.filter (fun t : Fin N => L.getD t false = b)).card = L.count b := by
  subst hN; exact card_getD_eq_count b L

theorem assign_balanced {E : Type*} {K : Type*} [DecidableEq K] (T : ℕ) (hT : Even T)
    (hole : E → K) (x : Fin T → E) (coin : Fin T → Bool) :
    Nonempty ({t // assign hole x coin t = false} ≃ {t // assign hole x coin t = true}) := by
  obtain ⟨h0, h1⟩ := pa_counts_le T hT (cellOf hole x) (coinOf coin) T le_rfl
  set L := prefixAssign T (cellOf hole x) (coinOf coin) T with hL
  have hlen : L.length = T := pa_length _ _ _ _
  have hs := count_ff_add_tt L
  rw [hlen] at hs
  obtain ⟨r, hr⟩ := hT
  have e0 : L.count false = L.count true := by omega
  have key : ∀ b, Fintype.card {t : Fin T // assign hole x coin t = b} = L.count b := by
    intro b
    rw [Fintype.card_subtype]
    exact card_getD_eq_count' b L T hlen
  exact ⟨Fintype.equivOfCardEq (by rw [key, key, e0])⟩

end PHDLower



namespace PHDLower

def sg' (b : Bool) : ℝ := if b then -1 else 1

/-- indicator of `i ≤ j` as a real number -/
def ind (i j : ℕ) : ℝ := if i ≤ j then 1 else 0

lemma abs_sub_eq_sum_ind (n i i' : ℕ) (hi : i ≤ n) (hi' : i' ≤ n) :
    |(i : ℝ) - i'| = ∑ j ∈ Finset.range n, |ind i j - ind i' j| := by
  have hterm : ∀ j, |ind i j - ind i' j| = if (i ≤ j ∧ ¬ i' ≤ j) ∨ (i' ≤ j ∧ ¬ i ≤ j) then 1 else 0 := by
    intro j
    unfold ind
    by_cases h1 : i ≤ j <;> by_cases h2 : i' ≤ j <;> simp [h1, h2]
  simp_rw [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rcases le_total i i' with h | h
  · have : (Finset.range n).filter (fun j => (i ≤ j ∧ ¬ i' ≤ j) ∨ (i' ≤ j ∧ ¬ i ≤ j))
        = Finset.Ico i i' := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [this, Nat.card_Ico, Nat.cast_sub h, abs_sub_comm, abs_of_nonneg (by
      exact sub_nonneg.mpr (by exact_mod_cast h))]
  · have : (Finset.range n).filter (fun j => (i ≤ j ∧ ¬ i' ≤ j) ∨ (i' ≤ j ∧ ¬ i ≤ j))
        = Finset.Ico i' i := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [this, Nat.card_Ico, Nat.cast_sub h, abs_of_nonneg (by
      exact sub_nonneg.mpr (by exact_mod_cast h))]

/-- signed threshold count `D_j = Σ_t [k t ≤ j] sg (w t)` -/
noncomputable def Dj {T : ℕ} (k : Fin T → ℕ) (w : Fin T → Bool) (j : ℕ) : ℝ :=
  ∑ t, ind (k t) j * sg' (w t)

lemma Dj_split {T : ℕ} (k : Fin T → ℕ) (w : Fin T → Bool) (j : ℕ) :
    Dj k w j = (∑ a : {t // w t = false}, ind (k a) j) - ∑ b : {t // w t = true}, ind (k b) j := by
  unfold Dj
  have h1 : ∑ a : {t // w t = false}, ind (k a) j
      = ∑ t ∈ Finset.univ.filter (fun t => w t = false), ind (k t) j :=
    (Finset.sum_subtype _ (by simp) (fun t => ind (k t) j)).symm
  have h2 : ∑ b : {t // w t = true}, ind (k b) j
      = ∑ t ∈ Finset.univ.filter (fun t => w t = true), ind (k t) j :=
    (Finset.sum_subtype _ (by simp) (fun t => ind (k t) j)).symm
  rw [h1, h2, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  cases w t <;> simp [sg']

theorem disc_lower {T n : ℕ} (hn : 0 < n) (k : Fin T → ℕ) (hk : ∀ t, k t ≤ n)
    (w : Fin T → Bool) (hbal : Nonempty ({t // w t = false} ≃ {t // w t = true})) :
    (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, |Dj k w j|
      ≤ PigeonholeDesign.Upper.discrepancy (fun t => (k t : ℝ) / n) w := by
  unfold PigeonholeDesign.Upper.discrepancy
  apply le_ciInf
  intro e
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : ∀ a : {t // w t = false},
      dist ((k a : ℝ) / n) ((k (e a) : ℝ) / n)
        = (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, |ind (k a) j - ind (k (e a)) j| := by
    intro a
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hn',
      abs_sub_eq_sum_ind n _ _ (hk _) (hk _)]
    ring
  simp_rw [hd]
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have hD : Dj k w j = ∑ a : {t // w t = false}, (ind (k a) j - ind (k (e a)) j) := by
    rw [Dj_split, Finset.sum_sub_distrib]
    congr 1
    exact (Equiv.sum_comp e (fun b => ind (k b) j)).symm
  rw [hD]
  exact Finset.abs_sum_le_sum_abs _ _

end PHDLower



namespace PHDLower

open PigeonholeDesign.Upper

-- new (M2)
lemma pa_prefix {ι : Type*} [DecidableEq ι] (T : ℕ) (cell : ℕ → ι) (coin : ℕ → Bool) (m : ℕ) :
    ∀ k, ∃ l, prefixAssign T cell coin (m + k) = prefixAssign T cell coin m ++ l := by
  intro k
  induction k with
  | zero => exact ⟨[], by simp⟩
  | succ k ih =>
    obtain ⟨l, hl⟩ := ih
    obtain ⟨b, hb, -, -⟩ := pa_succ_cases T cell coin (m + k)
    exact ⟨l ++ [b], by rw [← Nat.add_assoc, hb, hl, List.append_assoc]⟩

lemma pa_getD {ι : Type*} [DecidableEq ι] (T : ℕ) (cell : ℕ → ι) (coin : ℕ → Bool) (t m : ℕ)
    (htm : t < m) :
    (prefixAssign T cell coin m).getD t false =
      (prefixAssign T cell coin (t + 1)).getD t false := by
  obtain ⟨l, hl⟩ := pa_prefix T cell coin (t + 1) (m - (t + 1))
  rw [show t + 1 + (m - (t + 1)) = m by omega] at hl
  rw [hl, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [pa_length]; omega)]

def a0f {ι : Type*} [DecidableEq ι] (T : ℕ) (cell : ℕ → ι) (coin : ℕ → Bool) (n : ℕ)
    (b : Bool) : ℕ :=
  ((List.range n).zip (prefixAssign T cell coin n)).countP
    (fun sb => cell sb.1 = cell n ∧ sb.2 = b)

lemma pa_succ_eq {ι : Type*} [DecidableEq ι] (T : ℕ) (cell : ℕ → ι) (coin : ℕ → Bool) (n : ℕ) :
    prefixAssign T cell coin (n + 1) = prefixAssign T cell coin n ++
      [if (prefixAssign T cell coin n).count false = T / 2 then true
       else if (prefixAssign T cell coin n).count true = T / 2 then false
       else if a0f T cell coin n false < a0f T cell coin n true then false
       else if a0f T cell coin n true < a0f T cell coin n false then true
       else coin n] := rfl

lemma pa_step_free {ι : Type*} [DecidableEq ι] (T : ℕ) (cell : ℕ → ι) (coin : ℕ → Bool) (n : ℕ)
    (hn : 2 * n + 2 ≤ T) :
    prefixAssign T cell coin (n + 1) = prefixAssign T cell coin n ++
      [if a0f T cell coin n false < a0f T cell coin n true then false
       else if a0f T cell coin n true < a0f T cell coin n false then true
       else coin n] := by
  have h0 : (prefixAssign T cell coin n).count false ≠ T / 2 := by
    have := List.count_le_length (a := false) (l := prefixAssign T cell coin n)
    rw [pa_length] at this; omega
  have h1 : (prefixAssign T cell coin n).count true ≠ T / 2 := by
    have := List.count_le_length (a := true) (l := prefixAssign T cell coin n)
    rw [pa_length] at this; omega
  rw [pa_succ_eq, if_neg h0, if_neg h1]

lemma getD_snoc (L : List Bool) (b : Bool) (n : ℕ) (h : L.length = n) :
    (L ++ [b]).getD n false = b := by
  subst h; simp [List.getD_eq_getElem?_getD]

lemma cnt_fresh {ι : Type*} [DecidableEq ι] (T : ℕ) (cell : ℕ → ι) (coin : ℕ → Bool) (n : ℕ)
    (b : Bool) (hf : ∀ s < n, cell s ≠ cell n) : a0f T cell coin n b = 0 := by
  unfold a0f
  rw [List.countP_eq_zero]
  rintro ⟨s, c⟩ hmem
  have := List.of_mem_zip hmem
  simp only [List.mem_range] at this
  simp [hf s this.1]

lemma assign_eq_last {E ι : Type*} [DecidableEq ι] {T : ℕ} (hole : E → ι) (x : Fin T → E)
    (coin : Fin T → Bool) (t : Fin T) :
    assign hole x coin t =
      (prefixAssign T (cellOf hole x) (coinOf coin) (t.val + 1)).getD t.val false := by
  unfold assign; exact pa_getD _ _ _ _ _ t.isLt

/-- Singles: an arrival in the first half whose cell is fresh gets its own fair coin. -/
theorem assign_fresh {E ι : Type*} [DecidableEq ι] {T : ℕ} (hole : E → ι) (x : Fin T → E)
    (coin : Fin T → Bool) (t : Fin T) (ht : 2 * t.val + 2 ≤ T)
    (hf : ∀ s < t.val, cellOf hole x s ≠ cellOf hole x t.val) :
    assign hole x coin t = coin t := by
  rw [assign_eq_last, pa_step_free _ _ _ _ ht, getD_snoc _ _ _ (pa_length _ _ _ _),
    cnt_fresh _ _ _ _ false hf, cnt_fresh _ _ _ _ true hf]
  simp [coinOf, t.isLt]

def fpair (cn : ℕ → Bool) (n : ℕ) : Bool := if n % 2 = 1 then !(cn (n - 1)) else cn n

lemma countP_zip_map' {ι : Type*} [DecidableEq ι] (cell : ℕ → ι) (f : ℕ → Bool) (c : ι)
    (b : Bool) (l : List ℕ) :
    (l.zip (l.map f)).countP (fun sb => cell sb.1 = c ∧ sb.2 = b) =
      l.countP (fun s => cell s = c ∧ f s = b) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.zip_cons_cons, List.countP_cons, List.countP_cons, ih]

lemma bal_pairs {ι : Type*} [DecidableEq ι] (cell : ℕ → ι) (cn : ℕ → Bool) (P : ℕ)
    (hpair : ∀ p < P, cell (2 * p) = cell (2 * p + 1)) (c : ι) (b : Bool) :
    ∀ q ≤ P, (List.range (2 * q)).countP (fun s => cell s = c ∧ fpair cn s = b) =
      (List.range q).countP (fun p => cell (2 * p) = c) := by
  intro q
  induction q with
  | zero => intro _; simp
  | succ q ih =>
    intro hq
    rw [show 2 * (q + 1) = 2 * q + 1 + 1 by ring, List.range_succ, List.range_succ,
      List.range_succ, List.countP_append, List.countP_append, List.countP_append, ih (by omega)]
    have e0 : (2 * q) % 2 = 0 := by omega
    have e1 : (2 * q + 1) % 2 = 1 := by omega
    have h1 : fpair cn (2 * q) = cn (2 * q) := by simp [fpair, e0]
    have h2 : fpair cn (2 * q + 1) = !cn (2 * q) := by simp [fpair, e1]
    have hc := hpair q (by omega)
    simp only [List.countP_singleton, h1, h2, ← hc]
    by_cases hcc : cell (2 * q) = c <;> cases cn (2 * q) <;> cases b <;> simp [hcc]

lemma pa_pairs {ι : Type*} [DecidableEq ι] (T : ℕ) (cell : ℕ → ι) (cn : ℕ → Bool) (P : ℕ)
    (hP : 4 * P ≤ T) (hpair : ∀ p < P, cell (2 * p) = cell (2 * p + 1)) :
    ∀ m ≤ 2 * P, prefixAssign T cell cn m = (List.range m).map (fpair cn) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    have ihm := ih (by omega)
    rw [pa_step_free T cell cn m (by omega)]
    unfold a0f
    rw [ihm, countP_zip_map', countP_zip_map', List.range_succ, List.map_append,
      List.map_singleton]
    congr 2
    rcases Nat.even_or_odd' m with ⟨q, rfl | rfl⟩
    · rw [bal_pairs cell cn P hpair _ _ q (by omega), bal_pairs cell cn P hpair _ _ q (by omega)]
      have e : (2 * q) % 2 = 0 := by omega
      simp [fpair, e]
    · rw [List.range_succ, List.countP_append, List.countP_append,
        bal_pairs cell cn P hpair _ _ q (by omega), bal_pairs cell cn P hpair _ _ q (by omega)]
      have hc := hpair q (by omega)
      have e1 : (2 * q + 1) % 2 = 1 := by omega
      have e0 : (2 * q) % 2 = 0 := by omega
      simp only [List.countP_singleton, fpair, e0, e1, hc, Nat.add_sub_cancel]
      cases h : cn (2 * q) <;> simp [h]

/-- Pairs: arrivals 2p, 2p+1 (p < P) share a cell; the first gets its coin, the second the
opposite. -/
theorem assign_pairs {E ι : Type*} [DecidableEq ι] {T : ℕ} (hole : E → ι) (x : Fin T → E)
    (coin : Fin T → Bool) (P : ℕ) (hP : 4 * P ≤ T)
    (hpair : ∀ p < P, cellOf hole x (2 * p) = cellOf hole x (2 * p + 1)) (t : Fin T)
    (ht : t.val < 2 * P) :
    assign hole x coin t = fpair (coinOf coin) t.val := by
  unfold assign
  rw [pa_getD _ _ _ t.val T t.isLt, ← pa_getD _ _ _ t.val (2 * P) ht,
    pa_pairs T _ _ P hP hpair (2 * P) le_rfl]
  simp [List.getD_eq_getElem?_getD, ht]

end PHDLower



namespace PHDLower

open PigeonholeDesign.Upper Finset

-- ===== M5 assembly =====

open Classical

theorem frame {T n K : ℕ} (hT : Even T) (hn : 0 < n) (hole : ℝ → Fin K) (kN : ℕ → ℕ)
    (hk : ∀ u, kN u ≤ n) (V : ℕ → ℝ)
    (hD : ∀ j, j < n → ∃ c : Fin T → ℝ,
      (∀ coin : Fin T → Bool, Dj (fun t : Fin T => kN t.val)
          (assign hole (fun t : Fin T => ((kN t.val : ℕ) : ℝ) / n) coin) j = X c univ coin) ∧
        V j ≤ ∑ t, c t ^ 2) :
    (1 / (n : ℝ)) * ∑ j ∈ range n, Real.sqrt (3 * V j) / 3 ≤
      phdExp hole (fun t : Fin T => ((kN t.val : ℕ) : ℝ) / n) := by
  choose! c hc using hD
  unfold phdExp
  rw [le_div_iff₀ (by positivity)]
  have h1 : ∀ coin : Fin T → Bool, (1 / (n : ℝ)) * ∑ j ∈ range n, |X (c j) univ coin| ≤
      discrepancy (fun t : Fin T => ((kN t.val : ℕ) : ℝ) / n)
        (assign hole (fun t : Fin T => ((kN t.val : ℕ) : ℝ) / n) coin) := by
    intro coin
    have := disc_lower hn (fun t : Fin T => kN t.val) (fun t => hk _)
      (assign hole (fun t : Fin T => ((kN t.val : ℕ) : ℝ) / n) coin)
      (assign_balanced T hT hole _ coin)
    refine le_trans (le_of_eq ?_) this
    congr 1
    apply sum_congr rfl
    intro j hj
    rw [(hc j (mem_range.mp hj)).1 coin]
  have h2 : ∀ j ∈ range n, 2 ^ T * (Real.sqrt (3 * V j) / 3) ≤
      ∑ coin : Fin T → Bool, |X (c j) univ coin| := by
    intro j hj
    refine le_trans ?_ (khintchine (c j) univ)
    gcongr
    exact (hc j (mem_range.mp hj)).2
  calc ((1 / (n : ℝ)) * ∑ j ∈ range n, Real.sqrt (3 * V j) / 3) * 2 ^ T
      = (1 / (n : ℝ)) * ∑ j ∈ range n, 2 ^ T * (Real.sqrt (3 * V j) / 3) := by
        rw [← mul_sum]; ring
    _ ≤ (1 / (n : ℝ)) * ∑ j ∈ range n, ∑ coin : Fin T → Bool, |X (c j) univ coin| := by
        gcongr with j hj
        exact h2 j hj
    _ = ∑ coin : Fin T → Bool, (1 / (n : ℝ)) * ∑ j ∈ range n, |X (c j) univ coin| := by
        rw [sum_comm, mul_sum]
    _ ≤ _ := sum_le_sum (fun coin _ => h1 coin)

lemma sum_fin_coin {T : ℕ} (f : ℕ → ℝ) (coin : Fin T → Bool) :
    ∑ t : Fin T, f t.val * sg (coin t) = ∑ u ∈ range T, f u * sg (coinOf coin u) := by
  rw [← Fin.sum_univ_eq_sum_range (fun u => f u * sg (coinOf coin u)) T]
  apply sum_congr rfl
  intro t _
  simp [coinOf, t.isLt]

lemma pair_sum (g : ℕ → ℝ) (cn : ℕ → Bool) (P : ℕ) :
    ∑ u ∈ range (2 * P), g u * sg (fpair cn u) =
      ∑ u ∈ range (2 * P), (if u % 2 = 0 then g u - g (u + 1) else 0) * sg (cn u) := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [show 2 * (P + 1) = 2 * P + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_succ (fun u => (if u % 2 = 0 then g u - g (u + 1) else 0) * sg (cn u)),
      sum_range_succ (fun u => (if u % 2 = 0 then g u - g (u + 1) else 0) * sg (cn u)), ih]
    have e0 : (2 * P) % 2 = 0 := by omega
    have e1 : (2 * P + 1) % 2 = 1 := by omega
    simp [fpair, e0, e1, sg_not] <;> ring

lemma sum_range_cut {T M : ℕ} (hM : M ≤ T) (f : ℕ → ℝ) (hf : ∀ u, M ≤ u → f u = 0) :
    ∑ u ∈ range T, f u = ∑ u ∈ range M, f u := by
  rw [← sum_range_add_sum_Ico f hM, sum_eq_zero (fun u hu => hf u (mem_Ico.mp hu).1), add_zero]

/-- `j` is a cut of the grid `{0, 1/n, …, 1}`: no cell meets both `[0, j/n]` and `((j)/n, 1]`. -/
def cutP {K : ℕ} (hole : ℝ → Fin K) (n j : ℕ) : Prop :=
  ∀ a ≤ j, ∀ b, j < b → b ≤ n → hole ((a : ℝ) / n) ≠ hole ((b : ℝ) / n)

/-- Case I arrivals: subject `u < n` at grid point `u` if `u` is a cut, everyone else at `1`. -/
noncomputable def kI {K : ℕ} (hole : ℝ → Fin K) (n u : ℕ) : ℕ :=
  if u < n ∧ cutP hole n u then u else n

lemma kI_le {K : ℕ} (hole : ℝ → Fin K) (n u : ℕ) : kI hole n u ≤ n := by
  unfold kI; split_ifs with h
  · exact h.1.le
  · exact le_rfl

theorem caseI {T n K : ℕ} (h2n : 2 * n + 2 ≤ T) (hole : ℝ → Fin K) (j : ℕ) (hj : j < n) :
    ∃ c : Fin T → ℝ,
      (∀ coin : Fin T → Bool, Dj (fun t : Fin T => kI hole n t.val)
          (assign hole (fun t : Fin T => ((kI hole n t.val : ℕ) : ℝ) / n) coin) j =
            X c univ coin) ∧
        (((range (j + 1)).filter (fun u => cutP hole n u)).card : ℝ) ≤ ∑ t, c t ^ 2 := by
  refine ⟨fun t => ind (kI hole n t.val) j, ?_, ?_⟩
  · intro coin
    unfold Dj X
    apply sum_congr rfl
    intro t _
    by_cases ht : kI hole n t.val ≤ j
    · have hcut : t.val < n ∧ cutP hole n t.val := by
        unfold kI at ht
        split_ifs at ht with h
        · exact h
        · omega
      have hkt : kI hole n t.val = t.val := by unfold kI; rw [if_pos hcut]
      rw [assign_fresh hole _ coin t (by omega) ?_]
      · rfl
      · intro s hs
        have hsT : s < T := lt_trans hs t.isLt
        have key : hole ((kI hole n s : ℝ) / n) ≠ hole ((kI hole n t.val : ℝ) / n) := by
          rw [hkt]
          unfold kI
          split_ifs with hs'
          · exact hs'.2 s le_rfl t.val hs hcut.1.le
          · exact fun h => hcut.2 t.val le_rfl n hcut.1 le_rfl h.symm
        simpa [cellOf, hsT, t.isLt] using key
    · simp [ind, ht]
  · refine le_trans ?_ (le_of_eq (Fin.sum_univ_eq_sum_range (fun u => ind (kI hole n u) j ^ 2) T).symm)
    calc (((range (j + 1)).filter (fun u => cutP hole n u)).card : ℝ)
        = ∑ u ∈ (range (j + 1)).filter (fun u => cutP hole n u), (1 : ℝ) := by simp
      _ = ∑ u ∈ (range (j + 1)).filter (fun u => cutP hole n u), ind (kI hole n u) j ^ 2 := by
          apply sum_congr rfl
          intro u hu
          rw [mem_filter, mem_range] at hu
          have : kI hole n u = u := by unfold kI; rw [if_pos ⟨by omega, hu.2⟩]
          rw [this, ind, if_pos (by omega)]; norm_num
      _ ≤ ∑ u ∈ range T, ind (kI hole n u) j ^ 2 := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro u hu
            rw [mem_filter, mem_range] at hu
            rw [mem_range]; omega
          · intro _ _ _; positivity

/-- Case II witness pair for grid index `j`: grid points `a ≤ j < b` in one cell, or `(j, j)`. -/
noncomputable def W {K : ℕ} (hole : ℝ → Fin K) (n j : ℕ) : ℕ × ℕ :=
  if h : ∃ ab : ℕ × ℕ, ab.1 ≤ j ∧ j < ab.2 ∧ ab.2 ≤ n ∧
      hole ((ab.1 : ℝ) / n) = hole ((ab.2 : ℝ) / n) then Classical.choose h else (j, j)

lemma W_spec {K : ℕ} (hole : ℝ → Fin K) (n j : ℕ) (hj : j ≤ n) :
    (W hole n j).1 ≤ j ∧ (W hole n j).2 ≤ n ∧
      hole (((W hole n j).1 : ℝ) / n) = hole (((W hole n j).2 : ℝ) / n) ∧
      (¬ cutP hole n j → j < (W hole n j).2) := by
  unfold W
  split_ifs with h
  · have := Classical.choose_spec h
    exact ⟨this.1, this.2.2.1, this.2.2.2, fun _ => this.2.1⟩
  · refine ⟨le_rfl, hj, rfl, fun hc => absurd ?_ hc⟩
    intro a ha b hb hbn heq
    exact h ⟨(a, b), ha, hb, hbn, heq⟩

/-- Case II arrivals: pair `p < n R` (subjects `2p, 2p+1`) at the witness of `j = p / R`. -/
noncomputable def kII {K : ℕ} (hole : ℝ → Fin K) (n R u : ℕ) : ℕ :=
  if u < 2 * (n * R) then
    (if u % 2 = 0 then (W hole n (u / 2 / R)).1 else (W hole n (u / 2 / R)).2)
  else n

lemma kII_pair {K : ℕ} (hole : ℝ → Fin K) (n R p : ℕ) (hp : p < n * R) :
    kII hole n R (2 * p) = (W hole n (p / R)).1 ∧
      kII hole n R (2 * p + 1) = (W hole n (p / R)).2 := by
  have h1 : 2 * p < 2 * (n * R) := by omega
  have h2 : 2 * p + 1 < 2 * (n * R) := by omega
  have e0 : (2 * p) % 2 = 0 := by omega
  have e1 : (2 * p + 1) % 2 = 1 := by omega
  have d0 : (2 * p) / 2 = p := by omega
  have d1 : (2 * p + 1) / 2 = p := by omega
  unfold kII
  simp [h1, h2, e0, e1, d0, d1]

lemma div_lt_of_lt_mul' {p n R : ℕ} (hp : p < n * R) : p / R < n := by
  rcases Nat.eq_zero_or_pos R with h | h
  · subst h; simp at hp
  · exact (Nat.div_lt_iff_lt_mul h).mpr hp

lemma kII_le {K : ℕ} (hole : ℝ → Fin K) (n R u : ℕ) : kII hole n R u ≤ n := by
  unfold kII
  split_ifs with h1 h2
  · have := W_spec hole n (u / 2 / R) (div_lt_of_lt_mul' (by omega)).le
    have := div_lt_of_lt_mul' (p := u / 2) (n := n) (R := R) (by omega)
    omega
  · exact (W_spec hole n (u / 2 / R) (div_lt_of_lt_mul' (by omega)).le).2.1
  · exact le_rfl

theorem caseII {T n K R : ℕ} (hR : 0 < R) (h4 : 4 * (n * R) ≤ T) (hole : ℝ → Fin K) (j : ℕ)
    (hj : j < n) :
    ∃ c : Fin T → ℝ,
      (∀ coin : Fin T → Bool, Dj (fun t : Fin T => kII hole n R t.val)
          (assign hole (fun t : Fin T => ((kII hole n R t.val : ℕ) : ℝ) / n) coin) j =
            X c univ coin) ∧
        (if cutP hole n j then (0 : ℝ) else (R : ℝ)) ≤ ∑ t, c t ^ 2 := by
  set g : ℕ → ℝ := fun u => ind (kII hole n R u) j with hg
  set cN : ℕ → ℝ := fun u => if u % 2 = 0 ∧ u < 2 * (n * R) then g u - g (u + 1) else 0 with hcN
  have hzero : ∀ u, 2 * (n * R) ≤ u → g u = 0 := by
    intro u hu
    simp only [hg, ind, kII, if_neg (show ¬ u < 2 * (n * R) by omega)]
    rw [if_neg (by omega)]
  refine ⟨fun t => cN t.val, ?_, ?_⟩
  · intro coin
    have hpair : ∀ p < n * R,
        cellOf hole (fun t : Fin T => ((kII hole n R t.val : ℕ) : ℝ) / n) (2 * p) =
          cellOf hole (fun t : Fin T => ((kII hole n R t.val : ℕ) : ℝ) / n) (2 * p + 1) := by
      intro p hp
      have h1 : 2 * p < T := by omega
      have h2 : 2 * p + 1 < T := by omega
      obtain ⟨k0, k1⟩ := kII_pair hole n R p hp
      have hW := (W_spec hole n (p / R) (div_lt_of_lt_mul' hp).le).2.2.1
      simp [cellOf, h1, h2, k0, k1, hW]
    unfold Dj X
    calc ∑ t : Fin T, ind (kII hole n R t.val) j *
          sg' (assign hole (fun t : Fin T => ((kII hole n R t.val : ℕ) : ℝ) / n) coin t)
        = ∑ t : Fin T, g t.val * sg (fpair (coinOf coin) t.val) := by
          apply sum_congr rfl
          intro t _
          by_cases ht : t.val < 2 * (n * R)
          · rw [assign_pairs hole _ coin (n * R) h4 hpair t ht]; rfl
          · rw [hzero t.val (by omega)]
            simp [hg, ind, kII, if_neg ht, show ¬ n ≤ j by omega]
      _ = ∑ u ∈ range T, g u * sg (fpair (coinOf coin) u) :=
          Fin.sum_univ_eq_sum_range (fun u => g u * sg (fpair (coinOf coin) u)) T
      _ = ∑ u ∈ range (2 * (n * R)), g u * sg (fpair (coinOf coin) u) :=
          sum_range_cut (by omega) _ (fun u hu => by rw [hzero u hu, zero_mul])
      _ = ∑ u ∈ range (2 * (n * R)),
            (if u % 2 = 0 then g u - g (u + 1) else 0) * sg (coinOf coin u) :=
          pair_sum g (coinOf coin) (n * R)
      _ = ∑ u ∈ range (2 * (n * R)), cN u * sg (coinOf coin u) := by
          apply sum_congr rfl
          intro u hu
          rw [mem_range] at hu
          simp only [hcN, hu, and_true]
      _ = ∑ u ∈ range T, cN u * sg (coinOf coin u) := by
          refine (sum_range_cut (by omega) _ (fun u hu => ?_)).symm
          simp only [hcN]
          rw [if_neg (by omega), zero_mul]
      _ = ∑ t : Fin T, cN t.val * sg (coin t) := (sum_fin_coin cN coin).symm
  · split_ifs with hcut
    · exact sum_nonneg (fun _ _ => sq_nonneg _)
    · refine le_trans ?_ (le_of_eq (Fin.sum_univ_eq_sum_range (fun u => cN u ^ 2) T).symm)
      have hjn : j * R + R ≤ n * R := by
        have := Nat.mul_le_mul_right R (show j + 1 ≤ n by omega)
        rw [Nat.add_mul, one_mul] at this; exact this
      calc (R : ℝ) = ∑ p ∈ Ico (j * R) (j * R + R), (1 : ℝ) := by simp
        _ = ∑ p ∈ Ico (j * R) (j * R + R), cN (2 * p) ^ 2 := by
            apply sum_congr rfl
            intro p hp
            rw [mem_Ico] at hp
            have hpR : p / R = j := by
              apply Nat.div_eq_of_lt_le
              · exact hp.1
              · rw [Nat.add_mul, one_mul]; exact hp.2
            have hp' : p < n * R := by omega
            obtain ⟨k0, k1⟩ := kII_pair hole n R p hp'
            obtain ⟨wa, -, -, wb⟩ := W_spec hole n (p / R) (div_lt_of_lt_mul' hp').le
            rw [hpR] at k0 k1 wb
            have wb' := wb hcut
            have wa' := (W_spec hole n j hj.le).1
            have hc2 : cN (2 * p) = 1 := by
              simp only [hcN, hg]
              rw [if_pos ⟨by omega, by omega⟩, k0, k1, ind, ind, if_pos wa', if_neg (by omega)]
              norm_num
            rw [hc2]; norm_num
        _ = ∑ u ∈ (Ico (j * R) (j * R + R)).image (fun p => 2 * p), cN u ^ 2 := by
            rw [sum_image]
            intro a _ b _ hab; simpa using hab
        _ ≤ ∑ u ∈ range T, cN u ^ 2 := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro u hu
              rw [mem_image] at hu
              obtain ⟨p, hp, rfl⟩ := hu
              rw [mem_Ico] at hp
              rw [mem_range]; omega
            · intro _ _ _; positivity

lemma quarter_le (T n : ℕ) (hT : T ≤ 16 * (n * n)) :
    (T : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 * Real.sqrt n := by
  have hq : ((T : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = T := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have h2 : (2 * Real.sqrt n) ^ (4 : ℕ) = 16 * ((n : ℝ) * n) := by
    rw [mul_pow, show Real.sqrt n ^ 4 = (Real.sqrt n ^ 2) ^ 2 by ring,
      Real.sq_sqrt (by positivity)]
    ring
  rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (4 : ℕ) ≠ 0), hq, h2]
  exact_mod_cast hT

theorem main_bound : ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, 2 ≤ T₀ ∧
      ∀ T : ℕ, T₀ ≤ T → Even T →
        ∀ K : ℕ, 1 ≤ K → ∀ hole : ℝ → Fin K,
          ∃ x : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧
            c * (T : ℝ) ^ ((1 : ℝ) / 4) ≤ PigeonholeDesign.Upper.phdExp hole x := by
  refine ⟨1 / 100, by norm_num, 64, by norm_num, ?_⟩
  intro T hT hEven K _ hole
  set n := Nat.sqrt T with hn_def
  have hn8 : 8 ≤ n := Nat.le_sqrt.mpr (by omega)
  have hnT : n * n ≤ T := Nat.sqrt_le T
  have hTn : T < (n + 1) * (n + 1) := Nat.lt_succ_sqrt T
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hq := quarter_le T n (by nlinarith)
  have hsq : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hsqp : 0 < Real.sqrt n / 2 := div_pos (Real.sqrt_pos.mpr hnR) (by norm_num)
  suffices H : ∃ x : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧
      Real.sqrt n / 48 ≤ phdExp hole x by
    obtain ⟨x, hx, hb⟩ := H
    exact ⟨x, hx, by linarith⟩
  have hIcc : ∀ (kN : ℕ → ℕ), (∀ u, kN u ≤ n) →
      ∀ t : Fin T, ((kN t.val : ℕ) : ℝ) / n ∈ Set.Icc (0 : ℝ) 1 := by
    intro kN hk t
    exact ⟨by positivity, (div_le_one hnR).mpr (by exact_mod_cast hk _)⟩
  set h := n / 2 with hh
  set A := (range h).filter (fun u => cutP hole n u) with hA
  by_cases hcase : h ≤ 2 * A.card
  · set V : ℕ → ℝ := fun j => if h ≤ j then (A.card : ℝ) else 0 with hV
    refine ⟨_, hIcc _ (kI_le hole n), ?_⟩
    have hfr := frame hEven hn0 hole (kI hole n) (kI_le hole n) V (by
      intro j hj
      obtain ⟨c, hc1, hc2⟩ := caseI (T := T) (by nlinarith) hole j hj
      refine ⟨c, hc1, le_trans ?_ hc2⟩
      simp only [hV]
      split_ifs with hhj
      · have hsub : (range h).filter (fun u => cutP hole n u) ⊆
            (range (j + 1)).filter (fun u => cutP hole n u) :=
          filter_subset_filter _ (fun x hx => by rw [mem_range] at hx ⊢; omega)
        exact_mod_cast card_le_card hsub
      · positivity)
    refine le_trans ?_ hfr
    have hs : Real.sqrt n / 2 ≤ Real.sqrt (3 * A.card) := by
      rw [Real.le_sqrt' hsqp, div_pow, Real.sq_sqrt hnR.le]
      have : n ≤ 12 * A.card := by omega
      have : (n : ℝ) ≤ 12 * A.card := by exact_mod_cast this
      linarith
    have hnh : (n : ℝ) / 2 ≤ ((n - h : ℕ) : ℝ) := by
      have : n ≤ 2 * (n - h) := by omega
      have : (n : ℝ) ≤ 2 * ((n - h : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have hsum : ((n - h : ℕ) : ℝ) * (Real.sqrt (3 * A.card) / 3) ≤
        ∑ j ∈ range n, Real.sqrt (3 * V j) / 3 := by
      calc ((n - h : ℕ) : ℝ) * (Real.sqrt (3 * A.card) / 3)
          = ∑ j ∈ Ico h n, Real.sqrt (3 * (A.card : ℝ)) / 3 := by
            rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ = ∑ j ∈ Ico h n, Real.sqrt (3 * V j) / 3 :=
            sum_congr rfl (fun j hj => by simp only [hV, if_pos (mem_Ico.mp hj).1])
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg
            (fun j hj => mem_range.mpr (mem_Ico.mp hj).2) (fun _ _ _ => by positivity)
    have e : (1 / (n : ℝ)) * ((n / 2) * ((Real.sqrt n / 2) / 3)) = Real.sqrt n / 12 := by
      field_simp; ring
    calc Real.sqrt n / 48 ≤ (1 / (n : ℝ)) * ((n / 2) * ((Real.sqrt n / 2) / 3)) := by
          rw [e]; linarith
      _ ≤ (1 / (n : ℝ)) * (((n - h : ℕ) : ℝ) * (Real.sqrt (3 * A.card) / 3)) := by gcongr
      _ ≤ _ := by gcongr
  · 
    set R := n / 4 with hRdef
    have hR : 0 < R := by omega
    have h4 : 4 * (n * R) ≤ T := by
      have : 4 * R ≤ n := by omega
      calc 4 * (n * R) = n * (4 * R) := by ring
        _ ≤ n * n := Nat.mul_le_mul_left n this
        _ ≤ T := hnT
    set V : ℕ → ℝ := fun j => if cutP hole n j then (0 : ℝ) else (R : ℝ) with hV
    refine ⟨_, hIcc _ (kII_le hole n R), ?_⟩
    have hfr := frame hEven hn0 hole (kII hole n R) (kII_le hole n R) V (by
      intro j hj
      obtain ⟨c, hc1, hc2⟩ := caseII hR h4 hole j hj
      exact ⟨c, hc1, hc2⟩)
    refine le_trans ?_ hfr
    set B := (range h).filter (fun u => ¬ cutP hole n u) with hB
    have hBA : A.card + B.card = h := by
      rw [hA, hB, card_filter_add_card_filter_not, card_range]
    have hs : Real.sqrt n / 2 ≤ Real.sqrt (3 * (R : ℝ)) := by
      rw [Real.le_sqrt' hsqp, div_pow, Real.sq_sqrt hnR.le]
      have : n ≤ 12 * R := by omega
      have : (n : ℝ) ≤ 12 * (R : ℝ) := by exact_mod_cast this
      linarith
    have hnB : (n : ℝ) / 8 ≤ (B.card : ℝ) := by
      have : n ≤ 8 * B.card := by omega
      have : (n : ℝ) ≤ 8 * (B.card : ℝ) := by exact_mod_cast this
      linarith
    have hsum : (B.card : ℝ) * (Real.sqrt (3 * (R : ℝ)) / 3) ≤
        ∑ j ∈ range n, Real.sqrt (3 * V j) / 3 := by
      calc (B.card : ℝ) * (Real.sqrt (3 * (R : ℝ)) / 3)
          = ∑ j ∈ B, Real.sqrt (3 * (R : ℝ)) / 3 := by rw [sum_const, nsmul_eq_mul]
        _ = ∑ j ∈ B, Real.sqrt (3 * V j) / 3 := sum_congr rfl (fun j hj => by
              rw [hB, mem_filter] at hj; simp only [hV, if_neg hj.2])
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun j hj => by
              rw [hB, mem_filter, mem_range] at hj; rw [mem_range]; omega)
            (fun _ _ _ => by positivity)
    have e : (1 / (n : ℝ)) * ((n / 8) * ((Real.sqrt n / 2) / 3)) = Real.sqrt n / 48 := by
      field_simp; ring
    calc Real.sqrt n / 48 = (1 / (n : ℝ)) * ((n / 8) * ((Real.sqrt n / 2) / 3)) := e.symm
      _ ≤ (1 / (n : ℝ)) * ((B.card : ℝ) * (Real.sqrt (3 * (R : ℝ)) / 3)) := by gcongr
      _ ≤ _ := by gcongr

end PHDLower


theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, 2 ≤ T₀ ∧
      ∀ T : ℕ, T₀ ≤ T → Even T →
        ∀ K : ℕ, 1 ≤ K → ∀ hole : ℝ → Fin K,
          ∃ x : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧
            c * (T : ℝ) ^ ((1 : ℝ) / 4) ≤ PigeonholeDesign.Upper.phdExp hole x := by
  exact PHDLower.main_bound
