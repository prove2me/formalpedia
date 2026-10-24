-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.seed_permutation_weight_independent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T14:27:23.967976+00:00
-- url     : https://prove2.me/submissions/67a835a0-5764-493c-b884-9fc00173eed8

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23


noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

namespace X8S

variable {n : ℕ}

/-- plain inner product of functions -/
def ip (f g : Word n 2 → ℂ) : ℂ := ∑ x, conj (f x) * g x

/-- permutation action -/
def act (p : Equiv.Perm (Fin n)) (f : Word n 2 → ℂ) : Word n 2 → ℂ :=
  fun x => f (fun i => x (p i))

/-- ladder operator: set one bit to c -/
def Lop (c : Fin 2) (f : Word n 2 → ℂ) : Word n 2 → ℂ :=
  fun x => ∑ i, if x i ≠ c then f (Function.update x i c) else 0

lemma inner_eq (f g : EuclideanSpace ℂ (Word n 2)) :
    inner ℂ f g = ip (fun x => f x) (fun x => g x) := by
  simp [ip, PiLp.inner_apply, mul_comm]

lemma mulVec_eq (p : Equiv.Perm (Fin n)) (f : Word n 2 → ℂ) :
    (wordPermutationMatrix n 2 p).mulVec f = act p f := by
  funext x
  simp only [wordPermutationMatrix, Information100.P34.permutationMatrix, Matrix.mulVec,
    dotProduct, act]
  rw [Finset.sum_eq_single (fun i => x (p i))]
  · simp only [ite_mul, one_mul, zero_mul]
    rw [if_pos]
    funext i; simp [Equiv.arrowCongr_apply]
  · intro y _ hy
    rw [if_neg, zero_mul]
    intro h; apply hy; rw [h]; funext i; simp [Equiv.arrowCongr_apply]
  · simp

lemma ip_conj (f g : Word n 2 → ℂ) : ip f g = conj (ip g f) := by
  simp [ip, map_sum, mul_comm]

lemma ip_act_left (q : Equiv.Perm (Fin n)) (f g : Word n 2 → ℂ) :
    ip (act q f) g = ip f (act q⁻¹ g) := by
  unfold ip act
  let e : Word n 2 ≃ Word n 2 :=
    { toFun := fun x i => x (q i), invFun := fun y i => y (q⁻¹ i),
      left_inv := fun x => by funext i; simp,
      right_inv := fun y => by funext i; simp }
  refine Fintype.sum_equiv e _ _ ?_
  intro x; simp [e]

lemma act_act (p r : Equiv.Perm (Fin n)) (f : Word n 2 → ℂ) :
    act p (act r f) = act (p * r) f := by
  funext x; simp [act, Equiv.Perm.mul_apply]

lemma act_one (f : Word n 2 → ℂ) : act 1 f = f := by
  funext x; simp [act]

lemma Lop_act (c : Fin 2) (p : Equiv.Perm (Fin n)) (f : Word n 2 → ℂ) :
    Lop c (act p f) = act p (Lop c f) := by
  funext x
  simp only [Lop, act]
  rw [← Equiv.sum_comp p]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (fun j => Function.update x (p i) c (p j)) = Function.update (fun j => x (p j)) i c := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_apply, h, p.injective.ne h]
  simp only [this, Function.update_self]

/-- bit swap involution at a site -/
lemma Lop_adj (c d : Fin 2) (hcd : c ≠ d) (f g : Word n 2 → ℂ) :
    ip (Lop c f) g = ip f (Lop d g) := by
  unfold ip Lop
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  let τ : Word n 2 → Word n 2 := fun x => Function.update x i (if x i = c then d else c)
  have hτ : Function.Involutive τ := by
    intro x; funext j
    by_cases h : j = i
    · subst h; simp only [τ, Function.update_self]
      by_cases hx : x j = c
      · simp [hx, hcd.symm]
      · simp [hx]
        have : ∀ a c d : Fin 2, a ≠ c → c ≠ d → a = d := by decide
        exact (this _ _ _ hx hcd).symm
    · simp [τ, h]
  refine Fintype.sum_equiv (Function.Involutive.toPerm τ hτ) _ _ ?_
  intro x
  simp only [Function.Involutive.coe_toPerm, τ, Function.update_self]
  have h2 : ∀ a c d : Fin 2, a ≠ c → c ≠ d → a = d := by decide
  by_cases hx : x i = c
  · have : (if d ≠ d then g (Function.update (Function.update x i d) i d) else 0) = 0 := by simp
    simp [hx, hcd.symm]
  · have hd : x i = d := h2 _ _ _ hx hcd
    have hu : Function.update x i d = x := Function.update_eq_self_iff.mpr hd.symm
    simp [hx, hcd, hu]

end X8S

end QAlgorithms.Papers.Independent.Gap48.P23


noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

namespace X8S

variable {n : ℕ}

def sg (a b : Fin 2) : ℂ :=
  if a = 0 ∧ b = 1 then ((Real.sqrt 2)⁻¹ : ℂ) else if a = 1 ∧ b = 0 then -((Real.sqrt 2)⁻¹ : ℂ) else 0

def wt (k : TwoRowShape n) (x : Word n 2) : ℕ :=
  ∑ j : Fin (degree n k), if wordAt x j.val = 1 then 1 else 0

def S (k : TwoRowShape n) (x : Word n 2) : ℂ :=
  ∏ j : Fin k.val, sg (wordAt x (degree n k + 2 * j.val)) (wordAt x (degree n k + 2 * j.val + 1))

def E (k : TwoRowShape n) (u : ℕ) : Word n 2 → ℂ := fun x => if wt k x = u then S k x else 0

def aw (k : TwoRowShape n) (u : ℕ) : ℂ := ((Real.sqrt (Nat.choose (degree n k) u : ℝ))⁻¹ : ℂ)

lemma seed_eq (k : TwoRowShape n) (w : Fin (degree n k + 1)) :
    (fun x => schurSeed n k w x) = fun x => aw k w.val * E k w.val x := by
  funext x
  simp only [E]; rw [mul_ite, mul_zero]; rfl

lemma deg_le (k : TwoRowShape n) : degree n k + 2 * k.val = n := by
  have := k.isLt; unfold degree; omega

lemma wordAt_update (x : Word n 2) (i : Fin n) (c : Fin 2) (t : ℕ) :
    wordAt (Function.update x i c) t = if t = i.val then c else wordAt x t := by
  unfold wordAt
  by_cases ht : t < n
  · simp only [ht, dif_pos, Function.update_apply]
    by_cases h : t = i.val
    · simp [h, Fin.ext_iff]
    · have : (⟨t, ht⟩ : Fin n) ≠ i := fun e => h (by rw [← e])
      simp [h, this]
  · have : t ≠ i.val := by omega
    simp [ht, this]

lemma pair_cancel (c a b : Fin 2) :
    (if a ≠ c then sg c b else 0) + (if b ≠ c then sg a c else 0) = 0 := by
  fin_cases c <;> fin_cases a <;> fin_cases b <;> simp [sg]

lemma pair_cancel' (c a b : Fin 2) :
    (if b ≠ c then sg a c else 0) + (if a ≠ c then sg c b else 0) = 0 := by
  rw [add_comm]; exact pair_cancel c a b

lemma S_update (k : TwoRowShape n) (x : Word n 2) (i : Fin n) (c : Fin 2) (j : Fin k.val)
    (hi : i.val = degree n k + 2 * j.val ∨ i.val = degree n k + 2 * j.val + 1) :
    S k (Function.update x i c) =
      sg (wordAt (Function.update x i c) (degree n k + 2 * j.val))
        (wordAt (Function.update x i c) (degree n k + 2 * j.val + 1)) *
      ∏ j' ∈ Finset.univ.erase j, sg (wordAt x (degree n k + 2 * j'.val))
        (wordAt x (degree n k + 2 * j'.val + 1)) := by
  unfold S
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  congr 1
  refine Finset.prod_congr rfl fun j' hj' => ?_
  have hne : j'.val ≠ j.val := fun e => (Finset.mem_erase.mp hj').1 (Fin.ext e)
  rw [wordAt_update, wordAt_update, if_neg (by omega), if_neg (by omega)]

lemma wordAt_fin (x : Word n 2) (i : Fin n) : wordAt x i.val = x i := by
  simp [wordAt]

/-- singlet cancellation -/
lemma singlet_zero (k : TwoRowShape n) (c : Fin 2) (x : Word n 2) :
    ∑ i : Fin n, (if degree n k ≤ i.val ∧ x i ≠ c then S k (Function.update x i c) else 0) = 0 := by
  set m := degree n k with hm
  have hn := deg_le k
  rw [← hm] at hn
  let g : Fin n → Fin n := fun i =>
    if h : m ≤ i.val then
      (if h2 : (i.val - m) % 2 = 0 then ⟨i.val + 1, by omega⟩ else ⟨i.val - 1, by omega⟩)
    else i
  refine Finset.sum_ninvolution g ?_ ?_ (fun _ => Finset.mem_univ _) ?_
  · intro i
    by_cases hi : m ≤ i.val
    · have hk := deg_le k
      set j : Fin k.val := ⟨(i.val - m) / 2, by omega⟩ with hj
      have hia : m + 2 * j.val < n := by simp [hj]; omega
      have hib : m + 2 * j.val + 1 < n := by simp [hj]; omega
      set ia : Fin n := ⟨m + 2 * j.val, hia⟩
      set ib : Fin n := ⟨m + 2 * j.val + 1, hib⟩
      set P := ∏ j' ∈ Finset.univ.erase j, sg (wordAt x (degree n k + 2 * j'.val))
        (wordAt x (degree n k + 2 * j'.val + 1))
      have key : (if m ≤ ia.val ∧ x ia ≠ c then S k (Function.update x ia c) else 0) +
          (if m ≤ ib.val ∧ x ib ≠ c then S k (Function.update x ib c) else 0) = 0 := by
        rw [S_update k x ia c j (Or.inl rfl), S_update k x ib c j (Or.inr rfl)]
        simp only [wordAt_update, ia, ib]
        simp only [← hm]
        have h1 : m ≤ m + 2 * j.val := by omega
        have h2 : m ≤ m + 2 * j.val + 1 := by omega
        have ha : wordAt x (m + 2 * j.val) = x ia := wordAt_fin x ia
        have hb : wordAt x (m + 2 * j.val + 1) = x ib := wordAt_fin x ib
        simp only [h1, h2, true_and, if_true, if_neg (show m + 2 * j.val + 1 ≠ m + 2 * j.val by omega),
          if_neg (show m + 2 * j.val ≠ m + 2 * j.val + 1 by omega), ha, hb]
        have hc := pair_cancel c (x ia) (x ib)
        change ((if x ia ≠ c then _ else 0) + (if x ib ≠ c then _ else 0)) = 0
        generalize (∏ x_1 ∈ Finset.univ.erase j, sg (wordAt x (m + 2 * ↑x_1)) (wordAt x (m + 2 * ↑x_1 + 1))) = Q
        have e : ((if x ia ≠ c then sg c (x ib) * Q else 0) + if x ib ≠ c then sg (x ia) c * Q else 0)
            = ((if x ia ≠ c then sg c (x ib) else 0) + if x ib ≠ c then sg (x ia) c else 0) * Q := by
          rw [add_mul, ite_mul, ite_mul, zero_mul]
        rw [e, hc, zero_mul]
      by_cases he : (i.val - m) % 2 = 0
      · have e1 : i = ia := by ext; simp [ia, hj]; omega
        have e2 : g i = ib := by ext; simp [g, hi, he, ib, hj]; omega
        rw [e2, e1]; exact key
      · have e1 : i = ib := by ext; simp [ib, hj]; omega
        have e2 : g i = ia := by ext; simp [g, hi, he, ia, hj]; omega
        rw [e2, e1, add_comm]; exact key
    · have : g i = i := by simp [g, hi]
      simp [this, hi]
  · intro i hne
    by_cases hi : m ≤ i.val
    · simp only [g, hi, dif_pos]
      split_ifs <;> intro h <;> simp [Fin.ext_iff] at h <;> omega
    · exfalso; apply hne; simp [hi]
  · intro i
    by_cases hi : m ≤ i.val
    · simp only [g, hi, dif_pos]
      by_cases he : (i.val - m) % 2 = 0
      · simp only [he, dif_pos]
        have h1 : m ≤ i.val + 1 := by omega
        have h2 : ¬ (i.val + 1 - m) % 2 = 0 := by omega
        simp [h1, h2]
      · simp only [he, dif_neg, not_false_eq_true]
        have h1 : m ≤ i.val - 1 := by omega
        have h2 : (i.val - 1 - m) % 2 = 0 := by omega
        simp only [h1, dif_pos, h2]
        ext; simp; omega
    · simp [g, hi]

lemma S_update_low (k : TwoRowShape n) (x : Word n 2) (i : Fin n) (c : Fin 2)
    (hi : i.val < degree n k) : S k (Function.update x i c) = S k x := by
  unfold S
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [wordAt_update, wordAt_update, if_neg (by omega), if_neg (by omega)]

lemma wt_update_high (k : TwoRowShape n) (x : Word n 2) (i : Fin n) (c : Fin 2)
    (hi : degree n k ≤ i.val) : wt k (Function.update x i c) = wt k x := by
  unfold wt
  refine Finset.sum_congr rfl fun j _ => ?_
  have := j.isLt
  simp only [wordAt_update, show j.val ≠ i.val by omega, if_false]

lemma wt_update_low (k : TwoRowShape n) (x : Word n 2) (i : Fin n) (c : Fin 2)
    (hi : i.val < degree n k) :
    wt k (Function.update x i c) + (if x i = 1 then 1 else 0) =
      wt k x + (if c = 1 then 1 else 0) := by
  unfold wt
  set i' : Fin (degree n k) := ⟨i.val, hi⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i'), ← Finset.add_sum_erase _ _ (Finset.mem_univ i')]
  have hrest : ∑ j ∈ Finset.univ.erase i', (if wordAt (Function.update x i c) j.val = 1 then 1 else 0) =
      ∑ j ∈ Finset.univ.erase i', (if wordAt x j.val = 1 then 1 else 0) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hne : j.val ≠ i.val := fun e => (Finset.mem_erase.mp hj).1 (Fin.ext e)
    rw [wordAt_update, if_neg hne]
  rw [hrest, wordAt_update, if_pos rfl, wordAt_fin]
  omega

lemma wt_le (k : TwoRowShape n) (x : Word n 2) : wt k x ≤ degree n k := by
  unfold wt
  calc (∑ j : Fin (degree n k), if wordAt x j.val = 1 then 1 else 0)
      ≤ ∑ _j : Fin (degree n k), 1 := Finset.sum_le_sum fun j _ => by split_ifs <;> omega
    _ = degree n k := by simp

lemma cnt_split (k : TwoRowShape n) (P : Fin 2 → Prop) [DecidablePred P] (x : Word n 2) :
    (∑ i : Fin n, if i.val < degree n k ∧ P (x i) then 1 else 0) =
      ∑ j : Fin (degree n k), if P (wordAt x j.val) then 1 else 0 := by
  have hn := deg_le k
  have h1 : (∑ i : Fin n, if i.val < degree n k ∧ P (x i) then 1 else 0) =
      ∑ t ∈ Finset.range n, if t < degree n k ∧ P (wordAt x t) then 1 else 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun t => if t < degree n k ∧ P (wordAt x t) then 1 else 0)]
    simp only [wordAt_fin]
  have h2 : (∑ j : Fin (degree n k), if P (wordAt x j.val) then 1 else 0) =
      ∑ t ∈ Finset.range (degree n k), if P (wordAt x t) then 1 else 0 :=
    Fin.sum_univ_eq_sum_range (fun t => if P (wordAt x t) then 1 else 0) _
  rw [h1, h2, ← Finset.sum_range_add_sum_Ico _ (show degree n k ≤ n by omega)]
  rw [Finset.sum_eq_zero (s := Finset.Ico (degree n k) n) (fun t ht => by
    have := (Finset.mem_Ico.mp ht).1; simp; omega)]
  rw [add_zero]
  refine Finset.sum_congr rfl fun t ht => ?_
  have : t < degree n k := Finset.mem_range.mp ht
  simp [this]

lemma cnt1 (k : TwoRowShape n) (x : Word n 2) :
    (∑ i : Fin n, if i.val < degree n k ∧ x i = 1 then 1 else 0) = wt k x :=
  cnt_split k (fun a => a = 1) x

lemma cnt0 (k : TwoRowShape n) (x : Word n 2) :
    (∑ i : Fin n, if i.val < degree n k ∧ x i = 0 then 1 else 0) = degree n k - wt k x := by
  have h := cnt_split k (fun a => a = 0) x
  have hs : (∑ j : Fin (degree n k), if wordAt x j.val = 0 then 1 else 0) + wt k x = degree n k := by
    unfold wt
    rw [← Finset.sum_add_distrib]
    calc (∑ j : Fin (degree n k), ((if wordAt x j.val = 0 then 1 else 0) +
          (if wordAt x j.val = 1 then 1 else 0)))
        = ∑ _j : Fin (degree n k), 1 := Finset.sum_congr rfl fun j _ => by
          have : ∀ a : Fin 2, (if a = 0 then 1 else 0) + (if a = 1 then 1 else 0) = 1 := by decide
          exact this _
      _ = degree n k := by simp
  rw [h]; omega

/-- decomposition of a ladder image of E -/
lemma Lop_E (k : TwoRowShape n) (c : Fin 2) (u : ℕ) (x : Word n 2) :
    Lop c (E k u) x = ∑ i : Fin n,
      (if i.val < degree n k ∧ x i ≠ c ∧ wt k (Function.update x i c) = u then S k x else 0) := by
  unfold Lop E
  have hz := singlet_zero k c x
  have : ∀ i : Fin n, (if x i ≠ c then (if wt k (Function.update x i c) = u then
      S k (Function.update x i c) else 0) else 0) =
      (if i.val < degree n k ∧ x i ≠ c ∧ wt k (Function.update x i c) = u then S k x else 0) +
      (if wt k x = u then (if degree n k ≤ i.val ∧ x i ≠ c then S k (Function.update x i c) else 0)
        else 0) := by
    intro i
    by_cases hi : i.val < degree n k
    · rw [S_update_low k x i c hi]
      have : ¬ degree n k ≤ i.val := by omega
      by_cases hx : x i ≠ c <;> by_cases hw : wt k (Function.update x i c) = u <;>
        by_cases hw' : wt k x = u <;> simp [hi, hx, hw, hw', this]
    · have hi' : degree n k ≤ i.val := by omega
      rw [wt_update_high k x i c hi']
      by_cases hx : x i ≠ c <;> by_cases hw' : wt k x = u <;> simp [hi, hi', hx, hw']
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib]
  have e2 : (∑ i : Fin n, if wt k x = u then (if degree n k ≤ i.val ∧ x i ≠ c then
      S k (Function.update x i c) else 0) else 0) = 0 := by
    split_ifs
    · exact hz
    · simp
  rw [e2, add_zero]

lemma ne0 {a : Fin 2} (h : a ≠ 0) : a = 1 := by fin_cases a <;> simp_all
lemma ne1 {a : Fin 2} (h : a ≠ 1) : a = 0 := by fin_cases a <;> simp_all

lemma L0_E (k : TwoRowShape n) (u : ℕ) :
    Lop 0 (E k u) = fun x => ((u : ℂ) + 1) * E k (u + 1) x := by
  funext x
  rw [Lop_E]
  have : ∀ i : Fin n, (if i.val < degree n k ∧ x i ≠ 0 ∧ wt k (Function.update x i 0) = u
      then S k x else 0) =
      ((if i.val < degree n k ∧ x i = 1 then 1 else 0 : ℕ) : ℂ) * E k (u + 1) x := by
    intro i
    unfold E
    by_cases hi : i.val < degree n k
    · have hw := wt_update_low k x i 0 hi
      by_cases hx : x i = 1
      · simp only [hx, if_true] at hw
        simp only [Fin.zero_eta, Fin.isValue, zero_ne_one, if_false, add_zero] at hw
        by_cases h : wt k x = u + 1
        · have : wt k (Function.update x i 0) = u := by omega
          simp [hi, hx, h, this]
        · have : wt k (Function.update x i 0) ≠ u := by omega
          simp [hi, hx, h, this]
      · have : ¬ x i ≠ 0 := fun h => hx (ne0 h)
        simp [hi, hx, this]
    · simp [hi]
  rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.sum_mul, ← Nat.cast_sum, cnt1]
  unfold E
  split_ifs with h
  · rw [h]; push_cast; ring
  · simp

lemma L1_E (k : TwoRowShape n) (u : ℕ) :
    Lop 1 (E k u) = fun x => if wt k x + 1 = u then
      ((degree n k - wt k x : ℕ) : ℂ) * S k x else 0 := by
  funext x
  rw [Lop_E]
  have : ∀ i : Fin n, (if i.val < degree n k ∧ x i ≠ 1 ∧ wt k (Function.update x i 1) = u
      then S k x else 0) =
      ((if i.val < degree n k ∧ x i = 0 then 1 else 0 : ℕ) : ℂ) *
        (if wt k x + 1 = u then S k x else 0) := by
    intro i
    by_cases hi : i.val < degree n k
    · have hw := wt_update_low k x i 1 hi
      by_cases hx : x i = 0
      · simp only [hx, Fin.isValue, zero_ne_one, if_false, add_zero, if_true] at hw
        by_cases h : wt k x + 1 = u
        · have : wt k (Function.update x i 1) = u := by omega
          simp [hi, hx, h, this]
        · have : wt k (Function.update x i 1) ≠ u := by omega
          simp [hi, hx, h, this]
      · have : ¬ x i ≠ 1 := fun h => hx (ne1 h)
        simp [hi, hx, this]
    · simp [hi]
  rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.sum_mul, ← Nat.cast_sum, cnt0]
  split_ifs <;> simp

lemma L1_E_succ (k : TwoRowShape n) (u : ℕ) :
    Lop 1 (E k (u + 1)) = fun x => ((degree n k - u : ℕ) : ℂ) * E k u x := by
  rw [L1_E]; funext x; unfold E
  by_cases h : wt k x = u
  · simp [h]
  · have : ¬ wt k x + 1 = u + 1 := by omega
    simp [h, this]

lemma L1_E_zero (k : TwoRowShape n) : Lop 1 (E k 0) = fun _ => 0 := by
  rw [L1_E]; funext x; simp

end X8S

end QAlgorithms.Papers.Independent.Gap48.P23


noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

namespace X8S

variable {n : ℕ}

lemma Lop_smul (c : Fin 2) (a : ℂ) (f : Word n 2 → ℂ) :
    Lop c (fun x => a * f x) = fun x => a * Lop c f x := by
  funext x; simp only [Lop, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

lemma Lop_zero (c : Fin 2) : Lop c (fun _ : Word n 2 => (0 : ℂ)) = fun _ => 0 := by
  funext x; simp [Lop]

lemma act_smul (p : Equiv.Perm (Fin n)) (a : ℂ) (f : Word n 2 → ℂ) :
    act p (fun x => a * f x) = fun x => a * act p f x := rfl

lemma act_zero (p : Equiv.Perm (Fin n)) : act p (fun _ : Word n 2 => (0 : ℂ)) = fun _ => 0 := rfl

lemma ip_smul_left (a : ℂ) (f g : Word n 2 → ℂ) : ip (fun x => a * f x) g = conj a * ip f g := by
  simp [ip, Finset.mul_sum, mul_assoc]

lemma ip_smul_right (a : ℂ) (f g : Word n 2 → ℂ) : ip f (fun x => a * g x) = a * ip f g := by
  simp only [ip, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => by ring

lemma ip_zero_right (f : Word n 2 → ℂ) : ip f (fun _ => 0) = 0 := by simp [ip]

lemma adjL (f g : Word n 2 → ℂ) : ip (Lop 0 f) g = ip f (Lop 1 g) := Lop_adj 0 1 (by decide) f g
lemma adjR (f g : Word n 2 → ℂ) : ip (Lop 1 f) g = ip f (Lop 0 g) := Lop_adj 1 0 (by decide) f g

lemma E_zero_of_gt (k : TwoRowShape n) (u : ℕ) (hu : degree n k < u) : E k u = fun _ => 0 := by
  funext x; unfold E
  have := wt_le k x
  rw [if_neg (by omega)]

/-- Key 1 recursion -/
lemma G_succ (k : TwoRowShape n) (p : Equiv.Perm (Fin n)) (u : ℕ) :
    ((u : ℂ) + 1) * ip (E k (u + 1)) (act p (E k (u + 1))) =
      ((degree n k - u : ℕ) : ℂ) * ip (E k u) (act p (E k u)) := by
  have h1 : ip (Lop 0 (E k u)) (act p (Lop 0 (E k u))) =
      ip (E k u) (act p (Lop 1 (Lop 0 (E k u)))) := by
    rw [adjL, Lop_act]
  rw [L0_E, act_smul, Lop_smul, L1_E_succ] at h1
  simp only [act_smul, ip_smul_left, ip_smul_right] at h1
  have hc : conj ((u : ℂ) + 1) = (u : ℂ) + 1 := by simp
  rw [hc] at h1
  have hu : (u : ℂ) + 1 ≠ 0 := by norm_cast
  have := mul_left_cancel₀ hu h1
  linear_combination this

lemma aw_sq (k : TwoRowShape n) (u : ℕ) :
    conj (aw k u) * aw k u = ((Nat.choose (degree n k) u : ℂ))⁻¹ := by
  unfold aw
  rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by positivity)]
  push_cast; rfl

lemma N_eq (k : TwoRowShape n) (p : Equiv.Perm (Fin n)) (u : ℕ) (hu : u ≤ degree n k) :
    conj (aw k u) * aw k u * ip (E k u) (act p (E k u)) =
      conj (aw k 0) * aw k 0 * ip (E k 0) (act p (E k 0)) := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [← ih (by omega), aw_sq, aw_sq]
    have hG := G_succ k p u
    have h1 := Nat.choose_succ_right_eq (degree n k) u
    have hc0 : (Nat.choose (degree n k) u : ℂ) ≠ 0 := by
      norm_cast; exact (Nat.choose_pos (by omega)).ne'
    have hc1 : (Nat.choose (degree n k) (u + 1) : ℂ) ≠ 0 := by
      norm_cast; exact (Nat.choose_pos (by omega)).ne'
    have hmu : ((degree n k - u : ℕ) : ℂ) ≠ 0 := by norm_cast; omega
    have h1' : (Nat.choose (degree n k) (u + 1) : ℂ) * ((u : ℂ) + 1) =
        (Nat.choose (degree n k) u : ℂ) * ((degree n k - u : ℕ) : ℂ) := by exact_mod_cast h1
    have hu1 : (u : ℂ) + 1 ≠ 0 := by norm_cast
    have key : (Nat.choose (degree n k) u : ℂ) * ip (E k (u + 1)) (act p (E k (u + 1))) =
        (Nat.choose (degree n k) (u + 1) : ℂ) * ip (E k u) (act p (E k u)) := by
      apply mul_left_cancel₀ hu1
      linear_combination (Nat.choose (degree n k) u : ℂ) * hG - ip (E k u) (act p (E k u)) * h1'
    field_simp
    linear_combination key

/-- Key 2: ladder orthogonality -/
lemma Z_lt (k l : TwoRowShape n) (p : Equiv.Perm (Fin n)) :
    ∀ v w : ℕ, v < w → ip (E k w) (act p (E l v)) = 0 := by
  intro v
  induction v with
  | zero =>
    intro w hw
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    have h := adjL (E k w') (act p (E l 0))
    rw [L0_E, ip_smul_left, Lop_act, L1_E_zero, act_zero, ip_zero_right] at h
    have hc : conj ((w' : ℂ) + 1) ≠ 0 := by simp; norm_cast
    exact (mul_eq_zero.mp h).resolve_left hc
  | succ v ih =>
    intro w hw
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    have h := adjR (E k (w' + 1)) (act p (E l v))
    rw [L1_E_succ, ip_smul_left, ih w' (by omega), mul_zero, Lop_act, L0_E, act_smul,
      ip_smul_right] at h
    have hc : ((v : ℂ) + 1) ≠ 0 := by norm_cast
    exact (mul_eq_zero.mp h.symm).resolve_left hc

lemma Z_ne (k l : TwoRowShape n) (p : Equiv.Perm (Fin n)) (v w : ℕ) (h : v ≠ w) :
    ip (E k w) (act p (E l v)) = 0 := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact Z_lt k l p v w h
  · rw [ip_conj, ip_act_left, Z_lt l k p⁻¹ w v h, map_zero]

lemma RL_E (k : TwoRowShape n) (w : ℕ) (hw : w ≤ degree n k) :
    Lop 1 (Lop 0 (E k w)) = fun x => (((w : ℂ) + 1) * ((degree n k : ℂ) - w)) * E k w x := by
  rw [L0_E, Lop_smul, L1_E_succ]; funext x
  rw [Nat.cast_sub hw]; ring

lemma LR_E (k : TwoRowShape n) (w : ℕ) (hw : w ≤ degree n k) :
    Lop 0 (Lop 1 (E k w)) = fun x => ((w : ℂ) * ((degree n k : ℂ) - w + 1)) * E k w x := by
  cases w with
  | zero => rw [L1_E_zero, Lop_zero]; funext x; simp
  | succ w =>
    rw [L1_E_succ, Lop_smul, L0_E]; funext x
    rw [Nat.cast_sub (by omega)]; push_cast; ring

lemma ip_RL (f g : Word n 2 → ℂ) : ip (Lop 1 (Lop 0 f)) g = ip f (Lop 1 (Lop 0 g)) := by
  rw [adjR, adjL]
lemma ip_LR (f g : Word n 2 → ℂ) : ip (Lop 0 (Lop 1 f)) g = ip f (Lop 0 (Lop 1 g)) := by
  rw [adjL, adjR]

lemma degree_inj {k l : TwoRowShape n} (h : degree n k = degree n l) : k = l := by
  have hk := k.isLt; have hl := l.isLt
  unfold degree at h
  ext; omega

/-- Key 3 -/
lemma Z_shape (k l : TwoRowShape n) (hkl : k ≠ l) (p : Equiv.Perm (Fin n)) (w : ℕ) :
    ip (E k w) (act p (E l w)) = 0 := by
  by_cases hk : w ≤ degree n k
  swap
  · rw [E_zero_of_gt k w (by omega)]; simp [ip]
  by_cases hl : w ≤ degree n l
  swap
  · rw [E_zero_of_gt l w (by omega), act_zero, ip_zero_right]
  have h1 := ip_RL (E k w) (act p (E l w))
  have h2 := ip_LR (E k w) (act p (E l w))
  rw [Lop_act, Lop_act, RL_E k w hk, RL_E l w hl, act_smul, ip_smul_left,
    ip_smul_right] at h1
  rw [Lop_act, Lop_act, LR_E k w hk, LR_E l w hl, act_smul, ip_smul_left,
    ip_smul_right] at h2
  simp only [map_mul, map_add, map_sub, map_one, map_natCast] at h1 h2
  have hne : (degree n k : ℂ) - degree n l ≠ 0 := by
    intro h; apply hkl; apply degree_inj; exact_mod_cast sub_eq_zero.mp h
  have : ((degree n k : ℂ) - degree n l) * ip (E k w) (act p (E l w)) = 0 := by
    linear_combination h1 - h2
  exact (mul_eq_zero.mp this).resolve_left hne

end X8S

end QAlgorithms.Papers.Independent.Gap48.P23


noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

namespace X8S

variable {n : ℕ}

def seedF (k : TwoRowShape n) (w : ℕ) : Word n 2 → ℂ := fun x => aw k w * E k w x

def beta (alpha : RealSchurCoefficients n) (k : TwoRowShape n) (i : Fin (schurMultiplicity n k))
    (q : Equiv.Perm (Fin n)) : ℂ :=
  if i.val = 0 then (if q = 1 then 1 else 0) else (alpha k i q : ℂ)

def vecF (alpha : RealSchurCoefficients n) (k : TwoRowShape n) (w : ℕ)
    (i : Fin (schurMultiplicity n k)) : Word n 2 → ℂ :=
  fun x => ∑ q, beta alpha k i q * act q (seedF k w) x

lemma V_eq (alpha : RealSchurCoefficients n) (k : TwoRowShape n) (w : Fin (degree n k + 1))
    (i : Fin (schurMultiplicity n k)) :
    (fun x => schurVector alpha ⟨k, (w, i)⟩ x) = vecF alpha k w.val i := by
  funext x
  have hs := seed_eq k w
  unfold vecF beta schurVector
  by_cases hi : i.val = 0
  · simp only [hi, if_true]
    rw [Finset.sum_eq_single 1 (fun q _ hq => by simp [hq]) (by simp)]
    simp only [if_true, one_mul, act_one]
    exact congrFun hs x
  · simp only [hi, if_false]
    rw [WithLp.ofLp_sum]
    simp only [Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    rw [mulVec_eq]
    unfold seedF
    rw [← hs]

lemma V_eq' (alpha : RealSchurCoefficients n) (k : TwoRowShape n) (w : Fin (degree n k + 1))
    (i : Fin (schurMultiplicity n k)) :
    WithLp.ofLp (schurVector alpha ⟨k, (w, i)⟩) = vecF alpha k w.val i := V_eq alpha k w i

lemma seed_eq' (k : TwoRowShape n) (w : Fin (degree n k + 1)) :
    WithLp.ofLp (schurSeed n k w) = fun x => aw k w.val * E k w.val x := seed_eq k w

lemma ip_sum_left {ι : Type*} [Fintype ι] (b : ι → ℂ) (F : ι → Word n 2 → ℂ) (G : Word n 2 → ℂ) :
    ip (fun x => ∑ q, b q * F q x) G = ∑ q, conj (b q) * ip (F q) G := by
  simp only [ip, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun x _ => by ring

lemma ip_sum_right {ι : Type*} [Fintype ι] (b : ι → ℂ) (F : ι → Word n 2 → ℂ) (G : Word n 2 → ℂ) :
    ip G (fun x => ∑ q, b q * F q x) = ∑ q, b q * ip G (F q) := by
  simp only [ip, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun x _ => by ring

lemma act_sum {ι : Type*} [Fintype ι] (p : Equiv.Perm (Fin n)) (b : ι → ℂ) (F : ι → Word n 2 → ℂ) :
    act p (fun x => ∑ q, b q * F q x) = fun x => ∑ q, b q * act p (F q) x := rfl

lemma expand (alpha : RealSchurCoefficients n) (k l : TwoRowShape n) (w v : ℕ)
    (i : Fin (schurMultiplicity n k)) (j : Fin (schurMultiplicity n l)) (p : Equiv.Perm (Fin n)) :
    ip (vecF alpha k w i) (act p (vecF alpha l v j)) =
      ∑ q, ∑ r, conj (beta alpha k i q) * beta alpha l j r *
        ip (seedF k w) (act (q⁻¹ * p * r) (seedF l v)) := by
  unfold vecF
  rw [act_sum, ip_sum_left]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [ip_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [ip_act_left, act_act, act_act, mul_assoc q⁻¹]
  ring

lemma seed_ip (k l : TwoRowShape n) (w v : ℕ) (p : Equiv.Perm (Fin n)) :
    ip (seedF k w) (act p (seedF l v)) = conj (aw k w) * aw l v * ip (E k w) (act p (E l v)) := by
  unfold seedF; rw [act_smul, ip_smul_left, ip_smul_right]; ring

lemma seed_zero (k l : TwoRowShape n) (w v : ℕ) (p : Equiv.Perm (Fin n)) (h : k ≠ l ∨ w ≠ v) :
    ip (seedF k w) (act p (seedF l v)) = 0 := by
  rw [seed_ip]
  by_cases hwv : w = v
  · subst hwv
    rw [Z_shape k l (h.resolve_right (not_not.mpr rfl)) p w, mul_zero]
  · rw [Z_ne k l p v w (Ne.symm hwv), mul_zero]

lemma seed_same (k : TwoRowShape n) (w : ℕ) (hw : w ≤ degree n k) (p : Equiv.Perm (Fin n)) :
    ip (seedF k w) (act p (seedF k w)) = ip (seedF k 0) (act p (seedF k 0)) := by
  rw [seed_ip, seed_ip, N_eq k p w hw]

lemma vec_zero (alpha : RealSchurCoefficients n) (k l : TwoRowShape n) (w v : ℕ)
    (i : Fin (schurMultiplicity n k)) (j : Fin (schurMultiplicity n l)) (p : Equiv.Perm (Fin n))
    (h : k ≠ l ∨ w ≠ v) : ip (vecF alpha k w i) (act p (vecF alpha l v j)) = 0 := by
  rw [expand]
  refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun r _ => ?_
  rw [seed_zero k l w v _ h, mul_zero]

lemma vec_same (alpha : RealSchurCoefficients n) (k : TwoRowShape n) (w : ℕ) (hw : w ≤ degree n k)
    (i j : Fin (schurMultiplicity n k)) (p : Equiv.Perm (Fin n)) :
    ip (vecF alpha k w i) (act p (vecF alpha k w j)) =
      ip (vecF alpha k 0 i) (act p (vecF alpha k 0 j)) := by
  rw [expand, expand]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
  rw [seed_same k w hw]

lemma inner_V (alpha : RealSchurCoefficients n) (a b : SchurIndex n) :
    inner ℂ (schurVector alpha a) (schurVector alpha b) =
      ip (vecF alpha a.1 a.2.1.val a.2.2) (act 1 (vecF alpha b.1 b.2.1.val b.2.2)) := by
  obtain ⟨k, w, i⟩ := a
  obtain ⟨l, v, j⟩ := b
  rw [inner_eq, act_one, V_eq, V_eq]

lemma inner_PV (alpha : RealSchurCoefficients n) (p : Equiv.Perm (Fin n)) (a b : SchurIndex n) :
    inner ℂ (schurVector alpha a)
      (WithLp.toLp 2 ((wordPermutationMatrix n 2 p).mulVec (schurVector alpha b))) =
      ip (vecF alpha a.1 a.2.1.val a.2.2) (act p (vecF alpha b.1 b.2.1.val b.2.2)) := by
  obtain ⟨k, w, i⟩ := a
  obtain ⟨l, v, j⟩ := b
  rw [inner_eq]
  simp only [WithLp.ofLp_toLp, V_eq', mulVec_eq]

theorem x8_seed (n : ℕ) (k : TwoRowShape n) (p : Equiv.Perm (Fin n)) (w v : Fin (degree n k + 1)) :
    inner ℂ (schurSeed n k w) (WithLp.toLp 2 ((wordPermutationMatrix n 2 p).mulVec (schurSeed n k w))) =
    inner ℂ (schurSeed n k v) (WithLp.toLp 2 ((wordPermutationMatrix n 2 p).mulVec (schurSeed n k v))) := by
  rw [inner_eq, inner_eq]
  simp only [WithLp.ofLp_toLp, seed_eq', mulVec_eq]
  have h1 := seed_same k w.val (by omega) p
  have h2 := seed_same k v.val (by omega) p
  unfold seedF at h1 h2
  rw [h1, h2]

theorem x8_fixed (n : ℕ) (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (k : TwoRowShape n) (w : Fin (degree n k + 1)) (i j : Fin (schurMultiplicity n k)) :
    inner ℂ (schurVector alpha ⟨k, (w, i)⟩) (schurVector alpha ⟨k, (w, j)⟩) =
      if i = j then 1 else 0 := by
  rw [inner_V, vec_same alpha k w.val (by omega)]
  rw [← (ha k).1 i j, inner_V]

theorem x8_blocks (n : ℕ) (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (p : Equiv.Perm (Fin n)) (a b : SchurIndex n) :
    inner ℂ (schurVector alpha a)
      (WithLp.toLp 2 ((wordPermutationMatrix n 2 p).mulVec (schurVector alpha b))) =
      if h : a.1 = b.1 then
        if a.2.1.val = b.2.1.val then permutationBlock alpha a.1 p a.2.2 (h.symm ▸ b.2.2) else 0
      else 0 := by
  rw [inner_PV]
  obtain ⟨k, w, i⟩ := a
  obtain ⟨l, v, j⟩ := b
  dsimp only
  by_cases hkl : k = l
  · subst hkl
    rw [dif_pos rfl]
    by_cases hwv : w.val = v.val
    · rw [if_pos hwv, ← hwv, vec_same alpha k w.val (by omega)]
      unfold permutationBlock
      rw [inner_PV]
    · rw [if_neg hwv, vec_zero alpha k k _ _ i j p (Or.inr hwv)]
  · rw [dif_neg hkl, vec_zero alpha k l _ _ i j p (Or.inl hkl)]

theorem x8_orth (n : ℕ) (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (a b : SchurIndex n) :
    inner ℂ (schurVector alpha a) (schurVector alpha b) = if a = b then 1 else 0 := by
  obtain ⟨k, w, i⟩ := a
  obtain ⟨l, v, j⟩ := b
  by_cases hkl : k = l
  · subst hkl
    by_cases hwv : w = v
    · subst hwv
      rw [x8_fixed n alpha ha k w i j]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg]
        intro h
        apply hij
        have := (Sigma.mk.inj_iff.mp h).2
        exact congrArg Prod.snd (eq_of_heq this)
    · rw [inner_V, vec_zero alpha k k _ _ i j 1 (Or.inr (fun e => hwv (Fin.ext e))), if_neg]
      intro h
      apply hwv
      have := (Sigma.mk.inj_iff.mp h).2
      exact congrArg Prod.fst (eq_of_heq this)
  · rw [inner_V, vec_zero alpha k l _ _ i j 1 (Or.inl hkl), if_neg]
    intro h; exact hkl (Sigma.mk.inj_iff.mp h).1

end X8S

end QAlgorithms.Papers.Independent.Gap48.P23

end

section X8Final

open QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

theorem solution (n : ℕ) (hn : 1 ≤ n)
    (k : TwoRowShape n) (p : Equiv.Perm (Fin n)) (w v : Fin (degree n k + 1)) :
    inner ℂ (schurSeed n k w) (WithLp.toLp 2 ((wordPermutationMatrix n 2 p).mulVec (schurSeed n k w))) =
    inner ℂ (schurSeed n k v) (WithLp.toLp 2 ((wordPermutationMatrix n 2 p).mulVec (schurSeed n k v))) :=
  X8S.x8_seed n k p w v

end X8Final
