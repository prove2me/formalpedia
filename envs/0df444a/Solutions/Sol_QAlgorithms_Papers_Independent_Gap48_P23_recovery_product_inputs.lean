-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.recovery_product_inputs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:22:07.14266+00:00
-- url     : https://prove2.me/submissions/8b1550c8-7b48-49f0-ad26-e03c68ce900b

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_polynomial_irrep_properties
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_dicke_matrix_action


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

/-- generic factorization of a product-operator sum -/
lemma fact {d k n : ℕ} (e : Fin d ⊕ (Fin k × Fin 2) ≃ Fin n) (M : Op (Fin 2)) (x : Fin n → Fin 2)
    (A : (Fin d → Fin 2) → ℂ) (B : (Fin 2 → Fin 2) → ℂ) :
    ∑ y : Fin n → Fin 2, (∏ i, M (x i) (y i)) *
        (A (fun i => y (e (Sum.inl i))) * ∏ j, B (fun c => y (e (Sum.inr (j, c))))) =
      (∑ a : Fin d → Fin 2, (∏ i, M (x (e (Sum.inl i))) (a i)) * A a) *
        ∏ j, ∑ b : Fin 2 → Fin 2, (∏ c, M (x (e (Sum.inr (j, c)))) (b c)) * B b := by
  rw [Finset.prod_univ_sum, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  let E : (Fin d → Fin 2) × (Fin k → Fin 2 → Fin 2) ≃ (Fin n → Fin 2) :=
    (Equiv.prodCongr (Equiv.refl _) (Equiv.curry _ _ _).symm).trans
      ((Equiv.sumArrowEquivProdArrow _ _ _).symm.trans (Equiv.arrowCongr e (Equiv.refl _)))
  have hE1 : ∀ a g i, E (a, g) (e (Sum.inl i)) = a i := by
    intro a g i; simp [E, Equiv.arrowCongr_apply]
  have hE2 : ∀ a g j c, E (a, g) (e (Sum.inr (j, c))) = g j c := by
    intro a g j c; simp [E, Equiv.arrowCongr_apply, Equiv.curry]
  symm
  refine Fintype.sum_equiv E _ _ ?_
  rintro ⟨a, g⟩
  simp only [hE1, hE2]
  rw [← e.prod_comp, Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [hE1, hE2, Finset.prod_mul_distrib]
  ring

def sgf (b : Fin 2 → Fin 2) : ℂ := sg (b 0) (b 1)

lemma singlet_act (M : Op (Fin 2)) (u : Fin 2 → Fin 2) :
    ∑ b : Fin 2 → Fin 2, (∏ c, M (u c) (b c)) * sgf b = M.det * sgf u := by
  rw [← (piFinTwoEquiv fun _ => Fin 2).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fin.prod_univ_two, sgf, piFinTwoEquiv_symm_apply,
    Fin.cons_zero, Fin.cons_one, Matrix.det_fin_two]
  have h0 : u = ![u 0, u 1] := by ext i; fin_cases i <;> rfl
  generalize u 0 = u0 at *
  generalize u 1 = u1 at *
  fin_cases u0 <;> fin_cases u1 <;> simp [sg] <;> ring


def Dk (d w : ℕ) (a : Fin d → Fin 2) : ℂ :=
  if (∑ j : Fin d, if a j = 1 then 1 else 0) = w then ((Real.sqrt (Nat.choose d w : ℝ))⁻¹ : ℂ) else 0

lemma bitIndex_eq (b : Bool) : QAlgorithms.Papers.Independent.Support21.P18.bitIndex b = finTwoEquiv.symm b := by
  cases b <;> rfl

lemma hw_eq {d : ℕ} (a : Fin d → Fin 2) :
    QAlgorithms.hammingWeight (fun i => finTwoEquiv (a i)) = ∑ j : Fin d, if a j = 1 then 1 else 0 := by
  unfold QAlgorithms.hammingWeight
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (finTwoEquiv (a j) = true) ↔ a j = 1 := by
    generalize a j = c; fin_cases c <;> simp [finTwoEquiv]
  simp only [this]

lemma dicke_act (d : ℕ) (M : Op (Fin 2)) (w : Fin (d + 1)) (x : Fin d → Fin 2) :
    ∑ a : Fin d → Fin 2, (∏ i, M (x i) (a i)) * Dk d w.val a =
      ∑ v : Fin (d + 1), polynomialIrrep d M v w * Dk d v.val x := by
  have h := congrFun (congrFun (dicke_matrix_action d M).1 (fun i => finTwoEquiv (x i))) w
  simp only [Matrix.mul_apply, QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower,
    Matrix.submatrix_apply, tensorPower, symmetricEmbedding,
    QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding, bitIndex_eq,
    Equiv.symm_apply_apply, hw_eq] at h
  rw [← (Equiv.arrowCongr (Equiv.refl (Fin d)) finTwoEquiv).sum_comp] at h
  have harr : ∀ a : Fin d → Fin 2,
      (Equiv.arrowCongr (Equiv.refl (Fin d)) finTwoEquiv) a = fun i => finTwoEquiv (a i) := fun a => rfl
  simp only [harr, Equiv.symm_apply_apply, hw_eq] at h
  unfold Dk
  convert h using 2
  ring


variable {n : ℕ}

def ixf (k : TwoRowShape n) : Fin (degree n k) ⊕ (Fin k.val × Fin 2) → Fin n
  | Sum.inl i => ⟨i.val, by have := deg_le k; omega⟩
  | Sum.inr jc => ⟨degree n k + 2 * jc.1.val + jc.2.val, by
      have := deg_le k; have := jc.1.isLt; have := jc.2.isLt; omega⟩

lemma ixf_inj (k : TwoRowShape n) : Function.Injective (ixf k) := by
  rintro (i | ⟨j, c⟩) (i' | ⟨j', c'⟩) h <;> simp only [ixf, Fin.mk.injEq] at h
  · rw [Fin.ext h]
  · omega
  · omega
  · have := c.isLt; have := c'.isLt
    have h1 : j.val = j'.val := by omega
    have h2 : c.val = c'.val := by omega
    rw [Fin.ext h1, Fin.ext h2]

def ix (k : TwoRowShape n) : Fin (degree n k) ⊕ (Fin k.val × Fin 2) ≃ Fin n :=
  Equiv.ofBijective (ixf k) ((Fintype.bijective_iff_injective_and_card _).mpr ⟨ixf_inj k, by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod]
    have := deg_le k; omega⟩)

lemma ix_inl (k : TwoRowShape n) (i : Fin (degree n k)) : (ix k (Sum.inl i)).val = i.val := rfl

lemma ix_inr (k : TwoRowShape n) (j : Fin k.val) (c : Fin 2) :
    (ix k (Sum.inr (j, c))).val = degree n k + 2 * j.val + c.val := rfl

lemma wordAt_ix (y : Word n 2) (i : Fin n) (m : ℕ) (h : i.val = m) : wordAt y m = y i := by
  subst h; exact wordAt_fin y i

lemma seedF_fact (k : TwoRowShape n) (w : ℕ) (y : Word n 2) :
    seedF k w y = Dk (degree n k) w (fun i => y (ix k (Sum.inl i))) *
      ∏ j, sgf (fun c => y (ix k (Sum.inr (j, c)))) := by
  unfold seedF E aw Dk
  have hwt : wt k y = ∑ j : Fin (degree n k), if y (ix k (Sum.inl j)) = 1 then 1 else 0 := by
    unfold wt
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [wordAt_ix y (ix k (Sum.inl j)) j.val (ix_inl k j)]
  have hS : S k y = ∏ j, sgf (fun c => y (ix k (Sum.inr (j, c)))) := by
    unfold S sgf
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [wordAt_ix y (ix k (Sum.inr (j, 0))) _ (by rw [ix_inr]; rfl),
      wordAt_ix y (ix k (Sum.inr (j, 1))) _ (by rw [ix_inr]; rfl)]
  rw [hwt, hS]
  split_ifs <;> ring

lemma T_seed (M : Op (Fin 2)) (k : TwoRowShape n) (w : Fin (degree n k + 1)) :
    (tensorPower n M).mulVec (seedF k w.val) =
      fun x => ∑ v : Fin (degree n k + 1), partitionIrrep n k M v w * seedF k v.val x := by
  funext x
  simp only [Matrix.mulVec, dotProduct, tensorPower, seedF_fact]
  rw [fact (ix k) M x (Dk (degree n k) w.val) sgf, dicke_act]
  simp only [singlet_act, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_mul, partitionIrrep, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring


lemma T_act (M : Op (Fin 2)) (p : Equiv.Perm (Fin n)) (f : Word n 2 → ℂ) :
    (tensorPower n M).mulVec (act p f) = act p ((tensorPower n M).mulVec f) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, tensorPower, act]
  let e : Word n 2 ≃ Word n 2 :=
    { toFun := fun y i => y (p i), invFun := fun z i => z (p.symm i),
      left_inv := fun z => by funext i; simp,
      right_inv := fun y => by funext i; simp }
  refine Fintype.sum_equiv e _ _ ?_
  intro z
  simp only [e, Equiv.coe_fn_mk]
  congr 1
  rw [← Equiv.prod_comp p]

lemma T_vec (M : Op (Fin 2)) (alpha : RealSchurCoefficients n) (k : TwoRowShape n)
    (w : Fin (degree n k + 1)) (i : Fin (schurMultiplicity n k)) :
    (tensorPower n M).mulVec (vecF alpha k w.val i) =
      fun x => ∑ v : Fin (degree n k + 1), partitionIrrep n k M v w * vecF alpha k v.val i x := by
  have h1 : ∀ q : Equiv.Perm (Fin n), (tensorPower n M).mulVec (act q (seedF k w.val)) =
      fun x => ∑ v : Fin (degree n k + 1), partitionIrrep n k M v w * act q (seedF k v.val) x := by
    intro q; rw [T_act, T_seed]; rfl
  funext x
  have h2 : (tensorPower n M).mulVec (vecF alpha k w.val i) x =
      ∑ q, beta alpha k i q * (tensorPower n M).mulVec (act q (seedF k w.val)) x := by
    simp only [Matrix.mulVec, dotProduct, vecF, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [h2]
  simp only [h1, vecF, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun q _ => ?_
  ring

theorem x8_action (n : ℕ) (alpha : RealSchurCoefficients n) (M : Op (Fin 2)) (b : SchurIndex n) :
    WithLp.toLp 2 ((tensorPower n M).mulVec (schurVector alpha b)) =
      ∑ w : Fin (degree n b.1 + 1), partitionIrrep n b.1 M w b.2.1 • schurVector alpha ⟨b.1, (w, b.2.2)⟩ := by
  obtain ⟨k, w0, i⟩ := b
  ext x
  rw [V_eq', T_vec]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, V_eq']


theorem x8_elem (n : ℕ) (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (M : Op (Fin 2)) (a b : SchurIndex n) :
    inner ℂ (schurVector alpha a)
      (WithLp.toLp 2 ((tensorPower n M).mulVec (schurVector alpha b))) =
      if h : a.1 = b.1 then
        if a.2.2.val = b.2.2.val then partitionIrrep n a.1 M a.2.1 (h.symm ▸ b.2.1) else 0
      else 0 := by
  rw [x8_action, inner_sum]
  simp only [inner_smul_right, x8_orth n alpha ha]
  obtain ⟨ka, wa, ia⟩ := a
  obtain ⟨kb, wb, ib⟩ := b
  by_cases h : ka = kb
  · subst h
    simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and, dif_pos, mul_ite, mul_one,
      mul_zero]
    by_cases hi : ia = ib
    · subst hi
      simp
    · have : ia.val ≠ ib.val := fun e => hi (Fin.ext e)
      simp [hi, this]
  · simp [h]

end X8S

end QAlgorithms.Papers.Independent.Gap48.P23


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

lemma tele (n m : ℕ) (hm : 2 * m ≤ n) :
    ∑ k ∈ Finset.range (m + 1), ((n : ℤ) - 2 * k + 1) *
      ((Nat.choose n k : ℤ) - if k = 0 then 0 else (Nat.choose n (k - 1) : ℤ)) =
      2 * ∑ k ∈ Finset.range m, (Nat.choose n k : ℤ) + ((n : ℤ) - 2 * m + 1) * Nat.choose n m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega), Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
    push_cast
    ring

lemma even_half (m : ℕ) :
    2 * ∑ k ∈ Finset.range m, Nat.choose (2 * m) k + Nat.choose (2 * m) m = 2 ^ (2 * m) := by
  rw [← Nat.sum_range_choose, show 2 * m + 1 = m + 1 + m by ring, Finset.sum_range_add,
    Finset.sum_range_succ]
  have : ∑ x ∈ Finset.range m, Nat.choose (2 * m) (m + 1 + x) =
      ∑ x ∈ Finset.range m, Nat.choose (2 * m) x := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx := Finset.mem_range.mp hx
    rw [← Nat.choose_symm (by omega)]
    congr 1; omega
  rw [this]; ring

lemma card_count (n : ℕ) :
    ∑ k ∈ Finset.range (n / 2 + 1), (n - 2 * k + 1) *
      (Nat.choose n k - if k = 0 then 0 else Nat.choose n (k - 1)) = 2 ^ n := by
  have hcast : ∀ k ∈ Finset.range (n / 2 + 1), (((n - 2 * k + 1) *
      (Nat.choose n k - if k = 0 then 0 else Nat.choose n (k - 1)) : ℕ) : ℤ) =
      ((n : ℤ) - 2 * k + 1) *
      ((Nat.choose n k : ℤ) - if k = 0 then 0 else (Nat.choose n (k - 1) : ℤ)) := by
    intro k hk
    have hk := Finset.mem_range.mp hk
    have h2 : 2 * k ≤ n := by omega
    by_cases h0 : k = 0
    · subst h0; simp
    · have hle : Nat.choose n (k - 1) ≤ Nat.choose n k := by
        have := Nat.choose_le_succ_of_lt_half_left (r := k - 1) (n := n) (by omega)
        rwa [Nat.sub_add_cancel (by omega)] at this
      simp only [h0, if_false]
      push_cast [hle, h2]
      ring
  have := tele n (n / 2) (by omega)
  rw [← Finset.sum_congr rfl hcast] at this
  have key : ((∑ k ∈ Finset.range (n / 2 + 1), (n - 2 * k + 1) *
      (Nat.choose n k - if k = 0 then 0 else Nat.choose n (k - 1)) : ℕ) : ℤ) = 2 ^ n := by
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have hm : 2 * m / 2 = m := by omega
      rw [hm] at this ⊢
      push_cast at this ⊢
      rw [this]
      have := even_half m
      have h' : ((2 * ∑ k ∈ Finset.range m, Nat.choose (2 * m) k + Nat.choose (2 * m) m : ℕ) : ℤ) =
          ((2 ^ (2 * m) : ℕ) : ℤ) := by rw [this]
      push_cast at h'
      linear_combination h'
    · have hm : (2 * m + 1) / 2 = m := by omega
      rw [hm] at this ⊢
      push_cast at this ⊢
      rw [this]
      have := Nat.sum_range_choose_halfway m
      rw [Finset.sum_range_succ] at this
      have h' : ((∑ x ∈ Finset.range m, Nat.choose (2 * m + 1) x + Nat.choose (2 * m + 1) m : ℕ) : ℤ) =
          ((4 ^ m : ℕ) : ℤ) := by rw [this]
      push_cast at h'
      rw [pow_succ, pow_mul]
      linear_combination 2 * h'
  exact_mod_cast key

lemma card_schur (n : ℕ) : Fintype.card (SchurIndex n) = Fintype.card (Word n 2) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  simp only [schurMultiplicity, degree]
  rw [show Fintype.card (Word n 2) = 2 ^ n by simp, ← card_count n]
  rw [Fin.sum_univ_eq_sum_range (fun k => (n - 2 * k + 1) *
      (Nat.choose n k - if k = 0 then 0 else Nat.choose n (k - 1))) (n / 2 + 1)]

end X8S

end QAlgorithms.Papers.Independent.Gap48.P23


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

lemma W_entry (alpha : RealSchurCoefficients n) (T : Op (Word n 2)) (a b : SchurIndex n) :
    (schurTransform alpha * T * (schurTransform alpha)ᴴ) a b =
      inner ℂ (schurVector alpha a) (WithLp.toLp 2 (T.mulVec (schurVector alpha b))) := by
  rw [inner_eq]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, schurTransform, ip, Matrix.mulVec,
    dotProduct, Finset.sum_mul, Finset.mul_sum, RCLike.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

lemma WWH (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) :
    schurTransform alpha * (schurTransform alpha)ᴴ = 1 := by
  ext a b
  have h := W_entry alpha 1 a b
  rw [Matrix.mul_one, Matrix.one_mulVec] at h
  rw [h, x8_orth n alpha ha, Matrix.one_apply]

lemma WHW (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) :
    (schurTransform alpha)ᴴ * schurTransform alpha = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq (card_schur n))).mp (WWH alpha ha)

lemma W_conj (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) (T rho : Op (Word n 2)) :
    schurTransform alpha * (T * rho * Tᴴ) * (schurTransform alpha)ᴴ =
      (schurTransform alpha * T * (schurTransform alpha)ᴴ) *
        (schurTransform alpha * rho * (schurTransform alpha)ᴴ) *
        (schurTransform alpha * T * (schurTransform alpha)ᴴ)ᴴ := by
  have h := WHW alpha ha
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (schurTransform alpha)ᴴ (schurTransform alpha), h, Matrix.one_mul,
    ← Matrix.mul_assoc (schurTransform alpha)ᴴ (schurTransform alpha), h, Matrix.one_mul]


abbrev MIdx (n : ℕ) := Σ k : TwoRowShape n, Fin (schurMultiplicity n k)

def phi (c : SchurIndex n) : ReducedIndex n := ⟨c.1, c.2.1⟩

def psi (c : SchurIndex n) : MIdx n := ⟨c.1, c.2.2⟩

lemma idx_inj (c d : SchurIndex n) (h1 : phi c = phi d) (h2 : psi c = psi d) : c = d := by
  obtain ⟨k, w, i⟩ := c
  obtain ⟨l, v, j⟩ := d
  simp only [phi, psi, Sigma.mk.injEq] at h1 h2
  obtain ⟨rfl, h1⟩ := h1
  obtain ⟨-, h2⟩ := h2
  rw [heq_eq_eq] at h1 h2
  subst h1; subst h2; rfl

lemma sum_S (F : SchurIndex n → ℂ) :
    ∑ c, F c = ∑ k : TwoRowShape n, ∑ w : Fin (degree n k + 1), ∑ i : Fin (schurMultiplicity n k),
      F ⟨k, (w, i)⟩ := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_prod_type]

lemma sum_single (c0 : SchurIndex n) (F : SchurIndex n → ℂ) :
    ∑ d, (if phi d = phi c0 ∧ psi d = psi c0 then F d else 0) = F c0 := by
  rw [Finset.sum_eq_single c0]
  · simp
  · intro d _ hd
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hd (idx_inj d c0 h1 h2)
  · simp

lemma pre_formula (alpha : RealSchurCoefficients n) (rho : Op (Word n 2)) (r s : ReducedIndex n) :
    preprocessing alpha rho r s =
      ∑ c, ∑ d, (if phi c = r ∧ phi d = s ∧ psi c = psi d then
        (schurTransform alpha * rho * (schurTransform alpha)ᴴ) c d else 0) := by
  obtain ⟨k, w⟩ := r
  obtain ⟨l, v⟩ := s
  unfold preprocessing
  by_cases hkl : k = l
  · subst hkl
    rw [dif_pos rfl]
    unfold preprocessingBranch
    rw [sum_S, Finset.sum_eq_single k]
    · rw [Finset.sum_eq_single w]
      · refine Finset.sum_congr rfl fun i _ => ?_
        have := sum_single (⟨k, (v, i)⟩ : SchurIndex n)
          (fun d => (schurTransform alpha * rho * (schurTransform alpha)ᴴ) ⟨k, (w, i)⟩ d)
        rw [← this]
        refine Finset.sum_congr rfl fun d _ => ?_
        by_cases hd : phi d = phi (⟨k, (v, i)⟩ : SchurIndex n) ∧ psi d = psi (⟨k, (v, i)⟩ : SchurIndex n)
        · rw [if_pos hd, if_pos ⟨rfl, hd.1, hd.2.symm⟩]
        · rw [if_neg hd, if_neg]
          rintro ⟨-, h1, h2⟩
          exact hd ⟨h1, h2.symm⟩
      · intro w' _ hw'
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun d _ => ?_
        rw [if_neg]
        rintro ⟨h1, -⟩
        simp only [phi, Sigma.mk.injEq, heq_eq_eq, true_and] at h1
        exact hw' h1
      · simp
    · intro k' _ hk'
      refine Finset.sum_eq_zero fun w' _ => Finset.sum_eq_zero fun i _ =>
        Finset.sum_eq_zero fun d _ => ?_
      rw [if_neg]
      rintro ⟨h1, -⟩
      simp only [phi, Sigma.mk.injEq] at h1
      exact hk' h1.1
    · simp
  · rw [dif_neg hkl]
    symm
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    apply hkl
    have e1 : c.1 = k := congrArg Sigma.fst h1
    have e2 : d.1 = l := congrArg Sigma.fst h2
    have e3 : c.1 = d.1 := congrArg (fun m : MIdx n => m.1) h3
    rw [← e1, ← e2, e3]


def Qm (m : MIdx n) : Matrix (ReducedIndex n) (SchurIndex n) ℂ :=
  fun r c => if phi c = r ∧ psi c = m then 1 else 0

lemma Qm_apply (m : MIdx n) (r : ReducedIndex n) (c : SchurIndex n) :
    Qm m r c = if phi c = r ∧ psi c = m then 1 else 0 := rfl

def Km (alpha : RealSchurCoefficients n) (m : MIdx n) : Matrix (ReducedIndex n) (Word n 2) ℂ :=
  Qm m * schurTransform alpha

lemma Q_sum : ∑ m : MIdx n, (Qm m)ᴴ * Qm m = 1 := by
  ext c d
  rw [Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Qm, Matrix.one_apply]
  have : ∀ (m : MIdx n) (r : ReducedIndex n),
      star (if phi c = r ∧ psi c = m then (1 : ℂ) else 0) * (if phi d = r ∧ psi d = m then 1 else 0) =
      if r = phi c then (if m = psi c then (if c = d then 1 else 0) else 0) else 0 := by
    intro m r
    by_cases h1 : m = psi c
    · by_cases h2 : r = phi c
      · subst h1 h2
        by_cases hcd : c = d
        · subst hcd; simp
        · rw [if_pos rfl, if_pos rfl, if_neg hcd, if_pos ⟨rfl, rfl⟩, if_neg, mul_zero]
          rintro ⟨e1, e2⟩
          exact hcd (idx_inj c d e1.symm e2.symm)
      · rw [if_neg h2, if_neg, star_zero, zero_mul]
        rintro ⟨e1, -⟩; exact h2 e1.symm
    · rw [ite_eq_right_iff.mpr (fun _ => if_neg h1), if_neg, star_zero, zero_mul]
      rintro ⟨-, e2⟩; exact h1 e2.symm
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma kraus_sum (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) :
    ∑ m : MIdx n, (Km alpha m)ᴴ * Km alpha m = 1 := by
  have : ∀ m : MIdx n, (Km alpha m)ᴴ * Km alpha m =
      (schurTransform alpha)ᴴ * ((Qm m)ᴴ * Qm m) * schurTransform alpha := by
    intro m
    simp only [Km, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  simp only [this]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, Q_sum, Matrix.mul_one, WHW alpha ha]

lemma kraus_apply (alpha : RealSchurCoefficients n) (rho : Op (Word n 2)) :
    ∑ m : MIdx n, Km alpha m * rho * (Km alpha m)ᴴ = preprocessing alpha rho := by
  ext r s
  rw [pre_formula, Matrix.sum_apply]
  set G := schurTransform alpha * rho * (schurTransform alpha)ᴴ with hG
  have h1 : ∀ m : MIdx n, Km alpha m * rho * (Km alpha m)ᴴ = Qm m * G * (Qm m)ᴴ := by
    intro m
    simp only [Km, hG, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  simp only [h1]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  have : ∀ (m : MIdx n) (c d : SchurIndex n), Qm m r c * G c d * star (Qm m s d) =
      if m = psi c then (if phi c = r ∧ phi d = s ∧ psi c = psi d then G c d else 0) else 0 := by
    intro m c d
    rw [Qm_apply, Qm_apply]
    by_cases h1 : m = psi c
    · subst h1
      by_cases h2 : phi c = r ∧ phi d = s ∧ psi c = psi d
      · rw [if_pos ⟨h2.1, rfl⟩, if_pos ⟨h2.2.1, h2.2.2.symm⟩, if_pos rfl, if_pos h2]; simp
      · rw [if_pos rfl, if_neg h2]
        by_cases h3 : phi c = r
        · rw [if_pos ⟨h3, rfl⟩, if_neg, star_zero, mul_zero]
          rintro ⟨e1, e2⟩; exact h2 ⟨h3, e1, e2.symm⟩
        · rw [if_neg (fun e => h3 e.1), zero_mul, zero_mul]
    · rw [if_neg h1, if_neg (fun e => h1 e.2.symm), zero_mul, zero_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]

theorem x8_channel (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) :
    IsChannel (preprocessing alpha) := by
  let e := Fintype.equivFin (MIdx n)
  refine ⟨Fintype.card (MIdx n), fun j => Km alpha (e.symm j), ?_, ?_⟩
  · unfold IsKrausFamily
    rw [← kraus_sum alpha ha]
    exact Equiv.sum_comp e.symm (fun m => (Km alpha m)ᴴ * Km alpha m)
  · intro rho
    unfold krausApply
    rw [← kraus_apply alpha rho]
    exact (Equiv.sum_comp e.symm (fun m => Km alpha m * rho * (Km alpha m)ᴴ)).symm


lemma AP_entry (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (p : Equiv.Perm (Fin n)) (k : TwoRowShape n) (w w' : Fin (degree n k + 1))
    (i j : Fin (schurMultiplicity n k)) :
    (schurTransform alpha * wordPermutationMatrix n 2 p * (schurTransform alpha)ᴴ) ⟨k, (w, i)⟩ ⟨k, (w', j)⟩ =
      if w = w' then permutationBlock alpha k p i j else 0 := by
  rw [W_entry, x8_blocks n alpha ha]
  by_cases h : w = w'
  · subst h; simp
  · have : w.val ≠ w'.val := fun e => h (Fin.ext e)
    simp [this, h]

lemma AP_off (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (p : Equiv.Perm (Fin n)) (a b : SchurIndex n) (h : a.1 ≠ b.1) :
    (schurTransform alpha * wordPermutationMatrix n 2 p * (schurTransform alpha)ᴴ) a b = 0 := by
  rw [W_entry, x8_blocks n alpha ha, dif_neg h]

lemma rowP (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (p : Equiv.Perm (Fin n)) (k : TwoRowShape n) (w : Fin (degree n k + 1))
    (i : Fin (schurMultiplicity n k)) (F : SchurIndex n → ℂ) :
    ∑ e, (schurTransform alpha * wordPermutationMatrix n 2 p * (schurTransform alpha)ᴴ) ⟨k, (w, i)⟩ e * F e =
      ∑ j, permutationBlock alpha k p i j * F ⟨k, (w, j)⟩ := by
  rw [sum_S, Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single w]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [AP_entry alpha ha, if_pos rfl]
    · intro w' _ hw'
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [AP_entry alpha ha, if_neg (Ne.symm hw'), zero_mul]
    · simp
  · intro k' _ hk'
    refine Finset.sum_eq_zero fun w' _ => Finset.sum_eq_zero fun j _ => ?_
    rw [AP_off alpha ha p _ _ (Ne.symm hk'), zero_mul]
  · simp

lemma colP (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (p : Equiv.Perm (Fin n)) (k : TwoRowShape n) (w : Fin (degree n k + 1))
    (j : Fin (schurMultiplicity n k)) (F : SchurIndex n → ℂ) :
    ∑ c, F c * (schurTransform alpha * wordPermutationMatrix n 2 p * (schurTransform alpha)ᴴ) c ⟨k, (w, j)⟩ =
      ∑ i, F ⟨k, (w, i)⟩ * permutationBlock alpha k p i j := by
  rw [sum_S, Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single w]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [AP_entry alpha ha, if_pos rfl]
    · intro w' _ hw'
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [AP_entry alpha ha, if_neg hw', mul_zero]
    · simp
  · intro k' _ hk'
    refine Finset.sum_eq_zero fun w' _ => Finset.sum_eq_zero fun i _ => ?_
    rw [AP_off alpha ha p _ _ hk', mul_zero]
  · simp

lemma perm_unitary (p : Equiv.Perm (Fin n)) :
    (wordPermutationMatrix n 2 p)ᴴ * wordPermutationMatrix n 2 p = 1 := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, wordPermutationMatrix,
    Information100.P34.permutationMatrix, Matrix.one_apply]
  have : ∀ z : Word n 2, star (if z = (Equiv.arrowCongr p (Equiv.refl (Fin 2))) x then (1:ℂ) else 0) *
      (if z = (Equiv.arrowCongr p (Equiv.refl (Fin 2))) y then 1 else 0) =
      if z = (Equiv.arrowCongr p (Equiv.refl (Fin 2))) x then (if x = y then 1 else 0) else 0 := by
    intro z
    by_cases h : z = (Equiv.arrowCongr p (Equiv.refl (Fin 2))) x
    · subst h
      by_cases hxy : x = y
      · subst hxy; simp
      · have hne : (Equiv.arrowCongr p (Equiv.refl (Fin 2))) x ≠
            (Equiv.arrowCongr p (Equiv.refl (Fin 2))) y := fun e => hxy (Equiv.injective _ e)
        simp [hne, hxy]
    · rw [if_neg h, if_neg h, star_zero, zero_mul]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma block_unitary (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (p : Equiv.Perm (Fin n)) (k : TwoRowShape n) (j j' : Fin (schurMultiplicity n k)) :
    ∑ i, star (permutationBlock alpha k p i j) * permutationBlock alpha k p i j' =
      if j = j' then 1 else 0 := by
  set A := schurTransform alpha * wordPermutationMatrix n 2 p * (schurTransform alpha)ᴴ with hA
  have hU : Aᴴ * A = 1 := by
    have h := WHW alpha ha
    have h2 := WWH alpha ha
    simp only [hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (schurTransform alpha)ᴴ (schurTransform alpha), h, Matrix.one_mul,
      ← Matrix.mul_assoc (wordPermutationMatrix n 2 p)ᴴ, perm_unitary, Matrix.one_mul, h2]
  have e := congrFun (congrFun hU ⟨k, (0, j)⟩) ⟨k, (0, j')⟩
  rw [Matrix.mul_apply] at e
  simp only [Matrix.conjTranspose_apply] at e
  rw [colP alpha ha p k 0 j' (fun c => star (A c ⟨k, (0, j)⟩))] at e
  rw [Matrix.one_apply] at e
  have e2 : ∀ i, A ⟨k, (0, i)⟩ ⟨k, (0, j)⟩ = permutationBlock alpha k p i j := by
    intro i; rw [hA, AP_entry alpha ha, if_pos rfl]
  simp only [e2] at e
  rw [e]
  by_cases h : j = j'
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro e3; apply h
    have := (Sigma.mk.inj_iff.mp e3).2
    exact congrArg Prod.snd (eq_of_heq this)


lemma rowP' (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (p : Equiv.Perm (Fin n)) (k : TwoRowShape n) (w : Fin (degree n k + 1))
    (i : Fin (schurMultiplicity n k)) (F : SchurIndex n → ℂ) :
    ∑ e, F e * star ((schurTransform alpha * wordPermutationMatrix n 2 p * (schurTransform alpha)ᴴ)
      ⟨k, (w, i)⟩ e) = ∑ j, F ⟨k, (w, j)⟩ * star (permutationBlock alpha k p i j) := by
  rw [sum_S, Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single w]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [AP_entry alpha ha, if_pos rfl]
    · intro w' _ hw'
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [AP_entry alpha ha, if_neg (Ne.symm hw'), star_zero, mul_zero]
    · simp
  · intro k' _ hk'
    refine Finset.sum_eq_zero fun w' _ => Finset.sum_eq_zero fun j _ => ?_
    rw [AP_off alpha ha p _ _ (Ne.symm hk'), star_zero, mul_zero]
  · simp

lemma unit_trace {m : ℕ} (B G : Matrix (Fin m) (Fin m) ℂ) (hB : Bᴴ * B = 1) :
    ∑ i, ∑ j', (∑ j, B i j * G j j') * star (B i j') = ∑ j, G j j := by
  have h : ∑ i, (B * G * Bᴴ) i i = ∑ j, G j j := by
    have := Matrix.trace_mul_comm (B * G) Bᴴ
    unfold Matrix.trace at this
    simp only [Matrix.diag] at this
    rw [this, ← Matrix.mul_assoc, hB, Matrix.one_mul]
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem x8_perm (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (p : Equiv.Perm (Fin n)) (rho : Op (Word n 2)) :
    preprocessing alpha (conjSuperop (wordPermutationMatrix n 2 p) rho) = preprocessing alpha rho := by
  ext ⟨k, w⟩ ⟨l, v⟩
  unfold preprocessing
  by_cases hkl : k = l
  · subst hkl
    unfold preprocessingBranch conjSuperop
    rw [W_conj alpha ha]
    set A := schurTransform alpha * wordPermutationMatrix n 2 p * (schurTransform alpha)ᴴ with hA
    set G := schurTransform alpha * rho * (schurTransform alpha)ᴴ with hG
    have step : ∀ i, (A * G * Aᴴ) ⟨k, (w, i)⟩ ⟨k, (v, i)⟩ =
        ∑ j', (∑ j, permutationBlock alpha k p i j * G ⟨k, (w, j)⟩ ⟨k, (v, j')⟩) *
          star (permutationBlock alpha k p i j') := by
      intro i
      rw [Matrix.mul_apply]
      simp only [Matrix.conjTranspose_apply, Matrix.mul_apply]
      rw [hA, rowP' alpha ha p k v i (fun f => ∑ e, A ⟨k, (w, i)⟩ e * G e f)]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [hA, rowP alpha ha p k w i]
    simp only [step]
    have hB : (Matrix.of fun i j => permutationBlock alpha k p i j)ᴴ *
        (Matrix.of fun i j => permutationBlock alpha k p i j) = 1 := by
      ext j j'
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
      exact block_unitary alpha ha p k j j'
    have := unit_trace (Matrix.of fun i j => permutationBlock alpha k p i j)
      (Matrix.of fun j j' => G ⟨k, (w, j)⟩ ⟨k, (v, j')⟩) hB
    simp only [Matrix.of_apply] at this
    exact this
  · simp only [dif_neg hkl]


lemma AU_entry (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (M : Op (Fin 2)) (k : TwoRowShape n) (w w' : Fin (degree n k + 1))
    (i j : Fin (schurMultiplicity n k)) :
    (schurTransform alpha * tensorPower n M * (schurTransform alpha)ᴴ) ⟨k, (w, i)⟩ ⟨k, (w', j)⟩ =
      if i = j then partitionIrrep n k M w w' else 0 := by
  rw [W_entry, x8_elem n alpha ha]
  by_cases h : i = j
  · subst h; simp
  · have : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp [this, h]

lemma AU_off (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (M : Op (Fin 2)) (a b : SchurIndex n) (h : a.1 ≠ b.1) :
    (schurTransform alpha * tensorPower n M * (schurTransform alpha)ᴴ) a b = 0 := by
  rw [W_entry, x8_elem n alpha ha, dif_neg h]

lemma rowU (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (M : Op (Fin 2)) (k : TwoRowShape n) (w : Fin (degree n k + 1))
    (i : Fin (schurMultiplicity n k)) (F : SchurIndex n → ℂ) :
    ∑ e, (schurTransform alpha * tensorPower n M * (schurTransform alpha)ᴴ) ⟨k, (w, i)⟩ e * F e =
      ∑ w', partitionIrrep n k M w w' * F ⟨k, (w', i)⟩ := by
  rw [sum_S, Finset.sum_eq_single k]
  · refine Finset.sum_congr rfl fun w' _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [AU_entry alpha ha, if_pos rfl]
    · intro j _ hj
      rw [AU_entry alpha ha, if_neg (Ne.symm hj), zero_mul]
    · simp
  · intro k' _ hk'
    refine Finset.sum_eq_zero fun w' _ => Finset.sum_eq_zero fun j _ => ?_
    rw [AU_off alpha ha M _ _ (Ne.symm hk'), zero_mul]
  · simp

lemma rowU' (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (M : Op (Fin 2)) (k : TwoRowShape n) (w : Fin (degree n k + 1))
    (i : Fin (schurMultiplicity n k)) (F : SchurIndex n → ℂ) :
    ∑ e, F e * star ((schurTransform alpha * tensorPower n M * (schurTransform alpha)ᴴ) ⟨k, (w, i)⟩ e) =
      ∑ w', F ⟨k, (w', i)⟩ * star (partitionIrrep n k M w w') := by
  rw [sum_S, Finset.sum_eq_single k]
  · refine Finset.sum_congr rfl fun w' _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [AU_entry alpha ha, if_pos rfl]
    · intro j _ hj
      rw [AU_entry alpha ha, if_neg (Ne.symm hj), star_zero, mul_zero]
    · simp
  · intro k' _ hk'
    refine Finset.sum_eq_zero fun w' _ => Finset.sum_eq_zero fun j _ => ?_
    rw [AU_off alpha ha M _ _ (Ne.symm hk'), star_zero, mul_zero]
  · simp

lemma R_entry (M : Op (Fin 2)) (k : TwoRowShape n) (w w' : Fin (degree n k + 1)) :
    reducedAction n M ⟨k, w⟩ ⟨k, w'⟩ = partitionIrrep n k M w w' := by
  simp [reducedAction]

lemma R_off (M : Op (Fin 2)) (a b : ReducedIndex n) (h : a.1 ≠ b.1) : reducedAction n M a b = 0 := by
  simp [reducedAction, h]

lemma rowR (M : Op (Fin 2)) (k : TwoRowShape n) (w : Fin (degree n k + 1)) (F : ReducedIndex n → ℂ) :
    ∑ r, reducedAction n M ⟨k, w⟩ r * F r = ∑ w', partitionIrrep n k M w w' * F ⟨k, w'⟩ := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp only [R_entry]
  · intro k' _ hk'
    refine Finset.sum_eq_zero fun w' _ => ?_
    rw [R_off M _ _ (Ne.symm hk'), zero_mul]
  · simp

lemma rowR' (M : Op (Fin 2)) (k : TwoRowShape n) (w : Fin (degree n k + 1)) (F : ReducedIndex n → ℂ) :
    ∑ r, F r * star (reducedAction n M ⟨k, w⟩ r) = ∑ w', F ⟨k, w'⟩ * star (partitionIrrep n k M w w') := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp only [R_entry]
  · intro k' _ hk'
    refine Finset.sum_eq_zero fun w' _ => ?_
    rw [R_off M _ _ (Ne.symm hk'), star_zero, mul_zero]
  · simp

theorem x8_cov (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (M : Op (Fin 2)) (rho : Op (Word n 2)) :
    preprocessing alpha (conjSuperop (tensorPower n M) rho) =
      conjSuperop (reducedAction n M) (preprocessing alpha rho) := by
  ext ⟨k, w⟩ ⟨l, v⟩
  unfold conjSuperop
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Matrix.mul_apply]
  rw [rowR' M l v (fun s => ∑ r, reducedAction n M ⟨k, w⟩ r * preprocessing alpha rho r s)]
  simp only [rowR M k w]
  unfold preprocessing
  by_cases hkl : k = l
  · subst hkl
    unfold preprocessingBranch
    rw [W_conj alpha ha]
    set A := schurTransform alpha * tensorPower n M * (schurTransform alpha)ᴴ with hA
    set G := schurTransform alpha * rho * (schurTransform alpha)ᴴ with hG
    have step : ∀ i, (A * G * Aᴴ) ⟨k, (w, i)⟩ ⟨k, (v, i)⟩ =
        ∑ v', (∑ w', partitionIrrep n k M w w' * G ⟨k, (w', i)⟩ ⟨k, (v', i)⟩) *
          star (partitionIrrep n k M v v') := by
      intro i
      rw [Matrix.mul_apply]
      simp only [Matrix.conjTranspose_apply, Matrix.mul_apply]
      rw [hA, rowU' alpha ha M k v i (fun f => ∑ e, A ⟨k, (w, i)⟩ e * G e f)]
      refine Finset.sum_congr rfl fun v' _ => ?_
      rw [hA, rowU alpha ha M k w i]
    simp only [step, Finset.sum_mul, dite_true, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v' _ => ?_
    rw [Finset.sum_comm]
  · simp only [dif_neg hkl, mul_zero, zero_mul, Finset.sum_const_zero]

end X8S

end QAlgorithms.Papers.Independent.Gap48.P23


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

lemma bw_sum (x : Word n 2) :
    booleanWordWeight x = ∑ i : Fin n, if x i = 1 then 1 else 0 := by
  unfold booleanWordWeight
  rw [Finset.card_filter]

lemma bw_perm (x : Word n 2) (q : Equiv.Perm (Fin n)) :
    booleanWordWeight (fun i => x (q i)) = booleanWordWeight x := by
  rw [bw_sum, bw_sum]
  exact Equiv.sum_comp q (fun i => if x i = 1 then 1 else 0)

lemma sgf_cnt (b : Fin 2 → Fin 2) (h : sgf b ≠ 0) :
    (∑ c : Fin 2, if b c = 1 then 1 else 0) = 1 := by
  rw [Fin.sum_univ_two]
  unfold sgf sg at h
  generalize b 0 = b0 at *
  generalize b 1 = b1 at *
  fin_cases b0 <;> fin_cases b1 <;> simp_all

lemma seedF_weight (k : TwoRowShape n) (w : ℕ) (y : Word n 2) (h : seedF k w y ≠ 0) :
    booleanWordWeight y = w + k.val := by
  rw [seedF_fact] at h
  have h1 : Dk (degree n k) w (fun i => y (ix k (Sum.inl i))) ≠ 0 := left_ne_zero_of_mul h
  have h2 := right_ne_zero_of_mul h
  rw [Finset.prod_ne_zero_iff] at h2
  have hD : (∑ i : Fin (degree n k), if y (ix k (Sum.inl i)) = 1 then 1 else 0) = w := by
    unfold Dk at h1
    by_contra hc
    exact h1 (if_neg hc)
  rw [bw_sum, ← (ix k).sum_comp, Fintype.sum_sum_type, Fintype.sum_prod_type, hD]
  congr 1
  calc (∑ j : Fin k.val, ∑ c : Fin 2, if y (ix k (Sum.inr (j, c))) = 1 then 1 else 0)
      = ∑ _j : Fin k.val, 1 := Finset.sum_congr rfl fun j _ =>
        sgf_cnt (fun c => y (ix k (Sum.inr (j, c)))) (h2 j (Finset.mem_univ _))
    _ = k.val := by simp

lemma vec_weight (alpha : RealSchurCoefficients n) (k : TwoRowShape n) (w : Fin (degree n k + 1))
    (i : Fin (schurMultiplicity n k)) (x : Word n 2) (h : schurVector alpha ⟨k, (w, i)⟩ x ≠ 0) :
    booleanWordWeight x = w.val + k.val := by
  have e := congrFun (V_eq alpha k w i) x
  simp only at e
  rw [e] at h
  unfold vecF at h
  obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hs := right_ne_zero_of_mul hq
  unfold act at hs
  rw [← seedF_weight k w.val _ hs, bw_perm]

lemma vec_zero_of (alpha : RealSchurCoefficients n) (k : TwoRowShape n) (w : Fin (degree n k + 1))
    (i : Fin (schurMultiplicity n k)) (x : Word n 2) (h : booleanWordWeight x ≠ w.val + k.val) :
    schurVector alpha ⟨k, (w, i)⟩ x = 0 := by
  by_contra hc
  exact h (vec_weight alpha k w i x hc)

/-- transitivity of the permutation action on a weight class -/
lemma perm_trans (x y : Word n 2) (h : booleanWordWeight x = booleanWordWeight y) :
    ∃ q : Equiv.Perm (Fin n), y = fun i => x (q i) := by
  have c1 : Fintype.card {i // y i = 1} = Fintype.card {i // x i = 1} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact h.symm
  have c2 : Fintype.card {i // ¬ y i = 1} = Fintype.card {i // ¬ x i = 1} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, c1]
  let e := Fintype.equivOfCardEq c1
  let f := Fintype.equivOfCardEq c2
  refine ⟨Equiv.subtypeCongr e f, ?_⟩
  funext i
  by_cases hi : y i = 1
  · have e1 : Equiv.subtypeCongr e f i = e ⟨i, hi⟩ := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl, hi]
    simp only [e1, hi]
    exact (e ⟨i, hi⟩).2.symm
  · have e1 : Equiv.subtypeCongr e f i = f ⟨i, hi⟩ := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl, hi]
    simp only [e1]
    have := (f ⟨i, hi⟩).2
    rw [ne1 hi, ne1 this]

lemma card_weight (h : ℕ) :
    (Finset.univ.filter (fun x : Word n 2 => booleanWordWeight x = h)).card = Nat.choose n h := by
  rw [show Nat.choose n h = (Finset.powersetCard h (Finset.univ : Finset (Fin n))).card by simp]
  refine Finset.card_nbij' (fun x => Finset.univ.filter (fun i => x i = 1))
    (fun s => fun i => if i ∈ s then 1 else 0) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hx.2⟩
  · intro s hs
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hs
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold booleanWordWeight
    rw [← hs.2]
    congr 1
    ext i
    by_cases hi : i ∈ s <;> simp [hi]
  · intro x _
    funext i
    by_cases hi : x i = 1
    · simp [hi]
    · simp [hi, ne1 hi]
  · intro s _
    ext i
    by_cases hi : i ∈ s <;> simp [hi]

end X8S

end QAlgorithms.Papers.Independent.Gap48.P23


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

lemma branch_single (alpha : RealSchurCoefficients n) (k : TwoRowShape n) (x : Word n 2)
    (w v : Fin (degree n k + 1)) :
    preprocessingBranch alpha k (Matrix.single x x 1) w v =
      ∑ i, conj (schurVector alpha ⟨k, (w, i)⟩ x) * schurVector alpha ⟨k, (v, i)⟩ x := by
  unfold preprocessingBranch
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [W_entry, inner_eq, ip]
  rw [Finset.sum_eq_single x]
  · congr 1
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · intro y _ hy
    have : ((Matrix.single x x (1 : ℂ)).mulVec (schurVector alpha ⟨k, (v, i)⟩)) y = 0 := by
      simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Ne.symm hy]
    simp only [WithLp.ofLp_toLp, this, mul_zero]
  · simp

lemma pre_branch (alpha : RealSchurCoefficients n) (k : TwoRowShape n) (rho : Op (Word n 2))
    (w v : Fin (degree n k + 1)) :
    preprocessing alpha rho ⟨k, w⟩ ⟨k, v⟩ = preprocessingBranch alpha k rho w v := by
  unfold preprocessing
  rw [dif_pos rfl]

lemma conj_perm_single (p : Equiv.Perm (Fin n)) (x : Word n 2) :
    conjSuperop (wordPermutationMatrix n 2 p) (Matrix.single x x (1 : ℂ)) =
      Matrix.single (fun i => x (p.symm i)) (fun i => x (p.symm i)) 1 := by
  ext a b
  unfold conjSuperop
  have hx : (Equiv.arrowCongr p (Equiv.refl (Fin 2))) x = fun i => x (p.symm i) := by
    funext i; simp [Equiv.arrowCongr_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single_apply, ite_and,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, ite_mul, zero_mul]
  have hP : ∀ c, wordPermutationMatrix n 2 p c x = if c = (fun i => x (p.symm i)) then 1 else 0 := by
    intro c
    unfold wordPermutationMatrix Information100.P34.permutationMatrix
    rw [hx]
  rw [hP, hP]
  by_cases h1 : a = fun i => x (p.symm i)
  · by_cases h2 : b = fun i => x (p.symm i)
    · simp [h1, h2]
    · simp [h1, h2, Ne.symm h2]
  · simp [h1, Ne.symm h1]

def Q (alpha : RealSchurCoefficients n) (k : TwoRowShape n) (w : Fin (degree n k + 1)) (x : Word n 2) : ℂ :=
  ∑ i, conj (schurVector alpha ⟨k, (w, i)⟩ x) * schurVector alpha ⟨k, (w, i)⟩ x

lemma Q_perm (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) (k : TwoRowShape n)
    (w : Fin (degree n k + 1)) (x : Word n 2) (q : Equiv.Perm (Fin n)) :
    Q alpha k w (fun i => x (q i)) = Q alpha k w x := by
  have h := congrFun (congrFun (x8_perm alpha ha q.symm (Matrix.single x x 1)) ⟨k, w⟩) ⟨k, w⟩
  rw [conj_perm_single, pre_branch, pre_branch, branch_single, branch_single] at h
  simp only [Equiv.symm_symm] at h
  exact h

lemma Q_const (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) (k : TwoRowShape n)
    (w : Fin (degree n k + 1)) (x y : Word n 2) (h : booleanWordWeight x = booleanWordWeight y) :
    Q alpha k w y = Q alpha k w x := by
  obtain ⟨q, rfl⟩ := perm_trans x y h
  exact Q_perm alpha ha k w x q

lemma Q_zero (alpha : RealSchurCoefficients n) (k : TwoRowShape n)
    (w : Fin (degree n k + 1)) (x : Word n 2) (h : booleanWordWeight x ≠ w.val + k.val) :
    Q alpha k w x = 0 := by
  unfold Q
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [vec_zero_of alpha k w i x h, mul_zero]

lemma Qsum_eq (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) (k : TwoRowShape n)
    (w : Fin (degree n k + 1)) :
    ∑ x, Q alpha k w x = (schurMultiplicity n k : ℂ) := by
  unfold Q
  rw [Finset.sum_comm]
  have : ∀ i : Fin (schurMultiplicity n k),
      ∑ x, conj (schurVector alpha ⟨k, (w, i)⟩ x) * schurVector alpha ⟨k, (w, i)⟩ x = 1 := by
    intro i
    have h := x8_fixed n alpha ha k w i i
    rw [if_pos rfl, inner_eq] at h
    exact h
  simp [this]

lemma Q_val (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) (k : TwoRowShape n)
    (w : Fin (degree n k + 1)) (x : Word n 2) (h : booleanWordWeight x = w.val + k.val) :
    Q alpha k w x = (schurMultiplicity n k : ℂ) / (Nat.choose n (booleanWordWeight x) : ℂ) := by
  have hle : booleanWordWeight x ≤ n := by
    rw [h]; have := w.isLt; have := deg_le k; omega
  have hc : (Nat.choose n (booleanWordWeight x) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hle).ne'
  rw [eq_div_iff hc, ← Qsum_eq alpha ha k w]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun y : Word n 2 => booleanWordWeight y = booleanWordWeight x)]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter
    (fun y : Word n 2 => ¬ booleanWordWeight y = booleanWordWeight x)) (fun y hy => by
    rw [Finset.mem_filter] at hy
    exact Q_zero alpha k w y (by rw [← h]; exact hy.2)), add_zero]
  have hcst : ∀ y ∈ Finset.univ.filter (fun y : Word n 2 => booleanWordWeight y = booleanWordWeight x),
      Q alpha k w y = Q alpha k w x := fun y hy => by
    rw [Finset.mem_filter] at hy
    exact Q_const alpha ha k w x y hy.2.symm
  rw [Finset.sum_congr rfl hcst, Finset.sum_const, card_weight]
  simp [mul_comm]

lemma branch_cov (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) (k : TwoRowShape n)
    (M : Op (Fin 2)) (rho : Op (Word n 2)) :
    preprocessingBranch alpha k (conjSuperop (tensorPower n M) rho) =
      conjSuperop (partitionIrrep n k M) (preprocessingBranch alpha k rho) := by
  ext w v
  have h := congrFun (congrFun (x8_cov alpha ha M rho) ⟨k, w⟩) ⟨k, v⟩
  rw [pre_branch] at h
  rw [h]
  unfold conjSuperop
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [rowR' M k v (fun s => ∑ r, reducedAction n M ⟨k, w⟩ r * preprocessing alpha rho r s)]
  simp only [rowR M k w, pre_branch]

end X8S

end QAlgorithms.Papers.Independent.Gap48.P23


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

lemma branch_off (alpha : RealSchurCoefficients n) (k : TwoRowShape n) (x : Word n 2)
    (hs : ¬ (k.val ≤ booleanWordWeight x ∧ booleanWordWeight x ≤ n - k.val)) :
    preprocessingBranch alpha k (Matrix.single x x 1) = 0 := by
  ext w v
  rw [branch_single]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [vec_zero_of alpha k w i x, map_zero, zero_mul]
  intro h
  apply hs
  have := w.isLt; have := deg_le k
  unfold degree at *
  omega

lemma branch_on (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) (k : TwoRowShape n)
    (x : Word n 2) (j : Fin (degree n k + 1)) (hj : j.val + k.val = booleanWordWeight x) :
    preprocessingBranch alpha k (Matrix.single x x 1) =
      ((schurMultiplicity n k : ℂ) / (Nat.choose n (booleanWordWeight x) : ℂ)) • Matrix.single j j 1 := by
  ext w v
  rw [branch_single]
  by_cases hw : w = j
  · by_cases hv : v = j
    · subst hw; subst hv
      have := Q_val alpha ha k v x hj.symm
      unfold Q at this
      rw [this]
      simp
    · rw [Matrix.smul_apply, Matrix.single_apply, if_neg (fun h => hv h.2.symm), smul_zero]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [vec_zero_of alpha k v i x, mul_zero]
      intro h; apply hv; apply Fin.ext; omega
  · rw [Matrix.smul_apply, Matrix.single_apply, if_neg (fun h => hw h.1.symm), smul_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [vec_zero_of alpha k w i x, map_zero, zero_mul]
    intro h; apply hw; apply Fin.ext; omega

lemma det_unit (U : Matrix.unitaryGroup (Fin 2) ℂ) : star (U.val.det) * U.val.det = 1 := by
  rw [← Matrix.det_conjTranspose, ← Matrix.det_mul]
  have : U.valᴴ * U.val = 1 := Unitary.star_mul_self_of_mem U.2
  rw [this, Matrix.det_one]

lemma pi_unit (k : TwoRowShape n) (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    (partitionIrrep n k U.val)ᴴ * partitionIrrep n k U.val = 1 := by
  unfold partitionIrrep
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ((polynomial_irrep_properties (degree n k)).2.2.2.2.2.2.1 U).1, star_pow, ← mul_pow,
    det_unit U, one_pow, one_smul]

lemma mult_cast (k : TwoRowShape n) :
    (schurMultiplicity n k : ℂ) =
      ((((Nat.choose n k.val : ℝ) - (if k.val = 0 then 0 else (Nat.choose n (k.val - 1) : ℝ))) : ℝ) : ℂ) := by
  unfold schurMultiplicity
  by_cases hk : k.val = 0
  · simp [hk]
  · rw [if_neg hk, if_neg hk]
    have hle : Nat.choose n (k.val - 1) ≤ Nat.choose n k.val := by
      have h1 := Nat.choose_le_succ_of_lt_half_left (r := k.val - 1) (n := n)
        (by have := k.isLt; omega)
      rwa [Nat.sub_add_cancel (by omega)] at h1
    push_cast [hle]
    ring

theorem x8_ppo (n : ℕ) (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (x : Word n 2) (U : Matrix.unitaryGroup (Fin 2) ℂ) (k : TwoRowShape n) :
    (preprocessingBranch alpha k (encodedInput U.val x)).trace =
        samplingProbability n (booleanWordWeight x) k ∧
      preprocessingBranch alpha k (encodedInput U.val x) =
        predictedBranch n k (booleanWordWeight x) U.val := by
  unfold encodedInput
  rw [branch_cov alpha ha k U.val]
  by_cases hs : k.val ≤ booleanWordWeight x ∧ booleanWordWeight x ≤ n - k.val
  · have hvalid : booleanWordWeight x - k.val < degree n k + 1 := by
      unfold degree; omega
    set j : Fin (degree n k + 1) := ⟨booleanWordWeight x - k.val, hvalid⟩ with hjdef
    rw [branch_on alpha ha k x j (by simp only [hjdef]; omega)]
    have hsp : ((samplingProbability n (booleanWordWeight x) k : ℝ) : ℂ) =
        (schurMultiplicity n k : ℂ) / (Nat.choose n (booleanWordWeight x) : ℂ) := by
      unfold samplingProbability
      rw [if_pos hs, mult_cast]
      push_cast
      ring
    have hconj : ∀ (c : ℂ) (A : Op (Fin (degree n k + 1))),
        conjSuperop (partitionIrrep n k U.val) (c • A) =
          c • conjSuperop (partitionIrrep n k U.val) A := by
      intro c A
      unfold conjSuperop
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [hconj]
    constructor
    · rw [Matrix.trace_smul, hsp]
      unfold conjSuperop
      rw [Matrix.trace_mul_cycle, pi_unit, Matrix.one_mul, Matrix.trace_single_eq_same, smul_eq_mul,
        mul_one]
    · unfold predictedBranch
      rw [dif_pos hs, dif_pos hvalid, hsp]
  · rw [branch_off alpha k x hs]
    have h0 : conjSuperop (partitionIrrep n k U.val) (0 : Op (Fin (degree n k + 1))) = 0 := by
      unfold conjSuperop; simp
    rw [h0]
    unfold samplingProbability predictedBranch
    rw [if_neg hs, dif_neg hs]
    simp

end X8S

end QAlgorithms.Papers.Independent.Gap48.P23


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

lemma mult_pos (k : TwoRowShape n) : 0 < schurMultiplicity n k := by
  unfold schurMultiplicity
  by_cases hk : k.val = 0
  · rw [if_pos hk, hk]; simp
  · rw [if_neg hk]
    have hkn : k.val ≤ n / 2 := by have := k.isLt; omega
    have e : k.val - 1 + 1 = k.val := by omega
    have hp : 0 < Nat.choose n (k.val - 1) := Nat.choose_pos (by omega)
    -- C(n,k) * k = C(n,k-1) * (n - (k-1))
    have h3 : Nat.choose n k.val * k.val = Nat.choose n (k.val - 1) * (n - (k.val - 1)) := by
      have := Nat.choose_succ_right_eq n (k.val - 1)
      rw [e] at this
      exact this
    have h4 : Nat.choose n (k.val - 1) * k.val < Nat.choose n (k.val - 1) * (n - (k.val - 1)) :=
      Nat.mul_lt_mul_of_pos_left (by omega) hp
    have h5 : Nat.choose n (k.val - 1) < Nat.choose n k.val := by
      by_contra hc
      push_neg at hc
      have := Nat.mul_le_mul_right k.val hc
      omega
    omega

/-- the block matrix used by schurRecovery -/
def Blk (rho : Op (ReducedIndex n)) : Op (SchurIndex n) :=
  Matrix.of fun (a b : SchurIndex n) => if h : a.1 = b.1 then
      if a.2.2.val = b.2.2.val then rho ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩ /
        (schurMultiplicity n a.1 : ℂ) else 0 else 0

lemma rec_eq (alpha : RealSchurCoefficients n) (rho : Op (ReducedIndex n)) :
    schurRecovery alpha rho = (schurTransform alpha)ᴴ * Blk rho * schurTransform alpha := rfl

lemma Blk_entry (rho : Op (ReducedIndex n)) (k l : TwoRowShape n) (w : Fin (degree n k + 1))
    (v : Fin (degree n l + 1)) (i : Fin (schurMultiplicity n k)) (j : Fin (schurMultiplicity n l)) :
    Blk rho ⟨k, (w, i)⟩ ⟨l, (v, j)⟩ =
      if k = l ∧ i.val = j.val then rho ⟨k, w⟩ ⟨l, v⟩ / (schurMultiplicity n k : ℂ) else 0 := by
  unfold Blk
  simp only [Matrix.of_apply]
  by_cases hkl : k = l
  · rw [dif_pos hkl]
    by_cases hij : i.val = j.val
    · rw [if_pos hij, if_pos ⟨hkl, hij⟩]
    · rw [if_neg hij, if_neg (fun h => hij h.2)]
  · rw [dif_neg hkl, if_neg (fun h => hkl h.1)]

def cm (k : TwoRowShape n) : ℂ := ((Real.sqrt (schurMultiplicity n k : ℝ))⁻¹ : ℝ)

lemma cm_sq (k : TwoRowShape n) : star (cm k) * cm k = ((schurMultiplicity n k : ℂ))⁻¹ := by
  unfold cm
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (Nat.cast_nonneg _)]
  push_cast; rfl

lemma cm_sq' (k : TwoRowShape n) : cm k * star (cm k) = ((schurMultiplicity n k : ℂ))⁻¹ := by
  rw [mul_comm, cm_sq]

def Jm (alpha : RealSchurCoefficients n) (m : MIdx n) : Matrix (Word n 2) (ReducedIndex n) ℂ :=
  cm m.1 • ((schurTransform alpha)ᴴ * (Qm m)ᴴ)

lemma sum_phi (r : ReducedIndex n) (F : SchurIndex n → ℂ) :
    ∑ c, (if phi c = r then F c else 0) = ∑ i : Fin (schurMultiplicity n r.1), F ⟨r.1, (r.2, i)⟩ := by
  obtain ⟨k, w⟩ := r
  rw [sum_S, Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single w]
    · refine Finset.sum_congr rfl fun i _ => ?_
      exact if_pos rfl
    · intro w' _ hw'
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      intro h
      simp only [phi, Sigma.mk.injEq, heq_eq_eq, true_and] at h
      exact hw' h
    · simp
  · intro k' _ hk'
    refine Finset.sum_eq_zero fun w' _ => Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    intro h
    simp only [phi, Sigma.mk.injEq] at h
    exact hk' h.1
  · simp

lemma QQ_sum : ∑ m : MIdx n, ((schurMultiplicity n m.1 : ℂ))⁻¹ • (Qm m * (Qm m)ᴴ) = 1 := by
  ext r s
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Qm_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ (c : SchurIndex n) (m : MIdx n),
      ((schurMultiplicity n m.1 : ℂ))⁻¹ * ((if phi c = r ∧ psi c = m then (1 : ℂ) else 0) *
        star (if phi c = s ∧ psi c = m then (1 : ℂ) else 0)) =
      if m = psi c then (if phi c = r then (if r = s then ((schurMultiplicity n c.1 : ℂ))⁻¹ else 0)
        else 0) else 0 := by
    intro c m
    by_cases hm : m = psi c
    · subst hm
      by_cases h1 : phi c = r
      · by_cases h2 : r = s
        · subst h1 h2; simp; rfl
        · simp [h1, h2]
      · simp [h1]
    · have hm' : ¬ psi c = m := fun h => hm h.symm
      simp [hm, hm']
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [sum_phi]
  by_cases hrs : r = s
  · subst hrs
    simp only [if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Matrix.one_apply_eq]
    have := mult_pos r.1
    field_simp
  · simp [hrs, Matrix.one_apply_ne hrs]

lemma rkraus_sum (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) :
    ∑ m : MIdx n, (Jm alpha m)ᴴ * Jm alpha m = 1 := by
  have : ∀ m : MIdx n, (Jm alpha m)ᴴ * Jm alpha m =
      ((schurMultiplicity n m.1 : ℂ))⁻¹ • (Qm m * (Qm m)ᴴ) := by
    intro m
    unfold Jm
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, cm_sq]
    congr 1
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (schurTransform alpha), WWH alpha ha, Matrix.one_mul]
  simp only [this]
  exact QQ_sum

lemma QrQ (m : MIdx n) (rho : Op (ReducedIndex n)) (c d : SchurIndex n) :
    ((Qm m)ᴴ * rho * Qm m) c d = if psi c = m ∧ psi d = m then rho (phi c) (phi d) else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (phi d)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (phi c)]
    · simp only [Matrix.conjTranspose_apply, Qm_apply]
      by_cases h1 : psi c = m
      · by_cases h2 : psi d = m
        · simp [h1, h2]
        · simp [h2]
      · simp [h1]
    · intro r _ hr
      simp only [Matrix.conjTranspose_apply, Qm_apply]
      have : ¬ (phi c = r ∧ psi c = m) := fun h => hr h.1.symm
      simp [this]
    · simp
  · intro s _ hs
    simp only [Qm_apply]
    have : ¬ (phi d = s ∧ psi d = m) := fun h => hs h.1.symm
    simp [this]
  · simp

lemma Blk_kraus (rho : Op (ReducedIndex n)) :
    ∑ m : MIdx n, ((schurMultiplicity n m.1 : ℂ))⁻¹ • ((Qm m)ᴴ * rho * Qm m) = Blk rho := by
  ext c d
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, QrQ, smul_eq_mul]
  rw [Finset.sum_eq_single (psi c)]
  · obtain ⟨k, w, i⟩ := c
    obtain ⟨l, v, j⟩ := d
    rw [Blk_entry]
    by_cases hkl : k = l
    · subst hkl
      by_cases hij : i = j
      · subst hij
        rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, div_eq_mul_inv, mul_comm]
        rfl
      · rw [if_neg, if_neg (fun h => hij (Fin.ext h.2)), mul_zero]
        intro h
        have := h.2
        simp only [psi, Sigma.mk.injEq, heq_eq_eq, true_and] at this
        exact hij this.symm
    · rw [if_neg, if_neg (fun h => hkl h.1), mul_zero]
      intro h
      have := h.2
      simp only [psi, Sigma.mk.injEq] at this
      exact hkl this.1.symm
  · intro m _ hm
    rw [if_neg (fun h => hm h.1.symm), mul_zero]
  · simp

lemma rkraus_apply (alpha : RealSchurCoefficients n) (rho : Op (ReducedIndex n)) :
    ∑ m : MIdx n, Jm alpha m * rho * (Jm alpha m)ᴴ = schurRecovery alpha rho := by
  rw [rec_eq, ← Blk_kraus, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold Jm
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, cm_sq',
    Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem x8_rchannel (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) :
    IsChannel (schurRecovery alpha) := by
  let e := Fintype.equivFin (MIdx n)
  refine ⟨Fintype.card (MIdx n), fun j => Jm alpha (e.symm j), ?_, ?_⟩
  · unfold IsKrausFamily
    rw [← rkraus_sum alpha ha]
    exact Equiv.sum_comp e.symm (fun m => (Jm alpha m)ᴴ * Jm alpha m)
  · intro rho
    unfold krausApply
    rw [← rkraus_apply alpha rho]
    exact (Equiv.sum_comp e.symm (fun m => Jm alpha m * rho * (Jm alpha m)ᴴ)).symm


lemma RR_entry (M : Op (Fin 2)) (rho : Op (ReducedIndex n)) (k l : TwoRowShape n)
    (w : Fin (degree n k + 1)) (v : Fin (degree n l + 1)) :
    conjSuperop (reducedAction n M) rho ⟨k, w⟩ ⟨l, v⟩ =
      ∑ v', (∑ w', partitionIrrep n k M w w' * rho ⟨k, w'⟩ ⟨l, v'⟩) * star (partitionIrrep n l M v v') := by
  unfold conjSuperop
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Matrix.mul_apply]
  rw [rowR' M l v (fun s => ∑ r, reducedAction n M ⟨k, w⟩ r * rho r s)]
  simp only [rowR M k w]

lemma Blk_cov (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (M : Op (Fin 2)) (rho : Op (ReducedIndex n)) :
    Blk (conjSuperop (reducedAction n M) rho) =
      (schurTransform alpha * tensorPower n M * (schurTransform alpha)ᴴ) * Blk rho *
        (schurTransform alpha * tensorPower n M * (schurTransform alpha)ᴴ)ᴴ := by
  set A := schurTransform alpha * tensorPower n M * (schurTransform alpha)ᴴ with hA
  ext ⟨k, w, i⟩ ⟨l, v, j⟩
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Matrix.mul_apply]
  rw [hA, rowU' alpha ha M l v j (fun f => ∑ e, A ⟨k, (w, i)⟩ e * Blk rho e f)]
  simp only [hA, rowU alpha ha M k w i, Blk_entry, RR_entry]
  by_cases h : k = l ∧ i.val = j.val
  · simp only [if_pos h, Finset.sum_div]
    refine Finset.sum_congr rfl fun v' _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun w' _ => ?_
    ring
  · simp [if_neg h]

theorem x8_rcov (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (M : Op (Fin 2)) (rho : Op (ReducedIndex n)) :
    schurRecovery alpha (conjSuperop (reducedAction n M) rho) =
      conjSuperop (tensorPower n M) (schurRecovery alpha rho) := by
  rw [rec_eq, rec_eq, Blk_cov alpha ha]
  unfold conjSuperop
  have h := WHW alpha ha
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (schurTransform alpha)ᴴ (schurTransform alpha), h, Matrix.one_mul]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_one]

lemma PT_comm (M : Op (Fin 2)) (p : Equiv.Perm (Fin n)) :
    wordPermutationMatrix n 2 p * tensorPower n M = tensorPower n M * wordPermutationMatrix n 2 p := by
  rw [Matrix.ext_iff_mulVec]
  intro f
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulVec_eq, mulVec_eq, T_act]

lemma conj_lin {I J : Type*} [Fintype I] [Fintype J] (A : Matrix J I ℂ) (c : ℂ)
    {ι : Type*} (s : Finset ι) (X : ι → Matrix I I ℂ) :
    conjSuperop A (c • ∑ p ∈ s, X p) = c • ∑ p ∈ s, conjSuperop A (X p) := by
  unfold conjSuperop
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]

lemma tw_cov (M : Op (Fin 2)) (rho : Op (Word n 2)) :
    permutationTwirl n (conjSuperop (tensorPower n M) rho) =
      conjSuperop (tensorPower n M) (permutationTwirl n rho) := by
  have key : ∀ p : Equiv.Perm (Fin n),
      conjSuperop (wordPermutationMatrix n 2 p) (conjSuperop (tensorPower n M) rho) =
        conjSuperop (tensorPower n M) (conjSuperop (wordPermutationMatrix n 2 p) rho) := by
    intro p
    have h1 := PT_comm M p
    have h2 : (tensorPower n M)ᴴ * (wordPermutationMatrix n 2 p)ᴴ =
        (wordPermutationMatrix n 2 p)ᴴ * (tensorPower n M)ᴴ := by
      rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, h1]
    unfold conjSuperop
    calc wordPermutationMatrix n 2 p * (tensorPower n M * rho * (tensorPower n M)ᴴ) *
          (wordPermutationMatrix n 2 p)ᴴ
        = (wordPermutationMatrix n 2 p * tensorPower n M) * rho *
            ((tensorPower n M)ᴴ * (wordPermutationMatrix n 2 p)ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = (tensorPower n M * wordPermutationMatrix n 2 p) * rho *
            ((wordPermutationMatrix n 2 p)ᴴ * (tensorPower n M)ᴴ) := by rw [h1, h2]
      _ = tensorPower n M * (wordPermutationMatrix n 2 p * rho * (wordPermutationMatrix n 2 p)ᴴ) *
            (tensorPower n M)ᴴ := by simp only [Matrix.mul_assoc]
  unfold permutationTwirl
  rw [conj_lin]
  simp only [key]

lemma pre_lin (alpha : RealSchurCoefficients n) (c : ℂ) {ι : Type*} (s : Finset ι)
    (X : ι → Op (Word n 2)) :
    preprocessing alpha (c • ∑ p ∈ s, X p) = c • ∑ p ∈ s, preprocessing alpha (X p) := by
  rw [← kraus_apply]
  simp only [← kraus_apply]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
  simp only [← Finset.smul_sum]
  rw [Finset.sum_comm]

lemma pre_tw (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) (rho : Op (Word n 2)) :
    preprocessing alpha (permutationTwirl n rho) = preprocessing alpha rho := by
  unfold permutationTwirl
  rw [pre_lin]
  simp only [x8_perm alpha ha, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, one_div, inv_mul_cancel₀ this, one_smul]

end X8S

end QAlgorithms.Papers.Independent.Gap48.P23


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

/-- averaging over a weight class -/
lemma avg (f : Word n 2 → ℂ) (h : ℕ) (hz : ∀ y, booleanWordWeight y ≠ h → f y = 0)
    (hp : ∀ y (q : Equiv.Perm (Fin n)), f (fun i => y (q i)) = f y) (y : Word n 2)
    (hy : booleanWordWeight y = h) : f y * (Nat.choose n h : ℂ) = ∑ z, f z := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun z : Word n 2 => booleanWordWeight z = h)]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter (fun z : Word n 2 => ¬ booleanWordWeight z = h))
    (fun z hz' => hz z (Finset.mem_filter.mp hz').2), add_zero]
  have hcst : ∀ z ∈ Finset.univ.filter (fun z : Word n 2 => booleanWordWeight z = h), f z = f y := by
    intro z hz'
    obtain ⟨q, rfl⟩ := perm_trans y z (by rw [hy, (Finset.mem_filter.mp hz').2])
    exact hp y q
  rw [Finset.sum_congr rfl hcst, Finset.sum_const, card_weight]
  simp [mul_comm]

def sx (p : Equiv.Perm (Fin n)) (x : Word n 2) : Word n 2 := fun i => x (p.symm i)

lemma sx_iff (p q : Equiv.Perm (Fin n)) (x y : Word n 2) :
    sx p x = (fun i => y (q i)) ↔ sx (q * p) x = y := by
  unfold sx
  constructor
  · intro h
    funext j
    have := congrFun h (q.symm j)
    simp only [Equiv.apply_symm_apply] at this
    rw [← this]
    simp [Equiv.Perm.mul_def]
  · intro h
    funext i
    rw [← h]
    simp [Equiv.Perm.mul_def]

def Nc (x y : Word n 2) : ℂ := ∑ p : Equiv.Perm (Fin n), if sx p x = y then 1 else 0

lemma Nc_perm (x y : Word n 2) (q : Equiv.Perm (Fin n)) : Nc x (fun i => y (q i)) = Nc x y := by
  unfold Nc
  simp only [sx_iff]
  exact Equiv.sum_comp (Equiv.mulLeft q) (fun p => if sx p x = y then (1 : ℂ) else 0)

lemma Nc_zero (x y : Word n 2) (h : booleanWordWeight y ≠ booleanWordWeight x) : Nc x y = 0 := by
  unfold Nc
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [if_neg]
  intro e
  apply h
  rw [← e]
  exact bw_perm x p.symm

lemma Nc_sum (x : Word n 2) : ∑ y, Nc x y = (Nat.factorial n : ℂ) := by
  unfold Nc
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq, Fintype.card_perm]

lemma Nc_val (x y : Word n 2) (hy : booleanWordWeight y = booleanWordWeight x) :
    Nc x y * (Nat.choose n (booleanWordWeight x) : ℂ) = (Nat.factorial n : ℂ) := by
  rw [← Nc_sum x]
  exact avg (Nc x) _ (fun z hz => Nc_zero x z hz) (fun z q => Nc_perm x z q) y hy

lemma choose_ne (x : Word n 2) : (Nat.choose n (booleanWordWeight x) : ℂ) ≠ 0 := by
  have : booleanWordWeight x ≤ n := by
    unfold booleanWordWeight
    exact (Finset.card_le_univ _).trans (by simp)
  exact_mod_cast (Nat.choose_pos this).ne'

lemma tw_single (x : Word n 2) :
    permutationTwirl n (Matrix.single x x 1) = Matrix.of fun y z =>
      if y = z ∧ booleanWordWeight y = booleanWordWeight x then
        ((Nat.choose n (booleanWordWeight x) : ℂ))⁻¹ else 0 := by
  ext y z
  unfold permutationTwirl
  simp only [conj_perm_single, Matrix.smul_apply, Matrix.sum_apply, Matrix.single_apply,
    Matrix.of_apply, smul_eq_mul]
  have hf : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  by_cases hyz : y = z
  · subst hyz
    have e : (∑ p : Equiv.Perm (Fin n),
        if (fun i => x (p.symm i)) = y ∧ (fun i => x (p.symm i)) = y then (1 : ℂ) else 0) = Nc x y := by
      unfold Nc sx
      simp only [and_self]
    rw [e]
    by_cases hw : booleanWordWeight y = booleanWordWeight x
    · rw [if_pos ⟨rfl, hw⟩]
      have := Nc_val x y hw
      have hc := choose_ne x
      field_simp
      rw [this]
    · rw [if_neg (fun h => hw h.2), Nc_zero x y hw, mul_zero]
  · rw [if_neg (fun h => hyz h.1), Finset.sum_eq_zero, mul_zero]
    intro p _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hyz (h1.symm.trans h2)


lemma pre_single_entry (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) (x : Word n 2)
    (k : TwoRowShape n) (w v : Fin (degree n k + 1)) :
    preprocessing alpha (Matrix.single x x 1) ⟨k, w⟩ ⟨k, v⟩ =
      if w = v ∧ w.val + k.val = booleanWordWeight x then
        (schurMultiplicity n k : ℂ) / (Nat.choose n (booleanWordWeight x) : ℂ) else 0 := by
  rw [pre_branch]
  by_cases hs : k.val ≤ booleanWordWeight x ∧ booleanWordWeight x ≤ n - k.val
  · have hvalid : booleanWordWeight x - k.val < degree n k + 1 := by
      unfold degree; omega
    rw [branch_on alpha ha k x ⟨booleanWordWeight x - k.val, hvalid⟩ (by simp only; omega)]
    rw [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases h1 : w = v ∧ w.val + k.val = booleanWordWeight x
    · rw [if_pos h1, if_pos ⟨Fin.ext (by simp only; omega), Fin.ext (by rw [← h1.1]; simp only; omega)⟩,
        mul_one]
    · rw [if_neg h1, if_neg, mul_zero]
      rintro ⟨e1, e2⟩
      apply h1
      have a1 := congrArg Fin.val e1
      have a2 := congrArg Fin.val e2
      simp only at a1 a2
      exact ⟨Fin.ext (by omega), by omega⟩
  · rw [branch_off alpha k x hs, Matrix.zero_apply, if_neg]
    rintro ⟨-, h2⟩
    apply hs
    have := w.isLt; have := deg_le k
    unfold degree at *
    omega

lemma sig_eq (k : TwoRowShape n) (w v : Fin (degree n k + 1)) (i j : Fin (schurMultiplicity n k)) :
    ((⟨k, (w, i)⟩ : SchurIndex n) = ⟨k, (v, j)⟩) ↔ (w = v ∧ i = j) := by
  constructor
  · intro h
    have := (Sigma.mk.inj_iff.mp h).2
    rw [heq_eq_eq, Prod.mk.injEq] at this
    exact this
  · rintro ⟨rfl, rfl⟩; rfl

lemma Blk_pre (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) (x : Word n 2) :
    Blk (preprocessing alpha (Matrix.single x x 1)) = Matrix.of fun a b =>
      if a = b ∧ a.2.1.val + a.1.val = booleanWordWeight x then
        ((Nat.choose n (booleanWordWeight x) : ℂ))⁻¹ else 0 := by
  ext ⟨k, w, i⟩ ⟨l, v, j⟩
  rw [Blk_entry, Matrix.of_apply]
  by_cases hkl : k = l
  · subst hkl
    rw [pre_single_entry alpha ha x]
    simp only [sig_eq]
    have hm : (schurMultiplicity n k : ℂ) ≠ 0 := by exact_mod_cast (mult_pos k).ne'
    by_cases hij : i = j
    · subst hij
      by_cases hwv : w = v
      · subst hwv
        by_cases h2 : w.val + k.val = booleanWordWeight x
        · simp [h2]
          field_simp
        · simp [h2]
      · simp [hwv]
    · have hij' : ¬ i.val = j.val := fun e => hij (Fin.ext e)
      simp [hij, hij']
  · rw [if_neg (fun e => hkl e.1), if_neg]
    rintro ⟨e, -⟩
    exact hkl (Sigma.mk.inj_iff.mp e).1

lemma base (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) (x : Word n 2) :
    schurRecovery alpha (preprocessing alpha (Matrix.single x x 1)) =
      permutationTwirl n (Matrix.single x x 1) := by
  rw [rec_eq, Blk_pre alpha ha, tw_single]
  ext y z
  set C := ((Nat.choose n (booleanWordWeight x) : ℂ))⁻¹ with hC
  set h := booleanWordWeight x with hh
  rw [Matrix.mul_apply]
  have row : ∀ b : SchurIndex n,
      ∑ a, (schurTransform alpha)ᴴ y a *
        (Matrix.of fun a b : SchurIndex n => if a = b ∧ a.2.1.val + a.1.val = h then C else 0) a b =
      schurVector alpha b y * (if b.2.1.val + b.1.val = h then C else 0) := by
    intro b
    rw [Finset.sum_eq_single b]
    · simp [Matrix.conjTranspose_apply, schurTransform]
    · intro a _ hab
      simp [hab]
    · simp
  simp only [Matrix.mul_apply, row]
  have hW := congrFun (congrFun (WHW alpha ha) y) z
  rw [Matrix.mul_apply] at hW
  simp only [Matrix.conjTranspose_apply, schurTransform, RCLike.star_def, Complex.conj_conj,
    Matrix.one_apply] at hW
  rw [Matrix.of_apply]
  by_cases hy : booleanWordWeight y = h
  · have e : ∀ b : SchurIndex n,
        schurVector alpha b y * (if b.2.1.val + b.1.val = h then C else 0) *
          schurTransform alpha b z =
        C * (schurVector alpha b y * conj (schurVector alpha b z)) := by
      rintro ⟨k, w, i⟩
      by_cases hb : w.val + k.val = h
      · simp only [hb, if_true, schurTransform]; ring
      · rw [vec_zero_of alpha k w i y (by rw [hy]; exact Ne.symm hb)]
        simp
    simp only [e, ← Finset.mul_sum, hW]
    by_cases hyz : y = z
    · rw [if_pos hyz, if_pos ⟨hyz, hy⟩, mul_one]
    · rw [if_neg hyz, if_neg (fun e => hyz e.1), mul_zero]
  · rw [if_neg (fun e => hy e.2)]
    refine Finset.sum_eq_zero ?_
    rintro ⟨k, w, i⟩ _
    by_cases hb : w.val + k.val = h
    · rw [vec_zero_of alpha k w i y (by rw [← hb] at hy; exact hy)]
      simp
    · simp [hb]

theorem x8_rpi (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) (x : Word n 2)
    (U : Op (Fin 2)) :
    schurRecovery alpha (preprocessing alpha (permutationTwirl n (encodedInput U x))) =
      permutationTwirl n (encodedInput U x) := by
  unfold encodedInput
  rw [tw_cov, x8_cov alpha ha, x8_rcov alpha ha, pre_tw alpha ha, base alpha ha]

end X8S

end QAlgorithms.Papers.Independent.Gap48.P23

end

section X8Final

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

theorem solution (n : ℕ) (hn : 1 ≤ n)
    (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) :
    IsChannel (schurRecovery alpha) ∧
    (∀ (U : Matrix.unitaryGroup (Fin 2) ℂ) rho,
      schurRecovery alpha (conjSuperop (reducedAction n U.val) rho) =
        conjSuperop (tensorPower n U.val) (schurRecovery alpha rho)) ∧
    (∀ (x : Word n 2) (U : Matrix.unitaryGroup (Fin 2) ℂ),
      schurRecovery alpha (preprocessing alpha (permutationTwirl n (encodedInput U.val x))) =
        permutationTwirl n (encodedInput U.val x)) :=
  ⟨X8S.x8_rchannel alpha ha, fun U rho => X8S.x8_rcov alpha ha U.val rho,
    fun x U => X8S.x8_rpi alpha ha x U.val⟩

end X8Final
