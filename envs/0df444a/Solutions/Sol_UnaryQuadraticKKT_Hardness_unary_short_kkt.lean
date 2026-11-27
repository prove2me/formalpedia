-- Prove2me | solution 1 for UnaryQuadraticKKT.Hardness.unary_short_kkt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:54:38.931152+00:00
-- url     : https://prove2.me/submissions/3520fe4c-d655-4379-99eb-21969c8051a7

import Mathlib
import Definitions.Def_LinearChoresCLS_EpsKKT
import Theorems.Thm_MIQPInNP_SmallSol_theorem_3
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_UnaryQuadraticKKT_Hardness_Input

set_option autoImplicit false

open Finset

namespace LinearChoresCLS.QPMem
open MIQPInNP.SmallSol NetworkEquilibriumCLS.LinearNash

theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem bitSize_neg (q : ℚ) : bitSize (-q) = bitSize q := by
  simp [bitSize]

theorem bitSize_zero : bitSize 0 = 2 := by simp [bitSize]
theorem bitSize_one : bitSize 1 = 3 := by simp [bitSize]

theorem two_le_bitSize (q : ℚ) : 2 ≤ bitSize q := by
  unfold bitSize
  have : 1 ≤ Nat.size q.den := by
    rw [Nat.one_le_iff_ne_zero, Ne, Nat.size_eq_zero]; exact q.den_ne_zero
  omega

theorem bitSize_div_le (x y : ℚ) : bitSize (x / y) ≤ bitSize x + bitSize y := by
  by_cases hy : y = 0
  · subst hy; simp only [div_zero, bitSize_zero]; have := two_le_bitSize x; omega
  have hyn : y.num ≠ 0 := Rat.num_ne_zero.2 hy
  have hrep : x / y = Rat.divInt (x.num * y.den) (x.den * y.num) := by
    rw [Rat.divInt_eq_div]; push_cast
    conv_lhs => rw [← Rat.num_div_den x, ← Rat.num_div_den y]
    have : (y.num : ℚ) ≠ 0 := by exact_mod_cast hyn
    have : (y.den : ℚ) ≠ 0 := by exact_mod_cast y.den_ne_zero
    have : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
    field_simp
  have hden0 : (x.den : ℤ) * y.num ≠ 0 := mul_ne_zero (by exact_mod_cast x.den_ne_zero) hyn
  have hnum := Rat.num_dvd (x.num * y.den) hden0
  have hden := Rat.den_dvd (x.num * y.den) (x.den * y.num)
  rw [← hrep] at hnum hden
  -- numerators
  have h1 : (x / y).num.natAbs ≤ x.num.natAbs * y.den := by
    by_cases hx : x.num * y.den = 0
    · have : x = 0 := by
        rcases mul_eq_zero.1 hx with h | h
        · exact Rat.num_eq_zero.1 h
        · exact absurd h (by exact_mod_cast y.den_ne_zero)
      subst this; simp
    · have := Int.natAbs_le_of_dvd_ne_zero hnum hx
      simpa [Int.natAbs_mul] using this
  have h2 : (x / y).den ≤ x.den * y.num.natAbs := by
    have := Int.natAbs_le_of_dvd_ne_zero hden hden0
    simpa [Int.natAbs_mul] using this
  unfold bitSize
  have e1 := Nat.size_le_size h1
  have e2 := Nat.size_le_size h2
  have e3 := size_mul_le x.num.natAbs y.den
  have e4 := size_mul_le x.den y.num.natAbs
  omega

theorem len_lnNat (n : ℕ) : (NetworkEquilibriumCLS.LinearNash.encNat n).length = 2 * Nat.size n + 1 := by
  simp [NetworkEquilibriumCLS.LinearNash.encNat, Nat.size_eq_bits_len]; omega

theorem len_lnRat (q : ℚ) : (NetworkEquilibriumCLS.LinearNash.encRat q).length = 2 * bitSize q + 1 := by
  simp [NetworkEquilibriumCLS.LinearNash.encRat, NetworkEquilibriumCLS.LinearNash.encInt, len_lnNat,
    bitSize]; omega

theorem size_le_self' (n : ℕ) : Nat.size n ≤ n := by
  rw [Nat.size_le]; exact Nat.lt_two_pow_self

theorem poly_eval_mono (g : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : g.eval x ≤ g.eval y := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i))

theorem le_vecSize {n : ℕ} (v : Fin n → ℚ) (i : Fin n) : bitSize (v i) ≤ vecSize v := by
  unfold vecSize
  have := Finset.single_le_sum (f := fun i => bitSize (v i)) (fun _ _ => Nat.zero_le _) (mem_univ i)
  omega

theorem poly_bound (h : Polynomial ℕ) : ∃ k : ℕ, ∀ s : ℕ, h.eval s ≤ (s + 1) ^ k + k := by
  refine ⟨h.natDegree + h.eval 1, fun s => ?_⟩
  have h1 : h.eval s ≤ h.eval 1 * (s + 1) ^ h.natDegree := by
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    simp only [one_pow, mul_one]
    have hi' : i ≤ h.natDegree := by simpa [Nat.lt_succ_iff] using hi
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.le_succ s) i).trans
      (Nat.pow_le_pow_right (Nat.succ_pos s) hi'))
  have h2 : h.eval 1 ≤ (s + 1) ^ h.eval 1 + h.eval 1 := Nat.le_add_left _ _
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simp at h1 ⊢; omega
  · have h3 : h.eval 1 ≤ (s + 1) ^ h.eval 1 :=
      (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by omega) _)
    calc h.eval s ≤ h.eval 1 * (s + 1) ^ h.natDegree := h1
      _ ≤ (s + 1) ^ h.eval 1 * (s + 1) ^ h.natDegree := Nat.mul_le_mul_right _ h3
      _ = (s + 1) ^ (h.natDegree + h.eval 1) := by rw [← pow_add, Nat.add_comm (h.eval 1)]
      _ ≤ _ := Nat.le_add_right _ _

theorem len_flatMap_ge {α : Type} (f : α → List Bool) (l : List α) (x : α) (hx : x ∈ l) :
    (f x).length ≤ (l.flatMap f).length := by
  rw [List.length_flatMap]
  exact List.le_sum_of_mem (List.mem_map.2 ⟨x, hx, rfl⟩)

theorem len_lnList {α : Type} (f : α → List Bool) (l : List α) :
    (encList f l).length = 2 * Nat.size l.length + 1 + (l.map (fun x => (f x).length)).sum := by
  simp [encList, len_lnNat, List.length_flatMap]

theorem len_encVector_le {n : ℕ} (v : Fin n → ℚ) (K : ℕ) (hK : ∀ j, bitSize (v j) ≤ K) :
    (encVector v).length ≤ 2 * n + 1 + n * (2 * K + 1) := by
  unfold encVector
  rw [len_lnList]
  simp only [List.length_ofFn, List.map_ofFn, List.sum_ofFn, Function.comp_def, len_lnRat]
  have h1 := size_le_self' n
  have h2 : ∑ j, (2 * bitSize (v j) + 1) ≤ ∑ _j : Fin n, (2 * K + 1) :=
    Finset.sum_le_sum (fun j _ => by have := hK j; omega)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  omega

end LinearChoresCLS.QPMem


open Finset

namespace LinearChoresCLS.QPMem
open NetworkEquilibriumCLS.LinearNash

variable {n : ℕ}

theorem dsum_expand (Q : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    ∑ k, ∑ l, Q k l * (x k + if k = i then t else 0) * (x l + if l = i then t else 0) =
      ∑ k, ∑ l, Q k l * x k * x l + t * ∑ l, Q i l * x l + t * ∑ k, Q k i * x k + t ^ 2 * Q i i := by
  have h : ∀ k l, Q k l * (x k + if k = i then t else 0) * (x l + if l = i then t else 0) =
      Q k l * x k * x l + (if k = i then t * (Q k l * x l) else 0) +
        (if l = i then t * (Q k l * x k) else 0) +
        (if k = i then (if l = i then t ^ 2 * Q k l else 0) else 0) := by
    intro k l
    split_ifs <;> ring
  have e1 : ∑ k, ∑ l, (if k = i then t * (Q k l * x l) else 0) = t * ∑ l, Q i l * x l := by
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
    simp [Finset.mul_sum]
  have e2 : ∑ k, ∑ l, (if l = i then t * (Q k l * x k) else 0) = t * ∑ k, Q k i * x k := by
    simp [Finset.mul_sum]
  have e3 : ∑ k, ∑ l, (if k = i then (if l = i then t ^ 2 * Q k l else 0) else 0) = t ^ 2 * Q i i := by
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
    simp
  rw [Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => h k l))]
  simp only [Finset.sum_add_distrib]
  rw [e1, e2, e3]

end LinearChoresCLS.QPMem

namespace LinearChoresCLS.QPMem
open NetworkEquilibriumCLS.LinearNash

variable {n : ℕ}

theorem quad_step (P : Quadratic n) (x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    quadraticValue P (fun k => x k + if k = i then t else 0) =
      quadraticValue P x + t * sourceGradient P x i + t ^ 2 * (P.Q i i : ℝ) / 2 := by
  unfold quadraticValue sourceGradient
  rw [dsum_expand (fun k l => (P.Q k l : ℝ)) x i t]
  have hsym : ∑ k, (P.Q k i : ℝ) * x k = ∑ k, (P.Q i k : ℝ) * x k :=
    Finset.sum_congr rfl (fun k _ => by rw [P.symmetric k i])
  rw [hsym]
  have hc : ∑ k, (P.c k : ℝ) * (x k + if k = i then t else 0) = ∑ k, (P.c k : ℝ) * x k + t * P.c i := by
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring
  rw [hc]; ring

theorem grad_nonpos (P : Quadratic n) (x : Fin n → ℝ) (hx : InCube x)
    (hmax : ∀ y, InCube y → quadraticValue P y ≤ quadraticValue P x) (i : Fin n) (hi : x i < 1) :
    sourceGradient P x i ≤ 0 := by
  by_contra hG; push Not at hG
  set G := sourceGradient P x i
  set q := (P.Q i i : ℝ)
  set t := min (1 - x i) (G / (|q| + 1)) with ht
  have htpos : 0 < t := lt_min (by linarith) (div_pos hG (by positivity))
  have ht1 : t ≤ 1 - x i := min_le_left _ _
  have ht2 : t ≤ G / (|q| + 1) := min_le_right _ _
  have hy : InCube (fun k => x k + if k = i then t else 0) := by
    intro k
    by_cases hk : k = i
    · subst hk; simp only [if_true]; constructor <;> linarith [(hx k).1]
    · simp only [hk, if_false, add_zero]; exact hx k
  have := hmax _ hy
  rw [quad_step] at this
  have h3 : t * (|q| + 1) ≤ G := by rwa [le_div_iff₀ (by positivity)] at ht2
  have h4 : -(t * |q|) ≤ t * q := by
    have := neg_abs_le q; nlinarith
  nlinarith [abs_nonneg q]

theorem grad_nonneg (P : Quadratic n) (x : Fin n → ℝ) (hx : InCube x)
    (hmax : ∀ y, InCube y → quadraticValue P y ≤ quadraticValue P x) (i : Fin n) (hi : 0 < x i) :
    0 ≤ sourceGradient P x i := by
  by_contra hG; push Not at hG
  set G := sourceGradient P x i
  set q := (P.Q i i : ℝ)
  set t := min (x i) ((-G) / (|q| + 1)) with ht
  have htpos : 0 < t := lt_min hi (div_pos (by linarith) (by positivity))
  have ht1 : t ≤ x i := min_le_left _ _
  have ht2 : t ≤ (-G) / (|q| + 1) := min_le_right _ _
  have hy : InCube (fun k => x k + if k = i then -t else 0) := by
    intro k
    by_cases hk : k = i
    · subst hk; simp only [if_true]; constructor <;> linarith [(hx k).2]
    · simp only [hk, if_false, add_zero]; exact hx k
  have := hmax _ hy
  rw [quad_step] at this
  have h3 : t * (|q| + 1) ≤ -G := by rwa [le_div_iff₀ (by positivity)] at ht2
  have h4 : -(t * |q|) ≤ t * q := by
    have := neg_abs_le q; nlinarith
  nlinarith [abs_nonneg q]

theorem kkt_of_max (P : Quadratic n) (x : Fin n → ℝ) (hx : InCube x)
    (hmax : ∀ y, InCube y → quadraticValue P y ≤ quadraticValue P x) (ε : ℝ) (hε : 0 ≤ ε) :
    LinearChoresCLS.IsEpsKKT P ε x := by
  refine ⟨hx, fun i => ⟨fun h0 => ?_, fun h1 h2 => ?_, fun h3 => ?_⟩⟩
  · have := grad_nonpos P x hx hmax i (by rw [h0]; norm_num); linarith
  · have a := grad_nonpos P x hx hmax i h2
    have b := grad_nonneg P x hx hmax i h1
    rw [abs_le]; constructor <;> linarith
  · have := grad_nonneg P x hx hmax i (by rw [h3]; norm_num); linarith

end LinearChoresCLS.QPMem


open Finset

namespace LinearChoresCLS.QPMem
open MIQPInNP.SmallSol NetworkEquilibriumCLS.LinearNash

variable {n : ℕ}

def boxA (n : ℕ) : Matrix (Fin (n + n)) (Fin n) ℚ := fun r j =>
  if r.val < n then (if j.val = r.val then 1 else 0) else (if j.val + n = r.val then -1 else 0)
def boxB (n : ℕ) : Fin (n + n) → ℚ := fun r => if r.val < n then 1 else 0

theorem mem_box (y : Fin n → ℝ) : y ∈ polyhedron (boxA n) (boxB n) ↔ InCube y := by
  unfold polyhedron boxA boxB InCube
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h i
    have h1 := h ⟨i.val, by omega⟩
    have h2 := h ⟨i.val + n, by omega⟩
    simp only [i.isLt, if_true, show ¬ (i.val + n < n) by omega, if_false] at h1 h2
    have e1 : ∑ j : Fin n, ((if j.val = i.val then (1 : ℚ) else 0 : ℚ) : ℝ) * y j = y i := by
      rw [Finset.sum_eq_single i (fun b _ hb => by simp [Fin.val_ne_of_ne hb]) (by simp)]; simp
    have e2 : ∑ j : Fin n, ((if j.val + n = i.val + n then (-1 : ℚ) else 0 : ℚ) : ℝ) * y j = -y i := by
      rw [Finset.sum_eq_single i (fun b _ hb => by
        simp only [add_left_inj]; simp; left; exact fun h => hb (Fin.ext h)) (by simp)]; simp
    rw [e1] at h1; rw [e2] at h2
    simp at h1 h2
    exact ⟨by linarith, h1⟩
  · intro h r
    by_cases hr : r.val < n
    · simp only [hr, if_true]
      rw [Finset.sum_eq_single ⟨r.val, hr⟩ (fun b _ hb => by
        simp [show b.val ≠ r.val from fun h => hb (Fin.ext h)]) (by simp)]
      simpa using (h ⟨r.val, hr⟩).2
    · simp only [hr, if_false]
      rw [Finset.sum_eq_single ⟨r.val - n, by omega⟩ (fun b _ hb => by
        simp; left; intro h; exact hb (Fin.ext (by simp; omega))) (by simp)]
      simp only [show r.val - n + n = r.val by omega, if_true]
      simpa using (h ⟨r.val - n, by omega⟩).1

def negH (P : Quadratic n) : Matrix (Fin n) (Fin n) ℚ := fun i j => -(P.Q i j) / 2
def negC (P : Quadratic n) : Fin n → ℚ := fun i => -(P.c i)

theorem quadVal_neg (P : Quadratic n) (y : Fin n → ℝ) :
    quadVal (negH P) (negC P) 0 y = -quadraticValue P y := by
  unfold quadVal quadForm negH negC quadraticValue
  have h1 : ∑ i, ∑ j, y i * (((-(P.Q i j) / 2 : ℚ)) : ℝ) * y j =
      -((∑ i, ∑ j, (P.Q i j : ℝ) * y i * y j) / 2) := by
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    push_cast; ring
  have h2 : ∑ i, (((-(P.c i)) : ℚ) : ℝ) * y i = -∑ i, (P.c i : ℝ) * y i := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    push_cast; ring
  rw [h1, h2]; push_cast; ring

theorem exists_small_kkt :
    ∃ g : Polynomial ℕ, ∀ (n : ℕ) (P : Quadratic n), ∃ x : Fin n → ℚ,
      (∀ ε : ℝ, 0 ≤ ε → LinearChoresCLS.IsEpsKKT P ε (fun i => (x i : ℝ))) ∧
      vecSize x ≤ g.eval (instSize (negH P) (negC P) 0 (boxA n) (boxB n)) := by
  obtain ⟨g, -, hg⟩ := MIQPInNP.SmallSol.theorem_3
  refine ⟨g, fun n P => ?_⟩
  have hcube : IsCompact (polyhedron (boxA n) (boxB n)) := by
    have : polyhedron (boxA n) (boxB n) = Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
      ext y; rw [mem_box]; simp only [InCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    rw [this]; exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have hne : (polyhedron (boxA n) (boxB n)).Nonempty :=
    ⟨fun _ => 0, (mem_box _).2 (fun _ => ⟨le_rfl, zero_le_one⟩)⟩
  have hcont : ContinuousOn (fun y => quadVal (negH P) (negC P) 0 y) (polyhedron (boxA n) (boxB n)) := by
    unfold quadVal quadForm
    fun_prop
  obtain ⟨x0, hx0, hmin⟩ := hcube.exists_isMinOn hne hcont
  obtain ⟨xh, hxh, hopt, hsz⟩ := hg n (n + n) (negH P) (negC P) 0 (boxA n) (boxB n)
    ⟨x0, hx0, fun y hy => hmin hy⟩
  refine ⟨xh, fun ε hε => ?_, hsz⟩
  have hin : InCube (fun i => (xh i : ℝ)) := (mem_box _).1 hxh
  refine kkt_of_max P _ hin (fun y hy => ?_) ε hε
  have := hopt y ((mem_box y).2 hy)
  rw [quadVal_neg, quadVal_neg] at this
  have e : toReal xh = fun i => (xh i : ℝ) := rfl
  rw [e] at this; linarith

end LinearChoresCLS.QPMem

namespace LinearChoresCLS.QPMem
open MIQPInNP.SmallSol NetworkEquilibriumCLS.LinearNash Polynomial

variable {n : ℕ}

def IBq (n T : ℕ) : ℕ :=
  n * n + n * n * (T + 4) + (n + n * T) + 2 + ((n + n) * n + (n + n) * n * 3) + ((n + n) + (n + n) * 3)

theorem bitSize_two : bitSize 2 = 4 := by
  simp [bitSize]; decide

theorem instSize_q_le (P : Quadratic n) (T : ℕ) (hQ : ∀ i j, bitSize (P.Q i j) ≤ T)
    (hc : ∀ i, bitSize (P.c i) ≤ T) :
    instSize (negH P) (negC P) 0 (boxA n) (boxB n) ≤ IBq n T := by
  unfold instSize matSize vecSize IBq
  have hH : ∑ i, ∑ j, bitSize (negH P i j) ≤ n * n * (T + 4) := by
    calc ∑ i, ∑ j, bitSize (negH P i j) ≤ ∑ _i : Fin n, ∑ _j : Fin n, (T + 4) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => by
            unfold negH
            have := bitSize_div_le (-(P.Q i j)) 2
            rw [bitSize_neg, bitSize_two] at this
            have := hQ i j; omega))
      _ = n * n * (T + 4) := by simp [Finset.sum_const]; ring
  have hC : ∑ i, bitSize (negC P i) ≤ n * T := by
    calc ∑ i, bitSize (negC P i) ≤ ∑ _i : Fin n, T :=
          Finset.sum_le_sum (fun i _ => by unfold negC; rw [bitSize_neg]; exact hc i)
      _ = n * T := by simp
  have hA : ∑ r, ∑ j, bitSize (boxA n r j) ≤ (n + n) * n * 3 := by
    calc ∑ r, ∑ j, bitSize (boxA n r j) ≤ ∑ _r : Fin (n + n), ∑ _j : Fin n, 3 :=
          Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun j _ => by
            unfold boxA; split_ifs <;> simp [bitSize_neg, bitSize_one, bitSize_zero]))
      _ = (n + n) * n * 3 := by simp [Finset.sum_const]; ring
  have hB : ∑ r, bitSize (boxB n r) ≤ (n + n) * 3 := by
    calc ∑ r, bitSize (boxB n r) ≤ ∑ _r : Fin (n + n), 3 :=
          Finset.sum_le_sum (fun r _ => by
            unfold boxB; split_ifs <;> simp [bitSize_one, bitSize_zero])
      _ = (n + n) * 3 := by simp
  rw [bitSize_zero]
  omega

end LinearChoresCLS.QPMem

namespace LinearChoresCLS.QPMem
open MIQPInNP.SmallSol NetworkEquilibriumCLS.LinearNash Polynomial

theorem IBq_mono {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') : IBq a b ≤ IBq a' b' := by
  unfold IBq; gcongr

noncomputable def IBqpoly : Polynomial ℕ :=
  X * X + X * X * (X + 4) + (X + X * X) + 2 + ((X + X) * X + (X + X) * X * 3) + ((X + X) + (X + X) * 3)

theorem IBqpoly_eval (s : ℕ) : IBqpoly.eval s = IBq s s := by
  simp [IBqpoly, IBq]

theorem qdata_le {n : ℕ} (P : Quadratic n) (ε : ℚ) :
    (∀ i j, bitSize (P.Q i j) ≤ (encQuadratic P ++ encRat ε).length) ∧
    (∀ i, bitSize (P.c i) ≤ (encQuadratic P ++ encRat ε).length) ∧
    n ≤ (encQuadratic P ++ encRat ε).length := by
  have hlen : ∀ q : ℚ, bitSize q ≤ (encRat q).length := fun q => by rw [len_lnRat]; omega
  have hvec : ∀ {m : ℕ} (v : Fin m → ℚ) (j : Fin m), bitSize (v j) ≤ (encVector v).length := by
    intro m v j
    unfold encVector encList
    simp only [List.length_append]
    have := len_flatMap_ge encRat (List.ofFn v) (v j) (List.mem_ofFn.2 ⟨j, rfl⟩)
    have := hlen (v j); omega
  have hvecn : ∀ {m : ℕ} (v : Fin m → ℚ), m ≤ (encVector v).length := by
    intro m v
    unfold encVector
    rw [len_lnList]
    simp only [List.length_ofFn, List.map_ofFn, List.sum_ofFn, Function.comp_def, len_lnRat]
    have : ∑ _j : Fin m, 1 ≤ ∑ j, (2 * bitSize (v j) + 1) := Finset.sum_le_sum (fun j _ => by omega)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
    omega
  have hparts : (encList (encList encRat) (List.ofFn fun i => List.ofFn (P.Q i))).length ≤
      (encQuadratic P ++ encRat ε).length ∧ (encVector P.c).length ≤ (encQuadratic P ++ encRat ε).length := by
    unfold encQuadratic; simp only [List.length_append]; omega
  refine ⟨fun i j => ?_, fun i => (hvec P.c i).trans hparts.2, (hvecn P.c).trans hparts.2⟩
  refine le_trans ?_ hparts.1
  have hc : (List.flatMap (encList encRat) (List.ofFn fun i => List.ofFn (P.Q i))).length ≤
      (encList (encList encRat) (List.ofFn fun i => List.ofFn (P.Q i))).length := by
    show _ ≤ (encNat _ ++ _).length
    simp
  have h1 := len_flatMap_ge (encList encRat) (List.ofFn fun i => List.ofFn (P.Q i))
    (List.ofFn (P.Q i)) (List.mem_ofFn.2 ⟨i, rfl⟩)
  have h2 := hvec (P.Q i) j
  unfold encVector at h2
  omega

theorem short_rational_kkt : ∃ k : ℕ, TotalSearch (bounded LinearChoresCLS.epsQKKTSearch k) := by
  obtain ⟨g, hg⟩ := exists_small_kkt
  set h : Polynomial ℕ := 2 * X + 1 + X * (2 * g.comp IBqpoly + 1) with hh
  obtain ⟨k, hk⟩ := poly_bound h
  refine ⟨k, fun x hx => ?_⟩
  obtain ⟨n, hn, P, ε, hε, rfl⟩ := hx
  set s := (encQuadratic P ++ encRat ε).length with hs
  obtain ⟨hQ, hc, hns⟩ := qdata_le P ε
  obtain ⟨xh, hkkt, hsz⟩ := hg n P
  refine ⟨encVector xh, ⟨n, hn, P, ε, hε, rfl, xh, rfl, hkkt ε (by exact_mod_cast hε.le)⟩, ?_⟩
  have hV : vecSize xh ≤ g.eval (IBq s s) :=
    hsz.trans (poly_eval_mono g ((instSize_q_le P s hQ hc).trans (IBq_mono hns le_rfl)))
  have hl := len_encVector_le xh (vecSize xh) (fun j => le_vecSize xh j)
  have heval : h.eval s = 2 * s + 1 + s * (2 * g.eval (IBq s s) + 1) := by
    simp [hh, Polynomial.eval_comp, IBqpoly_eval]
  have hb : (encVector xh).length ≤ h.eval s := by
    rw [heval]
    have : n * (2 * vecSize xh + 1) ≤ s * (2 * g.eval (IBq s s) + 1) :=
      Nat.mul_le_mul hns (by omega)
    omega
  exact hb.trans (hk s)

end LinearChoresCLS.QPMem



namespace UQS
open MIQPInNP.SmallSol NetworkEquilibriumCLS.LinearNash UnaryQuadraticKKT.Hardness LinearChoresCLS.QPMem Polynomial

def negP {n : ℕ} (p : Quadratic n) : Quadratic n :=
  ⟨fun i j => -p.Q i j, fun i => -p.c i, fun i j => by rw [p.symmetric]⟩

theorem kkt_of_eps {n : ℕ} (p : Quadratic n) (x : Fin n → ℝ) (h : LinearChoresCLS.IsEpsKKT (negP p) 0 x) :
    QuadraticKKT p x := by
  obtain ⟨hcube, hs⟩ := h
  have hg : ∀ i, sourceGradient (negP p) x i = -sourceGradient p x i := by
    intro i; unfold sourceGradient negP; simp [Finset.sum_neg_distrib]; ring
  refine ⟨hcube, fun i => ⟨fun hpos => ?_, fun hlt => ?_⟩⟩
  · obtain ⟨-, h2, h3⟩ := hs i
    rw [hg] at h2 h3
    by_cases h1 : x i < 1
    · have := h2 hpos h1; rw [abs_neg] at this; exact (abs_le.mp this).2
    · have : x i = 1 := le_antisymm (hcube i).2 (not_lt.mp h1)
      have := h3 this; linarith
  · obtain ⟨h1, h2, -⟩ := hs i
    rw [hg] at h1 h2
    by_cases h0 : 0 < x i
    · have := h2 h0 hlt; rw [abs_neg] at this; have := (abs_le.mp this).1; linarith
    · have : x i = 0 := le_antisymm (not_lt.mp h0) (hcube i).1
      have := h1 this; linarith

theorem bitSize_le_unaryRat (q : ℚ) : bitSize q ≤ (unaryRat q).length := by
  unfold bitSize unaryRat unaryNat
  simp only [List.length_cons, List.length_append, List.length_replicate, List.length_nil]
  have h1 := size_le_self' q.num.natAbs
  have h2 := size_le_self' q.den
  omega

end UQS

namespace UQS
open MIQPInNP.SmallSol NetworkEquilibriumCLS.LinearNash UnaryQuadraticKKT.Hardness LinearChoresCLS.QPMem Polynomial

theorem mem_slots_q {n : ℕ} (a b : Fin n) (hab : a ≤ b) : Monomial.quadratic a b ∈ slots n := by
  unfold slots
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq]
  left; exact ⟨a, b, hab, rfl⟩

theorem mem_slots_l {n : ℕ} (i : Fin n) : Monomial.linear i ∈ slots n := by
  unfold slots; simp

theorem slot_len_le {n : ℕ} (p : Quadratic n) (t : Monomial n) (ht : t ∈ slots n) :
    (unaryRat (coefficient p t)).length ≤ (unaryCode p).length := by
  unfold unaryCode
  rw [List.length_append, List.length_flatMap]
  have := List.le_sum_of_mem (List.mem_map.mpr ⟨t, ht, rfl⟩ :
    (unaryRat (coefficient p t)).length ∈ (slots n).map fun t => (unaryRat (coefficient p t)).length)
  omega

theorem bitSize_two_mul (q : ℚ) : bitSize (2 * q) ≤ bitSize q + 4 := by
  have h := bitSize_div_le q (1 / 2)
  have e : q / (1 / 2) = 2 * q := by ring
  rw [e] at h
  have : bitSize (1 / 2 : ℚ) = 4 := by simp [bitSize]; decide
  omega

theorem udata {n : ℕ} (p : Quadratic n) :
    n ≤ (unaryCode p).length ∧ (∀ i j, bitSize ((negP p).Q i j) ≤ (unaryCode p).length + 4) ∧
      (∀ i, bitSize ((negP p).c i) ≤ (unaryCode p).length + 4) := by
  refine ⟨?_, fun i j => ?_, fun i => ?_⟩
  · unfold unaryCode unaryNat; simp
  · simp only [negP]; rw [bitSize_neg]
    rcases lt_trichotomy i j with h | h | h
    · have := slot_len_le p _ (mem_slots_q i j h.le)
      have h2 := bitSize_le_unaryRat (coefficient p (Monomial.quadratic i j))
      simp only [coefficient, Fin.ne_of_lt h, if_false] at h2 this
      omega
    · subst h
      have := slot_len_le p _ (mem_slots_q i i le_rfl)
      have h2 := bitSize_le_unaryRat (coefficient p (Monomial.quadratic i i))
      have h3 := bitSize_two_mul (coefficient p (Monomial.quadratic i i))
      simp only [coefficient, if_true] at h2 h3 this
      have e : 2 * (p.Q i i / 2) = p.Q i i := by ring
      rw [e] at h3
      omega
    · have := slot_len_le p _ (mem_slots_q j i h.le)
      have h2 := bitSize_le_unaryRat (coefficient p (Monomial.quadratic j i))
      simp only [coefficient, Fin.ne_of_lt h, if_false] at h2 this
      rw [p.symmetric]
      omega
  · simp only [negP]; rw [bitSize_neg]
    have := slot_len_le p _ (mem_slots_l i)
    have h2 := bitSize_le_unaryRat (coefficient p (Monomial.linear i))
    simp only [coefficient] at h2 this
    omega

theorem unary_short : ∃ b : ℕ, TotalSearch (bounded unarySearch b) := by
  obtain ⟨g, hg⟩ := exists_small_kkt
  set h : Polynomial ℕ := 2 * X + 1 + X * (2 * g.comp (IBqpoly.comp (X + 4)) + 1) with hh
  obtain ⟨k, hk⟩ := poly_bound h
  refine ⟨k, fun a ha => ?_⟩
  obtain ⟨n, hn, p, rfl⟩ := ha
  set s := (unaryCode p).length with hs
  obtain ⟨hns, hQ, hc⟩ := udata p
  obtain ⟨xh, hkkt, hsz⟩ := hg n (negP p)
  refine ⟨encVector xh, ⟨n, hn, p, rfl, xh, rfl, kkt_of_eps p _ (hkkt 0 le_rfl)⟩, ?_⟩
  have hV : vecSize xh ≤ g.eval (IBq (s + 4) (s + 4)) :=
    hsz.trans (poly_eval_mono g ((instSize_q_le (negP p) (s + 4) hQ hc).trans (IBq_mono (by omega) le_rfl)))
  have hl := len_encVector_le xh (vecSize xh) (fun j => le_vecSize xh j)
  have heval : h.eval s = 2 * s + 1 + s * (2 * g.eval (IBq (s + 4) (s + 4)) + 1) := by
    simp [hh, Polynomial.eval_comp, IBqpoly_eval]
  have hb : (encVector xh).length ≤ h.eval s := by
    rw [heval]
    have : n * (2 * vecSize xh + 1) ≤ s * (2 * g.eval (IBq (s + 4) (s + 4)) + 1) :=
      Nat.mul_le_mul hns (by omega)
    omega
  exact hb.trans (hk s)

end UQS

open NetworkEquilibriumCLS.LinearNash UnaryQuadraticKKT.Hardness in
theorem solution : ∃ b : ℕ, TotalSearch (bounded unarySearch b) := UQS.unary_short
