-- Prove2me | solution 1 for PvsNP.spatialBidiagonal_firstCell
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T17:20:51.114672+00:00
-- url     : https://prove2.me/submissions/fd97b5a4-8fe9-4c57-86fd-2e96504b6710

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace PvsNP.EffectiveGuessing.SpatialBidiagonal
open scoped BigOperators

/-- Number of ways to distribute the staying steps over the available cells. -/
def stayWays (enabled steps : ℕ) : ℕ :=
  if steps = 0 then 1 else
    if enabled = 0 then 0 else (steps+enabled-1).choose steps

@[simp] theorem stayWays_zero (enabled : ℕ) : stayWays enabled 0 = 1 := by
  simp [stayWays]

private theorem stayWays_at_one (steps : ℕ) : stayWays 1 steps = 1 := by
  by_cases h : steps = 0 <;> simp [stayWays,h]

private theorem stayWays_pascal (m k : ℕ) :
    stayWays (m+1) (k+1) = stayWays (m+1) k + stayWays m (k+1) := by
  cases m with
  | zero => simp [stayWays]
  | succ m =>
    cases k with
    | zero => simp [stayWays,Nat.add_comm]
    | succ k =>
      simp only [stayWays,Nat.succ_ne_zero,if_false]
      convert Nat.choose_succ_succ' (k+m+2) (k+1) using 3 <;> omega

/-- Offsets increase away from the queried cell. Include both endpoint
stay flags, but only the intervening pull flags. -/
def stays (stay : ℕ → Bool) (i : ℕ) : ℕ → ℕ
  | 0 => (stay i).toNat
  | d+1 => (stay i).toNat + stays stay (i+1) d

def connected (pull : ℕ → Bool) (i : ℕ) : ℕ → Bool
  | 0 => true
  | d+1 => pull i && connected pull (i+1) d

/-- Integer path count before reduction modulo two. -/
def coefficient (stay pull : ℕ → Bool) (t i d : ℕ) : ℕ :=
  if d ≤ t ∧ connected pull i d = true then
    stayWays (stays stay i d) (t-d)
  else 0

@[simp] theorem coefficient_beyond (stay pull : ℕ → Bool) {t i d : ℕ} (late : t < d) :
    coefficient stay pull t i d = 0 := by
  simp [coefficient,not_le_of_gt late]

@[simp] theorem coefficient_time_zero_here (stay pull : ℕ → Bool) (i : ℕ) :
    coefficient stay pull 0 i 0 = 1 := by
  simp [coefficient,connected]

private theorem same_cell_succ (stay pull : ℕ → Bool) (t i : ℕ) :
    coefficient stay pull (t+1) i 0 =
      (stay i).toNat * coefficient stay pull t i 0 := by
  cases active : stay i
  · simp [coefficient,connected,stays,active,stayWays]
  · simp [coefficient,connected,stays,active,stayWays_at_one]

private theorem weight_pascal (b : Bool) (m t d : ℕ) :
    (if d+1 ≤ t+1 then stayWays (b.toNat+m) (t+1-(d+1)) else 0) =
      b.toNat * (if d+1 ≤ t then stayWays (b.toNat+m) (t-(d+1)) else 0) +
      (if d ≤ t then stayWays m (t-d) else 0) := by
  cases b with
  | false => simp
  | true =>
    simp only [Bool.toNat_true,Nat.one_mul,Nat.succ_le_succ_iff,Nat.add_sub_add_right]
    by_cases late : d ≤ t
    · obtain ⟨k,eq⟩ := Nat.exists_eq_add_of_le late
      subst t
      cases k with
      | zero => simp
      | succ k =>
        rw [if_pos (by omega : d ≤ d+(k+1)),if_pos (by omega : d+1 ≤ d+(k+1))]
        simp only [if_pos (by omega : d ≤ d+(k+1))]
        rw [show d+(k+1)-d = k+1 by omega, show d+(k+1)-(d+1) = k by omega]
        simpa only [Nat.add_comm 1 m] using stayWays_pascal m k
    · simp [late,show ¬d+1 ≤ t by omega]

private theorem farther_cell_succ (stay pull : ℕ → Bool) (t i d : ℕ) :
    coefficient stay pull (t+1) i (d+1) =
      (stay i).toNat * coefficient stay pull t i (d+1) +
      (pull i).toNat * coefficient stay pull t (i+1) d := by
  cases edge : pull i
  · simp [coefficient,connected,edge]
  · cases suffix : connected pull (i+1) d
    · simp [coefficient,connected,edge,suffix]
    · simpa only [coefficient,connected,edge,suffix,Bool.true_and,and_true,
        Bool.toNat_true,Nat.one_mul,stays] using weight_pascal (stay i) (stays stay (i+1) d) t d

section Semiring
variable {K : Type} [Semiring K]

/-- Arbitrary position-specific Boolean diagonal and adjoining coefficients. -/
def round (stay pull : ℕ → Bool) (data : ℕ → K) (i : ℕ) : K :=
  ((stay i).toNat : K)*data i + ((pull i).toNat : K)*data (i+1)

private def contribution (stay pull : ℕ → Bool) (data : ℕ → K) (t i d : ℕ) : K :=
  (coefficient stay pull t i d : K)*data (i+d)

theorem round_iterate (stay pull : ℕ → Bool) (data : ℕ → K) (t i : ℕ) :
    ((round stay pull)^[t] data) i =
      ∑ d ∈ Finset.range (t+1), (coefficient stay pull t i d : K)*data (i+d) := by
  induction t generalizing i with
  | zero => simp
  | succ t ih =>
    change _ = ∑ d ∈ Finset.range ((t+1)+1), contribution stay pull data (t+1) i d
    rw [Function.iterate_succ_apply',round,ih,ih]
    conv_rhs => rw [Finset.sum_range_succ']
    have tail : (∑ d ∈ Finset.range (t+1), contribution stay pull data (t+1) i (d+1)) =
        (∑ d ∈ Finset.range (t+1), ((stay i).toNat : K)*
          contribution stay pull data t i (d+1)) +
        (∑ d ∈ Finset.range (t+1), ((pull i).toNat : K)*
          contribution stay pull data t (i+1) d) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d _
      rw [contribution,farther_cell_succ]
      simp only [contribution,Nat.cast_add,Nat.cast_mul,add_mul,mul_assoc]
      rw [show (i+(d+1)) = (i+1)+d by omega]
    have head : contribution stay pull data (t+1) i 0 =
        ((stay i).toNat : K)*contribution stay pull data t i 0 := by
      simp [contribution,same_cell_succ,Nat.cast_mul,mul_assoc]
    have merged : (∑ d ∈ Finset.range (t+1), contribution stay pull data t i (d+1)) +
        contribution stay pull data t i 0 =
        ∑ d ∈ Finset.range (t+1), contribution stay pull data t i d := by
      rw [← Finset.sum_range_succ',Finset.sum_range_succ]
      simp [contribution,coefficient_beyond]
    rw [tail,head,← Finset.mul_sum,← Finset.mul_sum,add_right_comm,← mul_add,merged]
    rfl

def zeroTail (data : List K) (i : ℕ) : K := data[i]?.getD 0

/-- For finite input the sum is bounded by the tape length, even when
the binary duration denotes a very large integer. -/
theorem first_cell_finite (stay pull : ℕ → Bool) (data : List K) (t : ℕ) :
    ((round stay pull)^[t] (zeroTail data)) 0 =
      ∑ d ∈ Finset.range data.length, (coefficient stay pull t 0 d : K)*zeroTail data d := by
  rw [round_iterate]
  simp only [Nat.zero_add]
  let f (d : ℕ) := (coefficient stay pull t 0 d : K)*zeroTail data d
  change ∑ d ∈ Finset.range (t+1), f d = ∑ d ∈ Finset.range data.length, f d
  rcases le_total (t+1) data.length with shorter | shorter
  · apply Finset.sum_subset (Finset.range_mono shorter)
    intro d _ outside
    have late : t < d := by
      simp only [Finset.mem_range,not_lt] at outside
      omega
    simp [f,coefficient_beyond _ _ late]
  · symm
    apply Finset.sum_subset (Finset.range_mono shorter)
    intro d _ outside
    have late : data.length ≤ d := by simpa only [Finset.mem_range,not_lt] using outside
    simp [f,zeroTail,List.getElem?_eq_none late]


private theorem stays_eq_sum (stay : ℕ → Bool) (i d : ℕ) :
    stays stay i d = ∑ j ∈ Finset.range (d + 1), (stay (i + j)).toNat := by
  induction d generalizing i with
  | zero => simp [stays]
  | succ d ih =>
    rw [stays, Finset.sum_range_succ', ih]
    rw [Nat.add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    omega

private theorem connected_eq_true (pull : ℕ → Bool) (i d : ℕ) :
    connected pull i d = true ↔ ∀ j < d, pull (i + j) = true := by
  induction d generalizing i with
  | zero => simp [connected]
  | succ d ih =>
    rw [connected, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨here, rest⟩ j hj
      cases j with
      | zero => simpa using here
      | succ j =>
        convert rest j (by omega) using 2
        omega
    · intro flags
      exact ⟨by simpa using flags 0 (by omega), fun j hj => by
        convert flags (j + 1) (by omega) using 2
        omega⟩

end Semiring
end PvsNP.EffectiveGuessing.SpatialBidiagonal

open scoped BigOperators
open PvsNP.EffectiveGuessing.SpatialBidiagonal

theorem solution {K : Type} [Semiring K]
    (stay pull : ℕ → Bool) (data : List K) (t : ℕ) :
    let step (v : ℕ → K) (i : ℕ) : K :=
      ((stay i).toNat : K) * v i + ((pull i).toNat : K) * v (i + 1)
    let w (d : ℕ) : ℕ := ∑ j ∈ Finset.range (d + 1), (stay j).toNat
    let paths (d : ℕ) : ℕ :=
      if d ≤ t ∧ (∀ j < d, pull j = true) then
        if t = d then 1 else if w d = 0 then 0 else (t - d + w d - 1).choose (t - d)
      else 0
    (step^[t] (fun i => data[i]?.getD 0)) 0 =
      ∑ d ∈ Finset.range data.length, (paths d : K) * data[d]?.getD 0 := by
  intro step w paths
  change ((round stay pull)^[t] (zeroTail data)) 0 =
    ∑ d ∈ Finset.range data.length, (paths d : K) * zeroTail data d
  rw [first_cell_finite]
  apply Finset.sum_congr rfl
  intro d _
  have counts : stays stay 0 d = w d := by simpa [w] using stays_eq_sum stay 0 d
  by_cases accessible : d ≤ t ∧ (∀ j < d, pull j = true)
  · have h : connected pull 0 d = true :=
      (connected_eq_true pull 0 d).2 (by simpa using accessible.2)
    have eq : t - d = 0 ↔ t = d := by omega
    dsimp only [paths]
    rw [if_pos accessible]
    simp [coefficient, stayWays, accessible.1, h, counts, eq]
  · have h : ¬(d ≤ t ∧ connected pull 0 d = true) := by
      simpa [connected_eq_true] using accessible
    dsimp only [paths]
    rw [if_neg accessible]
    simp [coefficient, h]
