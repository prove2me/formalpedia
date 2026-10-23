-- Prove2me | solution 1 for SensitivityWordFrontier.exists_215_success
-- status  : ACCEPTED   (disprove)
-- author  : @dmilosch
-- created : 2026-10-23T05:40:19.325485+00:00
-- url     : https://prove2.me/submissions/21e45091-1e60-43ac-ac7e-e1c90aa26cab

import Definitions.Def_SensitivityWordFrontier

/-
Diagonal-product obstruction for the fixed K=14055 finite-word frontier.
Every helper below is proved from the imported definitions and Mathlib.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SensitivityProductArithmetic

theorem cross_term_real (x y M : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hM : 0 ≤ M)
    (hxy : M ^ 2 ≤ x * y) :
    201 * M ≤ 7022 * x + 2 * y := by
  by_contra h
  have hlt : 7022 * x + 2 * y < 201 * M := lt_of_not_ge h
  have hleft : 0 ≤ 7022 * x + 2 * y := by positivity
  have hright : 0 ≤ 201 * M := by positivity
  have hsquare : (7022 * x + 2 * y) ^ 2 < (201 * M) ^ 2 :=
    (sq_lt_sq₀ hleft hright).2 hlt
  nlinarith [sq_nonneg (7022 * x - 2 * y)]

theorem product_bound_real (M a c y z : ℝ)
    (hM : 0 ≤ M) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hay : M ≤ a * y) (hzc : M ≤ z * c) :
    7225 * M ≤ (a + c) * (2 * y + 7022 * z) := by
  have hprod : M * M ≤ (a * y) * (z * c) :=
    mul_le_mul hay hzc hM (mul_nonneg ha hy)
  have hcrossprod : M ^ 2 ≤ (a * z) * (c * y) := by
    nlinarith only [hprod]
  have hcross := cross_term_real (a * z) (c * y) M
    (mul_nonneg ha hz) (mul_nonneg hc hy) hM hcrossprod
  nlinarith only [hay, hzc, hcross]

theorem product_bound_nat (M a c y z : ℕ)
    (hay : M ≤ a * y) (hzc : M ≤ z * c) :
    7225 * M ≤ (a + c) * (2 * y + 7022 * z) := by
  have hayR : (M : ℝ) ≤ (a : ℝ) * y := by exact_mod_cast hay
  have hzcR : (M : ℝ) ≤ (z : ℝ) * c := by exact_mod_cast hzc
  have h := product_bound_real M a c y z
    (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) hayR hzcR
  exact_mod_cast h

theorem target_lt_85_power : (14055 : ℕ) ^ 20 < 85 ^ 43 := by
  norm_num

end SensitivityProductArithmetic

namespace SensitivityProductBounds
open SensitivityProfileCycle SensitivityProfileSearch SensitivityProfileWord

theorem coupledCost_lower (q v a b c e : ℕ) :
    a + c ≤ coupledCost q v a b c e := by
  unfold coupledCost
  apply Finset.le_sup_of_le (b := 1) (by simp)
  apply Finset.le_sup_of_le (b := 1) (by simp)
  have hbudget : (1+1).choose 2 ≤ q*1+(q+1)*1 := by simp; omega
  rw [if_pos hbudget]
  simp only [Nat.one_mul, Nat.choose_eq_zero_of_lt (by decide : 1 < 2),
    Nat.sub_zero, Nat.zero_mul, Nat.add_zero]
  nlinarith

theorem ordinaryCost_lower (q v a b c e : ℕ) (hv : 3 ≤ v) :
    a + c ≤ ordinaryCost q v a b c e := by
  unfold ordinaryCost
  apply Finset.le_sup_of_le (b := 1) (by simp)
  apply Finset.le_sup_of_le (b := 1) (by simp)
  apply Finset.le_sup_of_le (b := 1) (by simp)
  have hlimit : ordinaryLimit q 1 1 = q+1 := by simp [ordinaryLimit]
  have hcond : (1+1).choose 2 ≤ q*1+(q+1)*1 ∧
      1+1 ≤ v-1 ∧ (1:ℕ) ≤ 1 ∧ 1 ≤ ordinaryLimit q 1 1 := by
    simp only [hlimit]
    norm_num
    omega
  rw [if_pos hcond, hlimit]
  simp only [Nat.one_mul, Nat.sub_self, Nat.zero_mul, Nat.add_zero]
  nlinarith

theorem dedupCost_lower (internal : ℕ → ℕ) (q v a b c e : ℕ) (hv : 3 ≤ v) :
    a + c ≤ dedupCost internal q v a b c e := by
  unfold dedupCost
  apply Finset.le_sup_of_le (b := 1) (by simp)
  apply Finset.le_sup_of_le (b := 1) (by simp)
  apply Finset.le_sup_of_le (b := 1) (by simp)
  have hlimit : 1 ≤ dedupLimit q 1 1 1 := by
    simp [dedupLimit, ordinaryLimit]
  have hcond : (1+1).choose 2 ≤ q*1+(q+1)*1 ∧
      1+1 ≤ v-1 ∧ (1:ℕ) ≤ 1 ∧ 1 ≤ dedupLimit q 1 1 1 := by
    norm_num
    exact ⟨by omega, by omega, hlimit⟩
  rw [if_pos hcond]
  have hcoef : 1 ≤ min (dedupChoice q 1 1 1) (positiveResidual q 1 1+1) := by
    apply le_min
    · exact le_max_left _ _
    · omega
  simp only [Nat.one_mul]
  nlinarith

theorem sourceCost_lower (v w a b c e : ℕ) (hw : 3 ≤ w) :
    a + c ≤ sourceCost v w a b c e := by
  unfold sourceCost
  apply Finset.le_sup_of_le (b := 1) (by decide)
  apply Finset.le_sup_of_le (b := 1) (by decide)
  apply Finset.le_sup_of_le (b := 1) (by decide)
  have hcond : (1+1).choose 2 ≤ 1 ∧
      1+1 ≤ effectiveCutoff v w 1 1-1 ∧ (1:ℕ) ≤ 1 ∧ 1 ≤ ordinaryLimit 0 1 1 := by
    norm_num [effectiveCutoff, ordinaryLimit]
    omega
  rw [if_pos hcond]
  norm_num [effectiveCutoff, ordinaryLimit]

theorem strictSourceCost_lower (t w a b c e : ℕ) :
    a + c ≤ strictSourceCost t w a b c e := by
  unfold strictSourceCost
  exact (Nat.le_add_right (a+c) ((w-3)*b)).trans
    ((le_max_left _ _).trans ((le_max_left _ _).trans
      ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))))

theorem rawZeroCoupled_diagonal_lower {n : ℕ} (C : Recipe n) (Z Y : Matrix n)
    (k t : ℕ) (v : ℕ → ℕ) (i : Fin n) (hi : 3 ≤ i.val) :
    Z (C.target i) (C.target i) + Y (C.gate i) (C.gate i) ≤
      rawZeroCoupled k t v C Z Y i i := by
  have hnot : ¬ i.val < 3 := by omega
  simp only [rawZeroCoupled, if_neg hnot]
  split_ifs with hq
  · exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
      (le_max_of_le_left (Nat.le_add_right _ _))))
  · exact coupledCost_lower _ _ _ _ _ _

theorem rawZeroOrdinary_diagonal_lower {n : ℕ} (C : Recipe n) (Z Y : Matrix n)
    (k t : ℕ) (v : ℕ → ℕ) (i : Fin n) (hi : 3 ≤ i.val)
    (hv : 3 ≤ v (C.tol i)) :
    Z (C.target i) (C.target i) + Y (C.gate i) (C.gate i) ≤
      rawZeroOrdinary k t v C Z Y i i := by
  rw [rawZeroOrdinary, if_pos ⟨hi, rfl⟩]
  exact le_min (rawZeroCoupled_diagonal_lower C Z Y k t v i hi)
    (ordinaryCost_lower _ _ _ _ _ _ hv)

theorem rawZeroSource_diagonal_lower {n : ℕ} (C : Recipe n) (Z Y : Matrix n)
    (k t w : ℕ) (v : ℕ → ℕ) (i : Fin n) (hi : 3 ≤ i.val)
    (hv : 3 ≤ v (C.tol i)) (hw : 3 ≤ w) :
    Z (C.target i) (C.target i) + Y (C.gate i) (C.gate i) ≤
      rawZeroSource k t v w C Z Y i i := by
  unfold rawZeroSource
  split_ifs
  · exact le_min (rawZeroOrdinary_diagonal_lower C Z Y k t v i hi hv)
      (sourceCost_lower _ _ _ _ _ _ hw)
  · exact rawZeroOrdinary_diagonal_lower C Z Y k t v i hi hv

theorem rawZeroSourceFull_diagonal_lower {n : ℕ} (C : Recipe n) (Z Y : Matrix n)
    (k t w : ℕ) (v : ℕ → ℕ) (i : Fin n) (hi : 3 ≤ i.val)
    (hv : 3 ≤ v (C.tol i)) (hw : 3 ≤ w) :
    Z (C.target i) (C.target i) + Y (C.gate i) (C.gate i) ≤
      rawZeroSourceFull k t v w C Z Y i i := by
  have hnot : ¬ i.val < 3 := by omega
  simp only [rawZeroSourceFull, if_neg hnot]
  split_ifs
  · exact le_min (rawZeroSource_diagonal_lower C Z Y k t w v i hi hv hw)
      (strictSourceCost_lower _ _ _ _ _ _)
  · exact rawZeroSource_diagonal_lower C Z Y k t w v i hi hv hw

theorem rawZeroDedupBoth_diagonal_lower {n : ℕ} (C : Recipe n) (Z Y : Matrix n)
    (k t : ℕ) (v : ℕ → ℕ) (i : Fin n) (hi : 3 ≤ i.val)
    (hv : 3 ≤ v (C.tol i)) :
    Z (C.target i) (C.target i) + Y (C.gate i) (C.gate i) ≤
      rawZeroDedupBoth k t v C Z Y i i := by
  rw [rawZeroDedupBoth, if_pos ⟨hi, rfl⟩]
  exact le_min (rawZeroCoupled_diagonal_lower C Z Y k t v i hi)
    (dedupCost_lower _ _ _ _ _ _ _ hv)

theorem rawZero_diagonal_lower {n : ℕ} (C : Recipe n) (Z Y : Matrix n)
    (i : Fin n) (hi : 3 ≤ i.val) (hq : C.tol i < 6) :
    Z (C.target i) (C.target i) + Y (C.gate i) (C.gate i) ≤
      rawZeroSourceCombined 14055 24 (extendCutoffs cutoffs) 22 C Z Y i i := by
  have hv : 3 ≤ extendCutoffs cutoffs (C.tol i) := by
    interval_cases h : C.tol i <;> norm_num [extendCutoffs, cutoffs, h]
  exact le_min (rawZeroSourceFull_diagonal_lower C Z Y 14055 24 22 _ i hi hv (by decide))
    (rawZeroDedupBoth_diagonal_lower C Z Y 14055 24 _ i hi hv)

end SensitivityProductBounds

namespace SensitivityProductInduction
open SensitivityProfileCycle SensitivityProfileSearch SensitivityProfileWord

variable {n : ℕ}

theorem envelope_diag (A : Matrix n) (i : Fin n) : envelope A i i = A i i := by
  have heq : intervals i i = {(i, i)} := by
    ext ab
    simp only [intervals, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro h
      exact Prod.ext (le_antisymm (le_trans h.2.1 h.2.2) h.1)
        (le_antisymm h.2.2 (le_trans h.1 h.2.1))
    · rintro rfl
      exact ⟨le_rfl, le_rfl, le_rfl⟩
  simp [envelope, heq]

theorem ordinary_one_lower (C : Recipe n) (P : Profile n) (i : Fin n)
    (hi : 3 ≤ i.val) (hq : C.tol i < 6) :
    2 * P.one (C.target i) (C.target i) +
      7022 * P.zero (C.gate i) (C.gate i) ≤ (step C P).one i i := by
  have hi' : ¬ i.val < 3 := by omega
  simp only [step, envelope_diag, rawOne, hi', if_false, if_true]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_right
  omega

theorem auxiliary_product_lower (C : Recipe n) (P : Profile n) (i : Fin n)
    (hi : i.val < 3) (M : ℕ)
    (hP : ∀ j, M ≤ P.zero j j * P.one j j) :
    14055 * M ≤ (step C P).zero i i * (step C P).one i i := by
  have hi' : ¬ 3 ≤ i.val := by omega
  simp only [step, envelope_diag, rawOne, rawZeroSourceCombined,
    rawZeroSourceFull, rawZeroSource, rawZeroOrdinary, rawZeroDedupBoth,
    rawZeroCoupled, hi, hi', false_and, if_false, if_true, min_self]
  have hM := hP (C.target i)
  generalize C.aux i = a
  fin_cases a <;> norm_num [auxCost, Fin.ext_iff] <;> nlinarith

/- The two arithmetic helper hypotheses are discharged by the separately
checked cost enumeration and integer product inequality. -/
variable
  (hzero : ∀ (C : Recipe n) (P : Profile n) (i : Fin n),
    3 ≤ i.val → C.tol i < 6 →
      P.zero (C.target i) (C.target i) + P.one (C.gate i) (C.gate i) ≤
        rawZeroSourceCombined 14055 24 (extendCutoffs cutoffs) 22 C P.zero P.one i i)
  (hproduct : ∀ (M a c y z : ℕ), M ≤ a*y → M ≤ z*c →
    7225*M ≤ (a+c)*(2*y+7022*z))

include hzero hproduct

theorem step_product_lower (C : Recipe n) (P : Profile n) (M : ℕ)
    (hC : ∀ i, 3 ≤ i.val → 0 < C.tol i → C.tol i < 6)
    (hP : ∀ i, M ≤ P.zero i i * P.one i i) :
    ∀ i, 7225*M ≤ (step C P).zero i i * (step C P).one i i := by
  intro i
  by_cases hi : i.val < 3
  · exact le_trans (Nat.mul_le_mul_right M (by decide))
      (auxiliary_product_lower C P i hi M hP)
  · have hi' : 3 ≤ i.val := by omega
    have hq : C.tol i < 6 := by
      by_cases hp : 0 < C.tol i
      · exact hC i hi' hp
      · omega
    have hz : P.zero (C.target i) (C.target i) +
        P.one (C.gate i) (C.gate i) ≤ (step C P).zero i i := by
      simpa only [step, envelope_diag] using hzero C P i hi' hq
    have hy := ordinary_one_lower C P i hi' hq
    exact le_trans
      (hproduct M _ _ _ _ (hP (C.target i)) (hP (C.gate i)))
      (Nat.mul_le_mul hz hy)

end SensitivityProductInduction

namespace SensitivityProductBounds
open SensitivityProfileCycle SensitivityProfileSearch SensitivityProfileWord
variable {n : ℕ}

theorem step_product (C : Recipe n) (P : Profile n) (M : ℕ)
    (htol : ∀ i, 3 ≤ i.val → C.tol i < 6)
    (hP : ∀ i, M ≤ P.zero i i * P.one i i) :
    ∀ i, 7225 * M ≤ (step C P).zero i i * (step C P).one i i := by
  exact SensitivityProductInduction.step_product_lower
    (fun C P i hi hq => rawZero_diagonal_lower C P.zero P.one i hi hq)
    SensitivityProductArithmetic.product_bound_nat
    C P M (fun i hi _ => htol i hi) hP

end SensitivityProductBounds

namespace SensitivityFrontierObstruction
open SensitivityProfileCycle SensitivityProfileSearch SensitivityProfileWord
open SensitivityWordFinite SensitivityWordFrontier

theorem envelope_diag {n : ℕ} (A : Matrix n) (i : Fin n) :
    envelope A i i = A i i := by
  have heq : intervals i i = {(i,i)} := by
    ext ab
    simp only [intervals, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hi, hab, hb⟩
      exact Prod.ext (le_antisymm (hab.trans hb) hi)
        (le_antisymm hb (hi.trans hab))
    · rintro rfl
      exact ⟨le_rfl, le_rfl, le_rfl⟩
  simp [envelope, heq]

theorem prune_mem {α : Type} (R : α → α → Prop) [DecidableRel R]
    {s : List α} {x : α} (hx : x ∈ FiniteDominance.prune R s) : x ∈ s := by
  induction s with
  | nil => exact hx
  | cons y s ih =>
    change x ∈ FiniteDominance.insert R y (FiniteDominance.prune R s) at hx
    unfold FiniteDominance.insert at hx
    split at hx
    · exact List.mem_cons_of_mem y (ih hx)
    · rcases List.mem_cons.mp hx with hxy | hx
      · exact List.mem_cons.mpr (Or.inl hxy)
      · exact List.mem_cons_of_mem y (ih (List.mem_filter.mp hx).1)

variable (step_product_bound : ∀ {n : ℕ} (C : Recipe n) (P : Profile n) (M : ℕ),
  (∀ i, 3 ≤ i.val → C.tol i < 6) →
  (∀ i, M ≤ P.zero i i * P.one i i) →
  ∀ i, 7225 * M ≤ (step C P).zero i i * (step C P).one i i)

include step_product_bound

theorem frontier_product {n k : ℕ} {P : Profile n} (hP : P ∈ frontier n k) :
    ∀ i, 7225 ^ k ≤ P.zero i i * P.one i i := by
  induction k generalizing P with
  | zero =>
    have heq : P = normalize (unitProfile n) := by
      change P ∈ [normalize (unitProfile n)] at hP
      simpa using hP
    subst P
    intro i
    simp [SensitivityProfileSearch.normalize, envelope_diag, unitProfile]
  | succ k ih =>
    have hmem := prune_mem Below hP
    obtain ⟨Q, hQ, hPQ⟩ := List.mem_flatMap.mp hmem
    obtain ⟨C, _hC, hCP⟩ := List.mem_map.mp hPQ
    have hs := step_product_bound C.recipe Q (7225^k)
      (fun i _ => (C.tol i).isLt) (ih hQ)
    intro i
    simpa only [hCP, pow_succ, Nat.mul_comm] using hs i

omit step_product_bound in
theorem entries_le_height {n : ℕ} (P : Profile n) (i j : Fin n) :
    P.zero i j ≤ height P ∧ P.one i j ≤ height P := by
  have hb : max (P.zero i j) (P.one i j) ≤ height P :=
    (Finset.le_sup (f := fun ij : Fin n × Fin n =>
      max (P.zero ij.1 ij.2) (P.one ij.1 ij.2)) (Finset.mem_univ (i,j))).trans
        (le_max_right _ _)
  exact ⟨(le_max_left _ _).trans hb, (le_max_right _ _).trans hb⟩

theorem frontier_height_lower {n k : ℕ} (hn : 0 < n)
    {P : Profile n} (hP : P ∈ frontier n k) : 85 ^ k ≤ height P := by
  let i : Fin n := ⟨0, hn⟩
  have hprod := frontier_product step_product_bound hP i
  have hentries := entries_le_height P i i
  have hsquare : 7225 ^ k ≤ height P * height P :=
    hprod.trans (Nat.mul_le_mul hentries.1 hentries.2)
  have heq : (7225 : ℕ)^k = (85^k)^2 := by
    have hbase : (7225 : ℕ) = 85^2 := by norm_num
    rw [hbase, ← pow_mul, ← pow_mul, Nat.mul_comm 2 k]
  rw [heq] at hsquare
  nlinarith

theorem no_success (hbase : (14055 : ℕ)^20 ≤ 85^43)
    {n : ℕ} (hn : 0 < n) (k : ℕ) : succeeds n k ≠ true := by
  intro hs
  obtain ⟨P, hP, hgap⟩ := List.any_eq_true.mp hs
  have hgap' : height P ^ 43 < 14055 ^ (20*k) := of_decide_eq_true hgap
  have hheight := frontier_height_lower step_product_bound hn hP
  have hleft : 14055 ^ (20*k) ≤ (85^k)^43 := by
    have hb := Nat.pow_le_pow_left hbase k
    simpa only [← pow_mul, Nat.mul_comm] using hb
  have hright : (85^k)^43 ≤ height P ^ 43 := Nat.pow_le_pow_left hheight 43
  exact (not_lt_of_ge (hleft.trans hright)) hgap'

end SensitivityFrontierObstruction

theorem solution :
    ¬ (∃ n k : ℕ, SensitivityWordFrontier.succeeds (n+1) k = true) := by
  rintro ⟨n, k, hs⟩
  exact SensitivityFrontierObstruction.no_success
    SensitivityProductBounds.step_product
    (le_of_lt SensitivityProductArithmetic.target_lt_85_power)
    (Nat.zero_lt_succ n) k hs

#print axioms solution
