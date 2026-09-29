-- Prove2me | solution 1 for Polynomial.coeff_countP_roots_isDominant_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1256c44d-9eea-59ee-9fd9-43a799cc340d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_coeff_countP_roots_isDominant_of_isAlgClosed

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial

namespace P2mKcNewtonPolygon

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

def gauss (P : K[X]) : Γ₀ := P.support.sup fun i => Valued.v (P.coeff i)

theorem v_coeff_le_gauss (P : K[X]) (i : ℕ) : v (P.coeff i) ≤ gauss P := by
  by_cases h : i ∈ P.support
  · exact Finset.le_sup (f := fun i => v (P.coeff i)) h
  · rw [Polynomial.notMem_support_iff.1 h, map_zero]; exact zero_le'

theorem gauss_le {P : K[X]} {γ : Γ₀} (h : ∀ i, v (P.coeff i) ≤ γ) : gauss P ≤ γ :=
  Finset.sup_le fun i _ => h i

theorem gauss_zero : gauss (0 : K[X]) = 0 := by simp [gauss, bot_eq_zero]

theorem exists_eq_gauss {P : K[X]} (hP : P ≠ 0) : ∃ i ∈ P.support, v (P.coeff i) = gauss P := by
  obtain ⟨i, hi, h⟩ := Finset.exists_mem_eq_sup P.support (Polynomial.support_nonempty.2 hP)
    (fun i => v (P.coeff i))
  exact ⟨i, hi, h.symm⟩

theorem gauss_pos {P : K[X]} (hP : P ≠ 0) : 0 < gauss P := by
  obtain ⟨i, hi, h⟩ := exists_eq_gauss hP
  rw [← h, Valuation.pos_iff]
  exact Polynomial.mem_support_iff.1 hi

theorem gauss_ne_zero {P : K[X]} (hP : P ≠ 0) : gauss P ≠ 0 := (gauss_pos hP).ne'

theorem gauss_C (a : K) : gauss (C a : K[X]) = v a := by
  apply le_antisymm
  · exact gauss_le fun i => by
      rw [coeff_C]; split_ifs
      · exact le_rfl
      · rw [map_zero]; exact zero_le'
  · simpa using v_coeff_le_gauss (C a) 0

theorem gauss_mul_X_sub_C (P : K[X]) (α : K) : gauss (P * (X - C α)) = gauss P * max 1 (v α) := by
  by_cases hP : P = 0
  · rw [hP, zero_mul, gauss_zero, zero_mul]
  have hc0 : (P * (X - C α)).coeff 0 = -(P.coeff 0 * α) := by
    rw [mul_sub, coeff_sub, coeff_mul_X_zero, coeff_mul_C, zero_sub]
  have hcs : ∀ a : ℕ, (P * (X - C α)).coeff (a + 1) = P.coeff a - P.coeff (a + 1) * α := fun a =>
    coeff_mul_X_sub_C
  apply le_antisymm
  · refine gauss_le fun i => ?_
    rcases i with _ | a
    · rw [hc0, Valuation.map_neg, map_mul]
      exact mul_le_mul' (v_coeff_le_gauss P 0) (le_max_right _ _)
    · rw [hcs]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
      · calc v (P.coeff a) = v (P.coeff a) * 1 := (mul_one _).symm
          _ ≤ gauss P * max 1 (v α) := mul_le_mul' (v_coeff_le_gauss P a) (le_max_left _ _)
      · rw [map_mul]; exact mul_le_mul' (v_coeff_le_gauss P _) (le_max_right _ _)
  · classical
    let I : Finset ℕ := P.support.filter fun i => v (P.coeff i) = gauss P
    have hI : I.Nonempty := by
      obtain ⟨i, hi, h⟩ := exists_eq_gauss hP
      exact ⟨i, Finset.mem_filter.2 ⟨hi, h⟩⟩
    have hIspec : ∀ i ∈ I, v (P.coeff i) = gauss P := fun i hi => (Finset.mem_filter.1 hi).2
    have hlt_of_notMem : ∀ i, i ∉ I → v (P.coeff i) < gauss P := fun i hi => by
      refine lt_of_le_of_ne (v_coeff_le_gauss P i) fun h => hi ?_
      refine Finset.mem_filter.2 ⟨Polynomial.mem_support_iff.2 fun h0 => ?_, h⟩
      rw [h0, map_zero] at h; exact gauss_ne_zero hP h.symm
    rcases le_or_gt (v α) 1 with hα | hα
    · rw [max_eq_left hα, mul_one]
      set j := I.max' hI with hj
      have hjI : j ∈ I := Finset.max'_mem I hI
      have hj1 : v (P.coeff (j + 1)) < gauss P := hlt_of_notMem _ fun h =>
        absurd (Finset.le_max' I _ h) (by rw [← hj]; omega)
      have hlt : v (P.coeff (j + 1) * α) < v (P.coeff j) := by
        rw [map_mul, hIspec j hjI]
        exact lt_of_le_of_lt (mul_le_mul' le_rfl hα) (by rw [mul_one]; exact hj1)
      calc gauss P = v ((P * (X - C α)).coeff (j + 1)) := by
            rw [hcs, Valuation.map_sub_eq_of_lt_left _ hlt, hIspec j hjI]
        _ ≤ gauss (P * (X - C α)) := v_coeff_le_gauss _ _
    · rw [max_eq_right hα.le]
      have key : ∀ j, j = I.min' hI → v ((P * (X - C α)).coeff j) = gauss P * v α := by
        intro j hj
        have hjI : j ∈ I := hj ▸ Finset.min'_mem I hI
        rcases j with _ | a
        · rw [hc0, Valuation.map_neg, map_mul, hIspec _ hjI]
        · have ha : v (P.coeff a) < gauss P := hlt_of_notMem _ fun h =>
            absurd (Finset.min'_le I _ h) (by rw [← hj]; omega)
          have hlt : v (P.coeff a) < v (P.coeff (a + 1) * α) := by
            rw [map_mul, hIspec _ hjI]
            exact lt_of_lt_of_le ha (le_of_lt (lt_of_le_of_lt (mul_one _).symm.le
              (mul_lt_mul_of_pos_left hα (gauss_pos hP))))
          rw [hcs, Valuation.map_sub_eq_of_lt_right _ hlt, map_mul, hIspec _ hjI]
      calc gauss P * v α = v ((P * (X - C α)).coeff (I.min' hI)) := (key _ rfl).symm
        _ ≤ gauss (P * (X - C α)) := v_coeff_le_gauss _ _

def IsMaxDom (P : K[X]) (m : ℕ) : Prop := v (P.coeff m) = gauss P ∧ ∀ j, m < j → v (P.coeff j) < gauss P

def IsMinDom (P : K[X]) (m : ℕ) : Prop := v (P.coeff m) = gauss P ∧ ∀ j, j < m → v (P.coeff j) < gauss P

theorem isMaxDom_C {a : K} (ha : a ≠ 0) : IsMaxDom (C a) 0 := by
  refine ⟨by rw [coeff_C_zero, gauss_C], fun j hj => ?_⟩
  rw [coeff_C, if_neg (Nat.pos_iff_ne_zero.1 hj), map_zero, gauss_C]
  exact (Valuation.pos_iff _).2 ha

theorem isMinDom_C {a : K} (ha : a ≠ 0) : IsMinDom (C a) 0 :=
  ⟨by rw [coeff_C_zero, gauss_C], fun j hj => absurd hj (Nat.not_lt_zero j)⟩

section Shift

variable {P : K[X]} {m : ℕ} {α : K}

private theorem c0 (P : K[X]) (α : K) : (P * (X - C α)).coeff 0 = -(P.coeff 0 * α) := by
  rw [mul_sub, coeff_sub, coeff_mul_X_zero, coeff_mul_C, zero_sub]

private theorem cs (P : K[X]) (α : K) (a : ℕ) : (P * (X - C α)).coeff (a + 1) = P.coeff a - P.coeff (a + 1) * α :=
  coeff_mul_X_sub_C

theorem IsMaxDom.mul_X_sub_C_of_le (hP : P ≠ 0) (h : IsMaxDom P m) (hα : v α ≤ 1) :
    IsMaxDom (P * (X - C α)) (m + 1) := by
  have hG : gauss (P * (X - C α)) = gauss P := by rw [gauss_mul_X_sub_C, max_eq_left hα, mul_one]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [hG, cs]
    have hlt : v (P.coeff (m + 1) * α) < v (P.coeff m) := by
      rw [map_mul, h.1]
      exact lt_of_le_of_lt (mul_le_mul' le_rfl hα) (by rw [mul_one]; exact h.2 _ (Nat.lt_succ_self m))
    rw [Valuation.map_sub_eq_of_lt_left _ hlt, h.1]
  · rw [hG]
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [cs]
    have hi : m < i := by omega
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (h.2 i hi) ?_)
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_mul' le_rfl hα) (by rw [mul_one]; exact h.2 (i + 1) (by omega))

theorem IsMaxDom.mul_X_sub_C_of_gt (hP : P ≠ 0) (h : IsMaxDom P m) (hα : 1 < v α) :
    IsMaxDom (P * (X - C α)) m := by
  have hG : gauss (P * (X - C α)) = gauss P * v α := by rw [gauss_mul_X_sub_C, max_eq_right hα.le]
  have hGpos : 0 < gauss P := gauss_pos hP
  have hα0 : 0 < v α := lt_trans zero_lt_one hα
  refine ⟨?_, fun j hj => ?_⟩
  · rw [hG]
    rcases m with _ | i
    · rw [c0, Valuation.map_neg, map_mul, h.1]
    · rw [cs]
      have hlt : v (P.coeff i) < v (P.coeff (i + 1) * α) := by
        rw [map_mul, h.1]
        exact lt_of_le_of_lt (v_coeff_le_gauss P i)
          (lt_of_le_of_lt (mul_one _).symm.le (mul_lt_mul_of_pos_left hα hGpos))
      rw [Valuation.map_sub_eq_of_lt_right _ hlt, map_mul, h.1]
  · rw [hG]
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [cs]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (v_coeff_le_gauss P i)
        (lt_of_le_of_lt (mul_one _).symm.le (mul_lt_mul_of_pos_left hα hGpos))
    · rw [map_mul]
      exact mul_lt_mul_of_pos_right (h.2 (i + 1) (by omega)) hα0

theorem IsMinDom.mul_X_sub_C_of_lt (hP : P ≠ 0) (h : IsMinDom P m) (hα : v α < 1) :
    IsMinDom (P * (X - C α)) (m + 1) := by
  have hG : gauss (P * (X - C α)) = gauss P := by rw [gauss_mul_X_sub_C, max_eq_left hα.le, mul_one]
  have hGpos : 0 < gauss P := gauss_pos hP
  have hsmall : ∀ i, v (P.coeff i * α) < gauss P := fun i => by
    rw [map_mul]
    rcases eq_or_ne (P.coeff i) 0 with h0 | h0
    · rw [h0, map_zero, zero_mul]; exact hGpos
    · calc v (P.coeff i) * v α < v (P.coeff i) * 1 := mul_lt_mul_of_pos_left hα ((Valuation.pos_iff _).2 h0)
        _ ≤ gauss P := by rw [mul_one]; exact v_coeff_le_gauss P i
  refine ⟨?_, fun j hj => ?_⟩
  · rw [hG, cs]
    have hlt : v (P.coeff (m + 1) * α) < v (P.coeff m) := by rw [h.1]; exact hsmall _
    rw [Valuation.map_sub_eq_of_lt_left _ hlt, h.1]
  · rw [hG]
    rcases j with _ | i
    · rw [c0, Valuation.map_neg]; exact hsmall 0
    · rw [cs]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (h.2 i (by omega)) (hsmall _))

theorem IsMinDom.mul_X_sub_C_of_ge (hP : P ≠ 0) (h : IsMinDom P m) (hα : 1 ≤ v α) :
    IsMinDom (P * (X - C α)) m := by
  have hG : gauss (P * (X - C α)) = gauss P * v α := by rw [gauss_mul_X_sub_C, max_eq_right hα]
  have hGpos : 0 < gauss P := gauss_pos hP
  have hα0 : 0 < v α := lt_of_lt_of_le zero_lt_one hα
  have hup : gauss P ≤ gauss P * v α := by
    calc gauss P = gauss P * 1 := (mul_one _).symm
      _ ≤ gauss P * v α := mul_le_mul' le_rfl hα
  refine ⟨?_, fun j hj => ?_⟩
  · rw [hG]
    rcases m with _ | i
    · rw [c0, Valuation.map_neg, map_mul, h.1]
    · rw [cs]
      have hlt : v (P.coeff i) < v (P.coeff (i + 1) * α) := by
        rw [map_mul, h.1]
        exact lt_of_lt_of_le (h.2 i (Nat.lt_succ_self i)) hup
      rw [Valuation.map_sub_eq_of_lt_right _ hlt, map_mul, h.1]
  · rw [hG]
    rcases j with _ | i
    · rw [c0, Valuation.map_neg, map_mul]
      exact mul_lt_mul_of_pos_right (h.2 0 hj) hα0
    · rw [cs]
      refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
      · exact lt_of_lt_of_le (h.2 i (by omega)) hup
      · rw [map_mul]
        exact mul_lt_mul_of_pos_right (h.2 (i + 1) (by omega)) hα0

end Shift

private theorem _root_.P2mKcNewtonPolygon.prod_ne_zero (s : Multiset K) : (s.map fun α => X - C α).prod ≠ 0 :=
  Multiset.prod_ne_zero fun h => by
    obtain ⟨α, -, hα⟩ := Multiset.mem_map.1 h
    exact X_sub_C_ne_zero α hα

p2m_export "P2mKcNewtonPolygon" "prod_ne_zero"
theorem C_mul_prod_ne_zero {a : K} (ha : a ≠ 0) (s : Multiset K) : C a * (s.map fun α => X - C α).prod ≠ 0 :=
  mul_ne_zero (C_ne_zero.2 ha) (prod_ne_zero s)

theorem isDom_C_mul_prod {a : K} (ha : a ≠ 0) (s : Multiset K) :
    IsMaxDom (C a * (s.map fun α => X - C α).prod) (s.countP fun α => v α ≤ 1) ∧
      IsMinDom (C a * (s.map fun α => X - C α).prod) (s.countP fun α => v α < 1) := by
  induction s using Multiset.induction with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, mul_one, Multiset.countP_zero]
    exact ⟨isMaxDom_C ha, isMinDom_C ha⟩
  | cons α s ih =>
    have hne : C a * (s.map fun α => X - C α).prod ≠ 0 := C_mul_prod_ne_zero ha s
    have heq : C a * ((α ::ₘ s).map fun α => X - C α).prod = (C a * (s.map fun α => X - C α).prod) * (X - C α) := by
      rw [Multiset.map_cons, Multiset.prod_cons]; ring
    rw [heq, Multiset.countP_cons, Multiset.countP_cons]
    constructor
    · by_cases hα : v α ≤ 1
      · rw [if_pos hα]; exact ih.1.mul_X_sub_C_of_le hne hα
      · rw [if_neg hα, add_zero]; exact ih.1.mul_X_sub_C_of_gt hne (lt_of_not_ge hα)
    · by_cases hα : v α < 1
      · rw [if_pos hα]; exact ih.2.mul_X_sub_C_of_lt hne hα
      · rw [if_neg hα, add_zero]; exact ih.2.mul_X_sub_C_of_ge hne (le_of_not_gt hα)

theorem eq_C_mul_prod [IsAlgClosed K] (P : K[X]) : P = C P.leadingCoeff * (P.roots.map fun α => X - C α).prod :=
  (C_leadingCoeff_mul_prod_multiset_X_sub_C
    ((splits_iff_card_roots.1 (IsAlgClosed.splits P)).symm ▸ rfl)).symm

theorem isDom_roots [IsAlgClosed K] {p : K[X]} (hp : p ≠ 0) :
    IsMaxDom p (p.roots.countP fun α => v α ≤ 1) ∧ IsMinDom p (p.roots.countP fun α => v α < 1) := by
  have h := isDom_C_mul_prod (leadingCoeff_ne_zero.2 hp) p.roots
  rwa [← eq_C_mul_prod p] at h

end P2mKcNewtonPolygon

open P2mKcNewtonPolygon in
theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (p : Polynomial K) (hp : p ≠ 0) :
    ((∀ j : ℕ, Valued.v (p.coeff j) ≤ Valued.v (p.coeff (p.roots.countP fun α => Valued.v α ≤ 1))) ∧
      ∀ j : ℕ, (p.roots.countP fun α => Valued.v α ≤ 1) < j →
        Valued.v (p.coeff j) < Valued.v (p.coeff (p.roots.countP fun α => Valued.v α ≤ 1))) ∧
    ((∀ j : ℕ, Valued.v (p.coeff j) ≤ Valued.v (p.coeff (p.roots.countP fun α => Valued.v α < 1))) ∧
      ∀ j : ℕ, j < (p.roots.countP fun α => Valued.v α < 1) →
        Valued.v (p.coeff j) < Valued.v (p.coeff (p.roots.countP fun α => Valued.v α < 1))) := by
  obtain ⟨hM, hm⟩ := isDom_roots (K := K) hp
  refine ⟨⟨fun j => ?_, fun j hj => ?_⟩, ⟨fun j => ?_, fun j hj => ?_⟩⟩
  · rw [hM.1]; exact v_coeff_le_gauss p j
  · rw [hM.1]; exact hM.2 j hj
  · rw [hm.1]; exact v_coeff_le_gauss p j
  · rw [hm.1]; exact hm.2 j hj

end
end S_Polynomial_coeff_countP_roots_isDominant_of_isAlgClosed
end P2MW
export P2MW.S_Polynomial_coeff_countP_roots_isDominant_of_isAlgClosed (solution)
