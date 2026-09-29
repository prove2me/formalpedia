-- Prove2me | solution 1 for Valued.v_prod_sub_one_sub_sum_sub_le_of_forall_v_sub_sub_mul_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/623205bb-6b99-5526-9ddc-b2127c591f98

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Valued_v_prod_sub_one_sub_sum_sub_le_of_forall_v_sub_sub_mul_sub_le

set_option autoImplicit false

namespace ProdTaylorCore

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

lemma v_one_add_le_one {x : K} {s : Γ₀} (hs : s ≤ 1) (hx : Valued.v x ≤ s) :
    Valued.v (1 + x) ≤ 1 :=
  Valuation.map_add_le _ (by simp) (hx.trans hs)

lemma v_prod_one_add_le_one {n : ℕ} (x : Fin n → K) {s : Γ₀} (hs : s ≤ 1)
    (hx : ∀ i, Valued.v (x i) ≤ s) : Valued.v (∏ i, (1 + x i)) ≤ 1 := by
  rw [map_prod]
  exact Finset.prod_le_one' (fun i _ => v_one_add_le_one hs (hx i))

lemma v_prod_one_add_sub_one_le : ∀ {n : ℕ} (x : Fin n → K) {s : Γ₀}, s ≤ 1 →
    (∀ i, Valued.v (x i) ≤ s) → Valued.v (∏ i, (1 + x i) - 1) ≤ s
  | 0, x, s, _, _ => by simp
  | n + 1, x, s, hs, hx => by
    rw [Fin.prod_univ_castSucc]
    set P := ∏ i : Fin n, (1 + x (Fin.castSucc i)) with hP
    have hP1 : Valued.v (P - 1) ≤ s :=
      v_prod_one_add_sub_one_le (fun i => x (Fin.castSucc i)) hs (fun i => hx _)
    have hy : Valued.v (x (Fin.last n)) ≤ s := hx _
    have : P * (1 + x (Fin.last n)) - 1 = (P - 1) + ((P - 1) * x (Fin.last n) + x (Fin.last n)) := by ring
    rw [this]
    refine Valuation.map_add_le _ hP1 (Valuation.map_add_le _ ?_ hy)
    rw [map_mul]
    calc Valued.v (P - 1) * Valued.v (x (Fin.last n)) ≤ s * 1 :=
          mul_le_mul' hP1 (hy.trans hs)
      _ = s := mul_one s

lemma v_prod_one_add_sub_prod_one_add_le : ∀ {n : ℕ} (x x' : Fin n → K) {s t : Γ₀}, s ≤ 1 →
    (∀ i, Valued.v (x i) ≤ s) → (∀ i, Valued.v (x' i) ≤ s) → (∀ i, Valued.v (x i - x' i) ≤ t) →
    Valued.v (∏ i, (1 + x i) - ∏ i, (1 + x' i)) ≤ t
  | 0, x, x', s, t, _, _, _, _ => by simp
  | n + 1, x, x', s, t, hs, hx, hx', hxx' => by
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    set P := ∏ i : Fin n, (1 + x (Fin.castSucc i)) with hP
    set P' := ∏ i : Fin n, (1 + x' (Fin.castSucc i)) with hP'
    have hPP' : Valued.v (P - P') ≤ t :=
      v_prod_one_add_sub_prod_one_add_le (fun i => x (Fin.castSucc i)) (fun i => x' (Fin.castSucc i)) hs
        (fun i => hx _) (fun i => hx' _) (fun i => hxx' _)
    have hP'1 : Valued.v P' ≤ 1 := v_prod_one_add_le_one (fun i => x' (Fin.castSucc i)) hs (fun i => hx' _)
    have h1y : Valued.v (1 + x (Fin.last n)) ≤ 1 := v_one_add_le_one hs (hx _)
    have : P * (1 + x (Fin.last n)) - P' * (1 + x' (Fin.last n)) =
        (P - P') * (1 + x (Fin.last n)) + P' * (x (Fin.last n) - x' (Fin.last n)) := by ring
    rw [this]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [map_mul]
      calc Valued.v (P - P') * Valued.v (1 + x (Fin.last n)) ≤ t * 1 := mul_le_mul' hPP' h1y
        _ = t := mul_one t
    · rw [map_mul]
      calc Valued.v P' * Valued.v (x (Fin.last n) - x' (Fin.last n)) ≤ 1 * t := mul_le_mul' hP'1 (hxx' _)
        _ = t := one_mul t

lemma v_prodRem_sub_prodRem_le : ∀ {n : ℕ} (x x' : Fin n → K) {s t : Γ₀}, s ≤ 1 →
    (∀ i, Valued.v (x i) ≤ s) → (∀ i, Valued.v (x' i) ≤ s) → (∀ i, Valued.v (x i - x' i) ≤ t) →
    Valued.v ((∏ i, (1 + x i) - 1 - ∑ i, x i) - (∏ i, (1 + x' i) - 1 - ∑ i, x' i)) ≤ t * s
  | 0, x, x', s, t, _, _, _, _ => by simp
  | n + 1, x, x', s, t, hs, hx, hx', hxx' => by
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    set P := ∏ i : Fin n, (1 + x (Fin.castSucc i)) with hP
    set P' := ∏ i : Fin n, (1 + x' (Fin.castSucc i)) with hP'
    set S := ∑ i : Fin n, x (Fin.castSucc i) with hS
    set S' := ∑ i : Fin n, x' (Fin.castSucc i) with hS'
    set y := x (Fin.last n) with hy
    set y' := x' (Fin.last n) with hy'
    have IH : Valued.v ((P - 1 - S) - (P' - 1 - S')) ≤ t * s :=
      v_prodRem_sub_prodRem_le (fun i => x (Fin.castSucc i)) (fun i => x' (Fin.castSucc i)) hs
        (fun i => hx _) (fun i => hx' _) (fun i => hxx' _)
    have hPP' : Valued.v (P - P') ≤ t :=
      v_prod_one_add_sub_prod_one_add_le (fun i => x (Fin.castSucc i)) (fun i => x' (Fin.castSucc i)) hs
        (fun i => hx _) (fun i => hx' _) (fun i => hxx' _)
    have hP1 : Valued.v (P - 1) ≤ s :=
      v_prod_one_add_sub_one_le (fun i => x (Fin.castSucc i)) hs (fun i => hx _)
    have : (P * (1 + y) - 1 - (S + y)) - (P' * (1 + y') - 1 - (S' + y')) =
        ((P - 1 - S) - (P' - 1 - S')) + ((P - 1) * (y - y') + (P - P') * y') := by ring
    rw [this]
    refine Valuation.map_add_le _ IH (Valuation.map_add_le _ ?_ ?_)
    · rw [map_mul, mul_comm t s]
      exact mul_le_mul' hP1 (hxx' _)
    · rw [map_mul]
      exact mul_le_mul' hPP' (hx' _)

lemma v_prodRem_le {n : ℕ} (x : Fin n → K) {s : Γ₀} (hs : s ≤ 1)
    (hx : ∀ i, Valued.v (x i) ≤ s) :
    Valued.v (∏ i, (1 + x i) - 1 - ∑ i, x i) ≤ s * s := by
  have h := v_prodRem_sub_prodRem_le x (fun _ => 0) (t := s) hs hx (fun _ => by simp)
    (fun i => by simpa using hx i)
  simpa using h

end ProdTaylorCore

theorem solution
    {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {n r : ℕ} (F : Fin n → Fin r → K → K) (d : Fin n → Fin r → K)
    (hd : ∀ i j, Valued.v (d i j) ≤ 1)
    (hF0 : ∀ i j, F i j 0 = 1)
    (hF : ∀ (i : Fin n) (j : Fin r) (e e' : K) (s t : Γ₀), s < 1 → Valued.v e ≤ s → Valued.v e' ≤ s →
      Valued.v (e - e') ≤ t → Valued.v (F i j e - F i j e' - d i j * (e - e')) ≤ t * s) :
    (∀ j : Fin r, (∏ i, F i j ((0 : Fin n → K) i)) - 1 - ∑ i, d i j * (0 : Fin n → K) i = 0) ∧
    ∀ (ε ε' : Fin n → K) (s t : Γ₀), s < 1 → (∀ i, Valued.v (ε i) ≤ s) → (∀ i, Valued.v (ε' i) ≤ s) →
      (∀ i, Valued.v (ε i - ε' i) ≤ t) →
      ∀ j : Fin r, Valued.v (((∏ i, F i j (ε i)) - 1 - ∑ i, d i j * ε i) - ((∏ i, F i j (ε' i)) - 1 - ∑ i, d i j * ε' i))
        ≤ t * s := by
  classical
  refine ⟨fun j => by simp [hF0], ?_⟩
  intro ε ε' s t hs hε hε' hεε' j
  have hs1 : s ≤ 1 := le_of_lt hs

  have hxle : ∀ η : Fin n → K, (∀ i, Valued.v (η i) ≤ s) → ∀ i, Valued.v (F i j (η i) - 1) ≤ s := by
    intro η hη i
    have h1 := hF i j (η i) 0 s s hs (hη i) (by simp) (by simpa using hη i)
    rw [hF0] at h1
    have : F i j (η i) - 1 = (F i j (η i) - 1 - d i j * (η i - 0)) + d i j * η i := by ring
    rw [this]
    refine Valuation.map_add_le _ (h1.trans ?_) ?_
    · calc s * s ≤ 1 * s := mul_le_mul' hs1 le_rfl
        _ = s := one_mul s
    · rw [map_mul]
      calc Valued.v (d i j) * Valued.v (η i) ≤ 1 * s := mul_le_mul' (hd i j) (hη i)
        _ = s := one_mul s

  have hxx' : ∀ i, Valued.v ((F i j (ε i) - 1) - (F i j (ε' i) - 1)) ≤ t := by
    intro i
    have h1 := hF i j (ε i) (ε' i) s t hs (hε i) (hε' i) (hεε' i)
    have : (F i j (ε i) - 1) - (F i j (ε' i) - 1) =
        (F i j (ε i) - F i j (ε' i) - d i j * (ε i - ε' i)) + d i j * (ε i - ε' i) := by ring
    rw [this]
    refine Valuation.map_add_le _ (h1.trans ?_) ?_
    · calc t * s ≤ t * 1 := mul_le_mul' le_rfl hs1
        _ = t := mul_one t
    · rw [map_mul]
      calc Valued.v (d i j) * Valued.v (ε i - ε' i) ≤ 1 * t := mul_le_mul' (hd i j) (hεε' i)
        _ = t := one_mul t

  have hE := ProdTaylorCore.v_prodRem_sub_prodRem_le (fun i => F i j (ε i) - 1) (fun i => F i j (ε' i) - 1)
    hs1 (hxle ε hε) (hxle ε' hε') hxx'
  have hp : ∀ η : Fin n → K, (∏ i, (1 + (F i j (η i) - 1))) = ∏ i, F i j (η i) :=
    fun η => Finset.prod_congr rfl (fun i _ => by ring)
  rw [hp ε, hp ε'] at hE

  have hS : Valued.v (∑ i, (F i j (ε i) - F i j (ε' i) - d i j * (ε i - ε' i))) ≤ t * s :=
    Valuation.map_sum_le _ (fun i _ => hF i j (ε i) (ε' i) s t hs (hε i) (hε' i) (hεε' i))
  have key : ((∏ i, F i j (ε i)) - 1 - ∑ i, d i j * ε i) - ((∏ i, F i j (ε' i)) - 1 - ∑ i, d i j * ε' i) =
      (((∏ i, F i j (ε i)) - 1 - ∑ i, (F i j (ε i) - 1)) - ((∏ i, F i j (ε' i)) - 1 - ∑ i, (F i j (ε' i) - 1)))
        + ∑ i, (F i j (ε i) - F i j (ε' i) - d i j * (ε i - ε' i)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [key]
  exact Valuation.map_add_le _ hE hS

end S_Valued_v_prod_sub_one_sub_sum_sub_le_of_forall_v_sub_sub_mul_sub_le
end P2MW
export P2MW.S_Valued_v_prod_sub_one_sub_sum_sub_le_of_forall_v_sub_sub_mul_sub_le (solution)
