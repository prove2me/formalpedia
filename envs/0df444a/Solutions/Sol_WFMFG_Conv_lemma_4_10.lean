-- Prove2me | solution 1 for WFMFG.Conv.lemma_4_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T16:55:42.896772+00:00
-- url     : https://prove2.me/submissions/913e538b-fc93-4413-bd92-372cf857dd20

import Mathlib
import Definitions.Def_WFMFG_Conv_Simplex
import Definitions.Def_WFMFG_Conv_Multinomial
import Definitions.Def_WFMFG_Conv_Setting
import Theorems.Thm_WFMFG_Conv_lemma_4_9

open Finset WFMFG.Conv

namespace WFMFG410

lemma empMeas_eq {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) (k : Fin d) :
    empMeas x y k = ∑ m, (if x m = k then (y m : ℝ) / N else 0) := by
  simp [empMeas, empQ, Finset.mul_sum, apply_ite, div_eq_inv_mul]

lemma sum_empMeas_mul {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) (G : Fin d → ℝ) :
    ∑ k, empMeas x y k * G k = ∑ m, ((y m : ℝ) / N) * G (x m) := by
  simp_rw [empMeas_eq, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  simp [ite_mul]

lemma pos_lip (a b : ℝ) : |pos a - pos b| ≤ |a - b| := abs_max_sub_max_le_abs a b 0

lemma abs_pos_le (a : ℝ) : |pos a| ≤ |a| := by
  unfold pos; rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le (le_abs_self a) (abs_nonneg a)

end WFMFG410

open WFMFG410

set_option maxHeartbeats 4000000 in
theorem solution (γ' ϵ : ℝ) (hγ0 : 0 < γ') (hγ1 : γ' < 1) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1 / 4) :
    ∃ η : ℝ, 0 < η ∧
    ∀ (d : ℕ) [NeZero d] (T κ δ : ℝ), 0 < T → 0 < δ →
    ∀ φ : ℝ → ℝ, IsCutoff κ δ φ →
    ∀ U : Fin d → ℝ → (Fin d → ℝ) → ℝ, WFReg γ' T U →
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    ∀ (l : Fin N) (t : ℝ) (x : Fin N → Fin d) (y : Fin N → ℚ),
      t ∈ Set.Icc 0 T → y ∈ Yset N → TN ϵ x y →
      |driftOp φ (fun l' s x' y' => zN U l' s x' y') l t x y
          - (∑ k, ∑ j, empMeas x y k * φ (empMeas x y j)
                * (sD (U (x l) t) (empMeas x y) j - sD (U (x l) t) (empMeas x y) k)
            + ∑ k, ∑ j, empMeas x y k * pos (U k t (empMeas x y) - U j t (empMeas x y))
                * (sD (U (x l) t) (empMeas x y) j - sD (U (x l) t) (empMeas x y) k)
            + ∑ j, φ (empMeas x y j) * (U j t (empMeas x y) - U (x l) t (empMeas x y)))| ≤
        C / (N : ℝ) ^ η := by
  refine ⟨ϵ * (γ' / 2), by positivity, ?_⟩
  intro d _ T κ δ hT hδ φ hφ U hU
  obtain ⟨C9, hC9⟩ := lemma_4_9 d γ' T hγ0 hγ1 hT U hU
  obtain ⟨_, _, K, hK⟩ := hU
  obtain ⟨hφ0, hφanti, _, hφκ, _⟩ := hφ
  set K' : ℝ := |K|
  set A : ℝ := |C9|
  set M' : ℝ := A + 2 * K'
  set Q : ℝ := d * (κ * A + M' * M' + 2 * K' * A)
  set Q' : ℝ := d * (κ * (A + 4 * K') + 4 * K' * K')
  refine ⟨Q + Q', ?_⟩
  intro N hN l t x y ht hy hTN
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  set η : ℝ := ϵ * (γ' / 2) with hη
  set ν : ℝ := (N:ℝ) ^ (-η) with hν
  have hν0 : 0 ≤ ν := by positivity
  have hν1 : ν ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by nlinarith)
  have hκ0 : 0 ≤ κ := by
    have := hφκ 0 ⟨le_refl _, hδ.le⟩; rw [← this]; exact hφ0 0 (le_refl _)
  have hφb : ∀ r, 0 ≤ r → |φ r| ≤ κ := by
    intro r hr
    rw [abs_of_nonneg (hφ0 r hr)]
    have h0 := hφκ 0 ⟨le_refl _, hδ.le⟩
    rw [← h0]
    exact hφanti (Set.mem_Ici.2 (le_refl 0)) (Set.mem_Ici.2 hr) hr
  have hpos : ∀ i, 0 < empMeas x y i := fun i =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) (hTN.1 i)
  set μ := empMeas x y with hμdef
  have hμ : μ ∈ simplexInt d := by
    refine ⟨hpos, ?_⟩
    have hq : ∑ i, empQ x y i = 1 := by
      unfold empQ
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [hy.2]
      have hN' : (N:ℚ) ≠ 0 := by positivity
      field_simp
    simp only [hμdef, empMeas]
    exact_mod_cast hq
  have hK0 : 0 ≤ K' := abs_nonneg K
  have hA0 : 0 ≤ A := abs_nonneg C9
  have hUb : ∀ j, |U j t μ| ≤ K' := fun j =>
    le_trans (hK j j j t ht μ hμ μ hμ).1 (le_abs_self K)
  have hSb : ∀ i j, |sD (U i t) μ j| ≤ K' := fun i j =>
    le_trans (hK i j j t ht μ hμ μ hμ).2.1 (le_abs_self K)
  have hSd : ∀ i j k, |sD (U i t) μ j - sD (U i t) μ k| ≤ 2 * K' := by
    intro i j k
    have := abs_sub (sD (U i t) μ j) (sD (U i t) μ k)
    have := hSb i j; have := hSb i k; linarith
  have hUd : ∀ j k, |U j t μ - U k t μ| ≤ 2 * K' := by
    intro j k
    have := abs_sub (U j t μ) (U k t μ)
    have := hUb j; have := hUb k; linarith
  -- weights
  set c : Fin N → ℝ := fun m => (y m : ℝ) / N with hc
  have hc0 : ∀ m, 0 ≤ c m := fun m => by
    have : (0:ℝ) ≤ y m := by exact_mod_cast hy.1 m
    simp only [hc]; positivity
  have hcsum : ∑ m, c m = 1 := by
    simp only [hc, ← Finset.sum_div]
    have : (∑ m, (y m : ℝ)) = N := by exact_mod_cast hy.2
    rw [this, div_self hNpos.ne']
  have hcε : ∀ m, c m ≤ (N:ℝ) ^ (-ϵ) := by
    intro m
    have h1 := hTN.2 m
    have h2 : (N:ℝ) ^ (1 - ϵ) = N * (N:ℝ) ^ (-ϵ) := by
      rw [sub_eq_add_neg, Real.rpow_add hNpos, Real.rpow_one]
    simp only [hc]
    rw [div_le_iff₀ hNpos]
    have : (0:ℝ) ≤ (N:ℝ) ^ (-ϵ) := by positivity
    nlinarith
  have hεν : (N:ℝ) ^ (-ϵ) ≤ ν :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
  have hcν : ∀ m, c m ≤ ν := fun m => le_trans (hcε m) hεν
  have hcpow : ∀ m, C9 * (y m : ℝ) ^ (1 + γ' / 2) / (N : ℝ) ^ (1 + γ' / 2) ≤ A * (c m * ν) := by
    intro m
    have hym : (0:ℝ) ≤ y m := by exact_mod_cast hy.1 m
    rw [mul_div_assoc, ← Real.div_rpow hym hNpos.le]
    change C9 * c m ^ (1 + γ' / 2) ≤ _
    rw [Real.rpow_one_add' (hc0 m) (by linarith)]
    have hp : c m ^ (γ' / 2) ≤ ν := by
      calc c m ^ (γ' / 2) ≤ ((N:ℝ) ^ (-ϵ)) ^ (γ' / 2) :=
            Real.rpow_le_rpow (hc0 m) (hcε m) (by linarith)
        _ = ν := by rw [hν, hη, ← Real.rpow_mul hNpos.le]; ring_nf
    have hp0 : 0 ≤ c m ^ (γ' / 2) := Real.rpow_nonneg (hc0 m) _
    calc C9 * (c m * c m ^ (γ' / 2)) ≤ A * (c m * c m ^ (γ' / 2)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (hc0 m) hp0)
      _ ≤ A * (c m * ν) := by
          apply mul_le_mul_of_nonneg_left _ hA0
          exact mul_le_mul_of_nonneg_left hp (hc0 m)
  -- abbreviations
  set i0 := x l with hi0
  set S : Fin d → Fin d → ℝ := fun i j => sD (U i t) μ j with hS
  set D : Fin N → Fin d → ℝ := fun m j => zN U l t (Function.update x m j) y - zN U l t x y
    with hD
  set E : Fin N → Fin d → ℝ := fun m j => S i0 j - S i0 (x m) with hE
  set P : Fin N → Fin d → ℝ := fun m j => pos (U (x m) t μ - U j t μ) with hP
  set a : Fin N → Fin d → ℝ := fun m j =>
    astar (x m) (fun j' => zN U m t (Function.update x m j') y) j with ha
  set ph : Fin d → ℝ := fun j => φ (μ j) with hph
  have hphb : ∀ j, |ph j| ≤ κ := fun j => hφb _ (hpos j).le
  have hEb : ∀ m j, |E m j| ≤ 2 * K' := fun m j => hSd _ _ _
  have hPb : ∀ m j, |P m j| ≤ 2 * K' := fun m j =>
    le_trans (abs_pos_le _) (hUd _ _)
  -- the estimates from Lemma 4.9
  have hρ1 : ∀ m, m ≠ l → ∀ j, |D m j - c m * E m j| ≤ A * (c m * ν) := by
    intro m hml j
    have h := (hC9 N hN l m t x y ht hy hpos j).1 hml
    exact le_trans (le_of_eq (by simp only [hD, hE, hS, hc, hi0, hμdef])) (le_trans h (hcpow m))
  have hρ2 : ∀ j, |D l j - (U j t μ - U i0 t μ) - c l * (S j j - S j i0)| ≤ A * (c l * ν) := by
    intro j
    have h := (hC9 N hN l l t x y ht hy hpos j).2
    exact le_trans (le_of_eq (by simp only [hD, hS, hc, hi0, hμdef])) (le_trans h (hcpow l))
  have hcomp : ∀ m j, |a m j - P m j| ≤ M' * c m := by
    intro m j
    have h := (hC9 N hN m m t x y ht hy hpos j).2
    have haeq : a m j = pos (U (x m) t μ - zN U m t (Function.update x m j) y) := by
      simp only [ha, astar, Function.update_eq_self, zN, hμdef]
    rw [haeq]
    refine le_trans (pos_lip _ _) ?_
    have e : (U (x m) t μ - zN U m t (Function.update x m j) y) - (U (x m) t μ - U j t μ)
        = -((zN U m t (Function.update x m j) y - zN U m t x y
            - (U j t (empMeas x y) - U (x m) t (empMeas x y))
            - ((y m : ℝ) / N) * (sD (U j t) (empMeas x y) j - sD (U j t) (empMeas x y) (x m)))
            + c m * (S j j - S j (x m))) := by
      simp only [zN, hc, hS, hμdef]; ring
    rw [e, abs_neg]
    refine le_trans (abs_add_le _ _) ?_
    have h2 : |c m * (S j j - S j (x m))| ≤ c m * (2 * K') := by
      rw [abs_mul, abs_of_nonneg (hc0 m)]
      exact mul_le_mul_of_nonneg_left (hSd _ _ _) (hc0 m)
    have h3 : A * (c m * ν) ≤ A * c m := by
      apply mul_le_mul_of_nonneg_left _ hA0
      nlinarith [hc0 m]
    have := le_trans h (hcpow m)
    simp only [M']; nlinarith
  -- decomposition into a sum over players
  set A3 : ℝ := ∑ j, ph j * (U j t μ - U i0 t μ) with hA3
  set R : Fin N → ℝ := fun m =>
    (∑ j, ph j * D m j + (if m = l then 0 else ∑ j, a m j * D m j))
      - c m * ∑ j, ph j * E m j - c m * ∑ j, P m j * E m j
      - (if m = l then A3 else 0) with hR
  have hdrift : driftOp φ (fun l' s x' y' => zN U l' s x' y') l t x y
      - (∑ k, ∑ j, empMeas x y k * φ (empMeas x y j)
                * (sD (U (x l) t) (empMeas x y) j - sD (U (x l) t) (empMeas x y) k)
            + ∑ k, ∑ j, empMeas x y k * pos (U k t (empMeas x y) - U j t (empMeas x y))
                * (sD (U (x l) t) (empMeas x y) j - sD (U (x l) t) (empMeas x y) k)
            + ∑ j, φ (empMeas x y j) * (U j t (empMeas x y) - U (x l) t (empMeas x y)))
      = ∑ m, R m := by
    have h1 : ∑ k, ∑ j, empMeas x y k * φ (empMeas x y j)
                * (sD (U (x l) t) (empMeas x y) j - sD (U (x l) t) (empMeas x y) k)
        = ∑ m, c m * ∑ j, ph j * E m j := by
      have := sum_empMeas_mul x y (fun k => ∑ j, φ (empMeas x y j)
                * (sD (U (x l) t) (empMeas x y) j - sD (U (x l) t) (empMeas x y) k))
      simp only [Finset.mul_sum] at this
      simp only [Finset.mul_sum, ← mul_assoc] at this ⊢
      rw [this]
    have h2 : ∑ k, ∑ j, empMeas x y k * pos (U k t (empMeas x y) - U j t (empMeas x y))
                * (sD (U (x l) t) (empMeas x y) j - sD (U (x l) t) (empMeas x y) k)
        = ∑ m, c m * ∑ j, P m j * E m j := by
      have := sum_empMeas_mul x y (fun k => ∑ j, pos (U k t (empMeas x y) - U j t (empMeas x y))
                * (sD (U (x l) t) (empMeas x y) j - sD (U (x l) t) (empMeas x y) k))
      simp only [Finset.mul_sum, ← mul_assoc] at this ⊢
      rw [this]
    have h3 : ∑ j, φ (empMeas x y j) * (U j t (empMeas x y) - U (x l) t (empMeas x y))
        = ∑ m, (if m = l then A3 else 0) := by
      rw [Finset.sum_ite_eq']; simp [hA3, hph, hμdef, hi0]
    have h4 : driftOp φ (fun l' s x' y' => zN U l' s x' y') l t x y
        = ∑ m, (∑ j, ph j * D m j + (if m = l then 0 else ∑ j, a m j * D m j)) := by
      unfold driftOp
      rw [Finset.sum_add_distrib, ← Finset.filter_ne', Finset.sum_filter]
      congr 1
      apply Finset.sum_congr rfl; intro m _
      by_cases hm : m = l <;> simp [hm] <;> rfl
    rw [h1, h2, h3, h4]
    simp only [hR, Finset.sum_sub_distrib]
    ring
  rw [hdrift]
  -- per-player bounds
  have hRb : ∀ m, |R m| ≤ Q * (c m * ν) + (if m = l then Q' * ν else 0) := by
    intro m
    by_cases hml : m = l
    · subst hml
      simp only [hR, ↓reduceIte, add_zero]
      have e : (∑ j, ph j * D m j) - c m * ∑ j, ph j * E m j - c m * ∑ j, P m j * E m j - A3
          = ∑ j, (ph j * (D m j - (U j t μ - U i0 t μ) - c m * E m j) - c m * (P m j * E m j)) := by
        simp only [hA3, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
      rw [e]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hj : ∀ j, |ph j * (D m j - (U j t μ - U i0 t μ) - c m * E m j) - c m * (P m j * E m j)|
          ≤ ν * (κ * (A + 4 * K') + 4 * K' * K') := by
        intro j
        have hEE : |D m j - (U j t μ - U i0 t μ) - c m * E m j| ≤ c m * (A + 4 * K') := by
          have e2 : D m j - (U j t μ - U i0 t μ) - c m * E m j
              = (D m j - (U j t μ - U i0 t μ) - c m * (S j j - S j i0))
                + c m * (S j j - S j i0) - c m * E m j := by ring
          rw [e2]
          have h1 := hρ2 j
          have h2 : |c m * (S j j - S j i0)| ≤ c m * (2 * K') := by
            rw [abs_mul, abs_of_nonneg (hc0 m)]
            exact mul_le_mul_of_nonneg_left (hSd _ _ _) (hc0 m)
          have h3 : |c m * E m j| ≤ c m * (2 * K') := by
            rw [abs_mul, abs_of_nonneg (hc0 m)]
            exact mul_le_mul_of_nonneg_left (hEb _ _) (hc0 m)
          have h4 : A * (c m * ν) ≤ A * c m := by
            apply mul_le_mul_of_nonneg_left _ hA0; nlinarith [hc0 m]
          calc _ ≤ |(D m j - (U j t μ - U i0 t μ) - c m * (S j j - S j i0))
                + c m * (S j j - S j i0)| + |c m * E m j| := abs_sub _ _
            _ ≤ _ := by
              have := abs_add_le (D m j - (U j t μ - U i0 t μ) - c m * (S j j - S j i0))
                (c m * (S j j - S j i0))
              nlinarith
        have hPE : |c m * (P m j * E m j)| ≤ c m * (4 * K' * K') := by
          rw [abs_mul, abs_of_nonneg (hc0 m), abs_mul]
          apply mul_le_mul_of_nonneg_left _ (hc0 m)
          have := mul_le_mul (hPb m j) (hEb m j) (abs_nonneg _) (by positivity)
          linarith
        have hphE : |ph j * (D m j - (U j t μ - U i0 t μ) - c m * E m j)|
            ≤ κ * (c m * (A + 4 * K')) := by
          rw [abs_mul]
          exact mul_le_mul (hphb j) hEE (abs_nonneg _) hκ0
        have hcm := hcν m
        calc _ ≤ _ := abs_sub _ _
          _ ≤ κ * (c m * (A + 4 * K')) + c m * (4 * K' * K') := add_le_add hphE hPE
          _ = c m * (κ * (A + 4 * K') + 4 * K' * K') := by ring
          _ ≤ ν * (κ * (A + 4 * K') + 4 * K' * K') :=
              mul_le_mul_of_nonneg_right hcm (by positivity)
      refine le_trans (Finset.sum_le_sum (fun j _ => hj j)) ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have : 0 ≤ Q * (c m * ν) := by
        have : 0 ≤ Q := by simp only [Q, M']; positivity
        exact mul_nonneg this (mul_nonneg (hc0 m) hν0)
      have : (d:ℝ) * (ν * (κ * (A + 4 * K') + 4 * K' * K')) = Q' * ν := by
        simp only [Q']; ring
      linarith
    · simp only [hR, if_neg hml, sub_zero, add_zero]
      have e : (∑ j, ph j * D m j + ∑ j, a m j * D m j) - c m * ∑ j, ph j * E m j
            - c m * ∑ j, P m j * E m j
          = ∑ j, (ph j * (D m j - c m * E m j)
              + ((a m j - P m j) * D m j + P m j * (D m j - c m * E m j))) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
      rw [e]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hj : ∀ j, |ph j * (D m j - c m * E m j)
              + ((a m j - P m j) * D m j + P m j * (D m j - c m * E m j))|
          ≤ (κ * A + M' * M' + 2 * K' * A) * (c m * ν) := by
        intro j
        have h1 := hρ1 m hml j
        have hDb : |D m j| ≤ M' * c m := by
          have : |D m j| ≤ |D m j - c m * E m j| + |c m * E m j| := by
            have := abs_add_le (D m j - c m * E m j) (c m * E m j); simpa using this
          have h3 : |c m * E m j| ≤ c m * (2 * K') := by
            rw [abs_mul, abs_of_nonneg (hc0 m)]
            exact mul_le_mul_of_nonneg_left (hEb _ _) (hc0 m)
          have h4 : A * (c m * ν) ≤ A * c m := by
            apply mul_le_mul_of_nonneg_left _ hA0
            exact mul_le_of_le_one_right (hc0 m) hν1
          have h5 : M' * c m = A * c m + c m * (2 * K') := by simp only [M']; ring
          linarith
        have t1 : |ph j * (D m j - c m * E m j)| ≤ κ * (A * (c m * ν)) := by
          rw [abs_mul]; exact mul_le_mul (hphb j) h1 (abs_nonneg _) hκ0
        have t2 : |(a m j - P m j) * D m j| ≤ M' * M' * (c m * ν) := by
          rw [abs_mul]
          have hM'0 : 0 ≤ M' := by simp only [M']; linarith
          have := mul_le_mul (hcomp m j) hDb (abs_nonneg _) (mul_nonneg hM'0 (hc0 m))
          have hcc : c m * c m ≤ c m * ν := mul_le_mul_of_nonneg_left (hcν m) (hc0 m)
          have hM0 : 0 ≤ M' * M' := by positivity
          calc _ ≤ M' * c m * (M' * c m) := this
            _ = M' * M' * (c m * c m) := by ring
            _ ≤ M' * M' * (c m * ν) := mul_le_mul_of_nonneg_left hcc hM0
        have t3 : |P m j * (D m j - c m * E m j)| ≤ 2 * K' * (A * (c m * ν)) := by
          rw [abs_mul]; exact mul_le_mul (hPb m j) h1 (abs_nonneg _) (by linarith)
        calc _ ≤ |ph j * (D m j - c m * E m j)|
              + (|(a m j - P m j) * D m j| + |P m j * (D m j - c m * E m j)|) := by
              refine le_trans (abs_add_le _ _) (add_le_add (le_refl _) (abs_add_le _ _))
          _ ≤ κ * (A * (c m * ν)) + (M' * M' * (c m * ν) + 2 * K' * (A * (c m * ν))) :=
              add_le_add t1 (add_le_add t2 t3)
          _ = _ := by ring
      refine le_trans (Finset.sum_le_sum (fun j _ => hj j)) ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact le_of_eq (by simp only [Q]; ring)
  calc |∑ m, R m| ≤ ∑ m, |R m| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m, (Q * (c m * ν) + (if m = l then Q' * ν else 0)) :=
        Finset.sum_le_sum (fun m _ => hRb m)
    _ = Q * ν * (∑ m, c m) + Q' * ν := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp only [Finset.mem_univ, if_true, Finset.mul_sum]
        congr 1; apply Finset.sum_congr rfl; intro m _; ring
    _ = (Q + Q') / (N : ℝ) ^ η := by
        rw [hcsum, hν, Real.rpow_neg hNpos.le]; field_simp
