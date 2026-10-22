-- Prove2me | solution 1 for WFMFG.Conv.lemma_4_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T16:47:21.845208+00:00
-- url     : https://prove2.me/submissions/f116dae0-5229-428b-ba93-993ead398fb5

import Mathlib
import Definitions.Def_WFMFG_Conv_Simplex
import Definitions.Def_WFMFG_Conv_Multinomial
import Definitions.Def_WFMFG_Conv_Setting
import Theorems.Thm_WFMFG_Conv_lemma_4_9

open Finset WFMFG.Conv

namespace WFMFG411

lemma pos_sq_sub (a b : ℝ) : |pos a ^ 2 - pos b ^ 2| ≤ |a - b| * (|a| + |b|) := by
  have h1 : |pos a - pos b| ≤ |a - b| := abs_max_sub_max_le_abs a b 0
  have ha : |pos a| ≤ |a| := by
    unfold pos; rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self a) (abs_nonneg a)
  have hb : |pos b| ≤ |b| := by
    unfold pos; rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self b) (abs_nonneg b)
  rw [sq_sub_sq, abs_mul, mul_comm]
  have := abs_add_le (pos a) (pos b)
  exact mul_le_mul h1 (by linarith) (abs_nonneg _) (abs_nonneg _)

end WFMFG411

open WFMFG411

theorem solution (d : ℕ) [NeZero d] (γ' T : ℝ) (hγ0 : 0 < γ') (hγ1 : γ' < 1) (hT : 0 < T)
    (U : Fin d → ℝ → (Fin d → ℝ) → ℝ) (hU : WFReg γ' T U) :
    ∃ C : ℝ, ∀ ϵ : ℝ, 0 < ϵ → ϵ < 1 / 4 → ∀ N : ℕ, 1 ≤ N →
    ∀ (l : Fin N) (t : ℝ) (x : Fin N → Fin d) (y : Fin N → ℚ),
      t ∈ Set.Icc 0 T → y ∈ Yset N → TN ϵ x y →
      |ham (x l) (fun j => zN U l t (Function.update x l j) y)
          - ham (x l) (fun j => U j t (empMeas x y))| ≤
        C * (y l : ℝ) / N := by
  obtain ⟨C9, hC9⟩ := lemma_4_9 d γ' T hγ0 hγ1 hT U hU
  obtain ⟨_, _, K, hK⟩ := hU
  set M : ℝ := |C9| + 2 * |K| with hM
  refine ⟨d * M * (4 * |K| + M), ?_⟩
  intro ϵ hϵ0 _ N hN l t x y ht hy hTN
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hpos : ∀ i, 0 < empMeas x y i := fun i =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) (hTN.1 i)
  set μ := empMeas x y with hμdef
  have hμ : μ ∈ simplexInt d := by
    refine ⟨hpos, ?_⟩
    -- sum of the empirical measure is one
    have hq : ∑ i, empQ x y i = 1 := by
      unfold empQ
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [hy.2]
      have hN' : (N:ℚ) ≠ 0 := by positivity
      field_simp
    simp only [hμdef, empMeas]
    exact_mod_cast hq
  set c : ℝ := (y l : ℝ) / N with hc
  have hyl : (0:ℝ) ≤ y l := by exact_mod_cast hy.1 l
  have hc0 : 0 ≤ c := by positivity
  have hylN : (y l : ℝ) ≤ N := by
    have h1 : y l ≤ ∑ m, y m :=
      Finset.single_le_sum (fun m _ => hy.1 m) (Finset.mem_univ l)
    rw [hy.2] at h1
    exact_mod_cast h1
  have hc1 : c ≤ 1 := by rw [hc, div_le_one hNpos]; exact hylN
  -- componentwise estimate
  set u : Fin d → ℝ := fun j => zN U l t (Function.update x l j) y with hu
  set v : Fin d → ℝ := fun j => U j t μ with hv
  have hvb : ∀ j, |v j| ≤ |K| := fun j =>
    le_trans (hK j j j t ht μ hμ μ hμ).1 (le_abs_self K)
  have hdiff : ∀ j, |u j - v j| ≤ M * c := by
    intro j
    have h49 := (hC9 N hN l l t x y ht hy hpos j).2
    have hsD : |c * (sD (U j t) μ j - sD (U j t) μ (x l))| ≤ c * (2 * |K|) := by
      rw [abs_mul, abs_of_nonneg hc0]
      apply mul_le_mul_of_nonneg_left _ hc0
      have h1 := (hK j j j t ht μ hμ μ hμ).2.1
      have h2 := (hK j (x l) j t ht μ hμ μ hμ).2.1
      have := abs_sub (sD (U j t) μ j) (sD (U j t) μ (x l))
      have := le_abs_self K
      linarith
    have hrem : C9 * (y l : ℝ) ^ (1 + γ' / 2) / (N : ℝ) ^ (1 + γ' / 2) ≤ |C9| * c := by
      rw [mul_div_assoc, ← Real.div_rpow hyl hNpos.le, ← hc,
        Real.rpow_one_add' hc0 (by linarith)]
      have hp : c ^ (γ' / 2) ≤ 1 := Real.rpow_le_one hc0 hc1 (by linarith)
      have hp0 : 0 ≤ c ^ (γ' / 2) := Real.rpow_nonneg hc0 _
      calc C9 * (c * c ^ (γ' / 2)) ≤ |C9| * (c * c ^ (γ' / 2)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |C9| * (c * 1) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left hp hc0
        _ = |C9| * c := by ring
    have hzx : zN U l t x y = U (x l) t μ := rfl
    have e : u j - v j = (zN U l t (Function.update x l j) y - zN U l t x y
          - (U j t (empMeas x y) - U (x l) t (empMeas x y))
          - ((y l : ℝ) / N) * (sD (U j t) (empMeas x y) j - sD (U j t) (empMeas x y) (x l)))
          + c * (sD (U j t) μ j - sD (U j t) μ (x l)) := by
      simp only [hu, hv, hzx, hc, hμdef]; ring
    rw [e]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ |C9| * c + c * (2 * |K|) := add_le_add (le_trans h49 hrem) hsD
      _ = M * c := by rw [hM]; ring
  have hM0 : 0 ≤ M := by positivity
  have hux : u (x l) = v (x l) := by
    simp [hu, hv, zN, hμdef]
  have hub : ∀ j, |u j| ≤ |K| + M := by
    intro j
    have h1 := hdiff j
    have h2 := hvb j
    have : |u j| ≤ |u j - v j| + |v j| := by
      have := abs_add_le (u j - v j) (v j); simpa using this
    have : M * c ≤ M := by nlinarith
    linarith
  -- Hamiltonian difference
  have hterm : ∀ j, |pos (u (x l) - u j) ^ 2 - pos (v (x l) - v j) ^ 2|
      ≤ (M * c) * (4 * |K| + M) := by
    intro j
    refine le_trans (pos_sq_sub _ _) ?_
    have hab : |(u (x l) - u j) - (v (x l) - v j)| ≤ M * c := by
      rw [hux]
      have : (v (x l) - u j) - (v (x l) - v j) = -(u j - v j) := by ring
      rw [this, abs_neg]; exact hdiff j
    have ha : |u (x l) - u j| ≤ 2 * |K| + M := by
      rw [hux]
      have := abs_sub (v (x l)) (u j)
      have := hvb (x l); have := hub j; linarith
    have hb : |v (x l) - v j| ≤ 2 * |K| := by
      have := abs_sub (v (x l)) (v j)
      have := hvb (x l); have := hvb j; linarith
    apply mul_le_mul hab (by linarith) (by positivity) (by positivity)
  have hham : ham (x l) u - ham (x l) v
      = -(1 / 2) * ∑ j, (pos (u (x l) - u j) ^ 2 - pos (v (x l) - v j) ^ 2) := by
    unfold ham; rw [Finset.sum_sub_distrib]; ring
  change |ham (x l) u - ham (x l) v| ≤ _
  rw [hham, abs_mul]
  have hs : |∑ j, (pos (u (x l) - u j) ^ 2 - pos (v (x l) - v j) ^ 2)|
      ≤ d * ((M * c) * (4 * |K| + M)) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun j _ => hterm j)) ?_
    simp
  have : |(-(1:ℝ) / 2)| = 1 / 2 := by norm_num
  rw [show (-(1:ℝ) / 2) = -(1/2) by ring] at this
  rw [this]
  have hfin : d * M * (4 * |K| + M) * (y l : ℝ) / N = d * ((M * c) * (4 * |K| + M)) := by
    rw [hc]; ring
  rw [hfin]
  have hnn : 0 ≤ d * ((M * c) * (4 * |K| + M)) := by positivity
  linarith
