-- Prove2me | solution 1 for RegularSingular.norm_sum_shifted_sub_sum_reindexed_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9f4886b7-2fd5-501b-b3f2-4c3e88fe29cf

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RegularSingular_norm_sum_shifted_sub_sum_reindexed_le

namespace RegSingShiftFoldSol

open Finset

theorem rpow_mul_abs_log_pow_le {y δ : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) (hδ : 0 < δ) (j : ℕ) :
    y ^ δ * |Real.log y| ^ j ≤ (((j : ℝ) + 1) / δ) ^ j := by
  have hlog : Real.log y ≤ 0 := Real.log_nonpos hy0.le hy1
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity

  set s : ℝ := δ * (-Real.log y) / ((j : ℝ) + 1) with hs
  have hs0 : 0 ≤ s := by
    have : 0 ≤ -Real.log y := by linarith
    positivity
  have habs : |Real.log y| = (((j : ℝ) + 1) / δ) * s := by
    rw [abs_of_nonpos hlog, hs]
    field_simp
  have hyδ : y ^ δ = Real.exp (-(((j : ℝ) + 1) * s)) := by
    rw [Real.rpow_def_of_pos hy0]
    congr 1
    rw [hs]
    field_simp
  have hsexp : s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  have hC : (0 : ℝ) ≤ (((j : ℝ) + 1) / δ) ^ j := by positivity
  calc y ^ δ * |Real.log y| ^ j
      = Real.exp (-(((j : ℝ) + 1) * s)) * ((((j : ℝ) + 1) / δ) ^ j * s ^ j) := by
        rw [hyδ, habs, mul_pow]
    _ ≤ Real.exp (-(((j : ℝ) + 1) * s)) * ((((j : ℝ) + 1) / δ) ^ j * Real.exp s ^ j) := by
        gcongr
    _ = (((j : ℝ) + 1) / δ) ^ j * Real.exp (-s) := by
        rw [← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add]
        congr 2
        ring
    _ ≤ (((j : ℝ) + 1) / δ) ^ j * 1 := by
        gcongr
        exact Real.exp_le_one_iff.mpr (by linarith)
    _ = (((j : ℝ) + 1) / δ) ^ j := mul_one _

theorem norm_cpow_mul_log_pow_le {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ)
    (μ : ℂ) (hμ : ρ + 2 * δ ≤ μ.re) (j : ℕ) :
    ‖(y : ℂ) ^ μ * ((Real.log y : ℝ) : ℂ) ^ j‖ ≤ (((j : ℝ) + 1) / δ) ^ j * y ^ (ρ + δ) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hy0]
  have h1 : y ^ μ.re ≤ y ^ (ρ + 2 * δ) := Real.rpow_le_rpow_of_exponent_ge hy0 hy1 hμ
  have h2 : y ^ (ρ + 2 * δ) = y ^ (ρ + δ) * y ^ δ := by
    rw [show ρ + 2 * δ = (ρ + δ) + δ by ring, Real.rpow_add hy0]
  calc y ^ μ.re * |Real.log y| ^ j ≤ y ^ (ρ + 2 * δ) * |Real.log y| ^ j := by gcongr
    _ = y ^ (ρ + δ) * (y ^ δ * |Real.log y| ^ j) := by rw [h2, mul_assoc]
    _ ≤ y ^ (ρ + δ) * (((j : ℝ) + 1) / δ) ^ j := by
        gcongr
        exact rpow_mul_abs_log_pow_le hy0 hy1 hδ j
    _ = (((j : ℝ) + 1) / δ) ^ j * y ^ (ρ + δ) := mul_comm _ _

theorem sum_comm_four {α β γ κ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype κ]
    {N : Type*} [AddCommMonoid N] (g : α → β → γ → κ → N) :
    ∑ p, ∑ q, ∑ a, ∑ i, g p q a i = ∑ a, ∑ i, ∑ q, ∑ p, g p q a i := by
  calc ∑ p, ∑ q, ∑ a, ∑ i, g p q a i
      = ∑ p, ∑ a, ∑ q, ∑ i, g p q a i := Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ a, ∑ p, ∑ q, ∑ i, g p q a i := Finset.sum_comm
    _ = ∑ a, ∑ p, ∑ i, ∑ q, g p q a i :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ p, ∑ q, g p q a i := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ q, ∑ p, g p q a i :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem fold_sub_reindexed_eq {n J D : ℕ} (e : Fin n → ℂ) (he : Function.Injective e)
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (c : ℂ → Fin J → ℂ) (v : Fin D → Fin n → Fin J → E) (sh : Fin D → ℂ) :
    (∑ a : Fin D, ∑ i : Fin n, ∑ j : Fin J, c (e i + sh a) j • v a i j) -
        ∑ i' : Fin n, ∑ j : Fin J, c (e i') j •
          (∑ a : Fin D, ∑ i : Fin n, if e i + sh a = e i' then v a i j else 0)
      = ∑ a : Fin D, ∑ i : Fin n, ∑ j : Fin J,
          if ∃ i', e i' = e i + sh a then (0 : E) else c (e i + sh a) j • v a i j := by

  have hB : (∑ i' : Fin n, ∑ j : Fin J, c (e i') j •
        (∑ a : Fin D, ∑ i : Fin n, if e i + sh a = e i' then v a i j else 0))
      = ∑ a : Fin D, ∑ i : Fin n, ∑ j : Fin J,
          if ∃ i', e i' = e i + sh a then c (e i + sh a) j • v a i j else 0 := by
    calc (∑ i' : Fin n, ∑ j : Fin J, c (e i') j •
            (∑ a : Fin D, ∑ i : Fin n, if e i + sh a = e i' then v a i j else 0))
        = ∑ i' : Fin n, ∑ j : Fin J, ∑ a : Fin D, ∑ i : Fin n,
            (if e i + sh a = e i' then c (e i') j • v a i j else 0) := by
          refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          split_ifs <;> simp
      _ = ∑ a : Fin D, ∑ i : Fin n, ∑ j : Fin J, ∑ i' : Fin n,
            (if e i + sh a = e i' then c (e i') j • v a i j else 0) :=
          sum_comm_four (fun i' j a i => if e i + sh a = e i' then c (e i') j • v a i j else 0)
      _ = _ := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => ?_
          by_cases h : ∃ i', e i' = e i + sh a
          · obtain ⟨i₀, hi₀⟩ := h
            rw [if_pos ⟨i₀, hi₀⟩, Finset.sum_eq_single i₀]
            · rw [if_pos hi₀.symm, hi₀]
            · intro b _ hb
              rw [if_neg]
              intro hb'
              exact hb (he (hb'.symm.trans hi₀.symm))
            · intro hi₀'
              exact absurd (Finset.mem_univ i₀) hi₀'
          · rw [if_neg h]
            refine Finset.sum_eq_zero fun i' _ => ?_
            rw [if_neg]
            intro h'
            exact h ⟨i', h'.symm⟩
  rw [hB, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

end RegSingShiftFoldSol

open RegSingShiftFoldSol in

theorem solution
    {n J : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hcl : ∀ i (k : ℕ), (e i + k).re ≤ ρ → ∃ i', e i' = e i + k)
    (hgap : ∀ i (k : ℕ), ρ < (e i + k).re → ρ + 2 * δ ≤ (e i + k).re)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (d₂ : ℕ) (v : Fin (d₂ + 1) → Fin n → Fin J → E) (M : ℝ) (hM : ∀ a i j, ‖v a i j‖ ≤ M)
    (y : ℝ) (hy : y ∈ Set.Ioc (0 : ℝ) 1) :
    ‖(∑ a : Fin (d₂ + 1), ∑ i : Fin n, ∑ j : Fin J,
          ((y : ℂ) ^ (e i + (a : ℕ)) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • v a i j) -
        ∑ i' : Fin n, ∑ j : Fin J, ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) •
          (∑ a : Fin (d₂ + 1), ∑ i : Fin n, if e i + (a : ℕ) = e i' then v a i j else 0)‖ ≤
      (((d₂ : ℝ) + 1) * n * M * ∑ j : Fin J, (((j : ℝ) + 1) / δ) ^ (j : ℕ)) * y ^ (ρ + δ) := by
  obtain ⟨hy0, hy1⟩ := hy

  have hfold : (∑ a : Fin (d₂ + 1), ∑ i : Fin n, ∑ j : Fin J,
          ((y : ℂ) ^ (e i + (a : ℕ)) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • v a i j) -
        ∑ i' : Fin n, ∑ j : Fin J, ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) •
          (∑ a : Fin (d₂ + 1), ∑ i : Fin n, if e i + (a : ℕ) = e i' then v a i j else 0)
      = ∑ a : Fin (d₂ + 1), ∑ i : Fin n, ∑ j : Fin J,
          if ∃ i', e i' = e i + (a : ℕ) then (0 : E) else
            ((y : ℂ) ^ (e i + (a : ℕ)) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • v a i j :=
    fold_sub_reindexed_eq e he (fun μ (j : Fin J) => (y : ℂ) ^ μ * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))
      v (fun a : Fin (d₂ + 1) => ((a : ℕ) : ℂ))
  rw [hfold]

  have hterm : ∀ (a : Fin (d₂ + 1)) (i : Fin n) (j : Fin J),
      ‖(if ∃ i', e i' = e i + (a : ℕ) then (0 : E) else
          ((y : ℂ) ^ (e i + (a : ℕ)) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • v a i j)‖
        ≤ M * ((((j : ℕ) : ℝ) + 1) / δ) ^ (j : ℕ) * y ^ (ρ + δ) := by
    intro a i j
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a i j)
    split_ifs with h
    · rw [norm_zero]
      positivity
    ·
      have hre : ρ + 2 * δ ≤ (e i + ((a : ℕ) : ℂ)).re := by
        refine hgap i (a : ℕ) ?_
        by_contra hle
        exact h (hcl i (a : ℕ) (not_lt.mp hle))
      rw [norm_smul]
      calc ‖(y : ℂ) ^ (e i + ((a : ℕ) : ℂ)) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)‖ * ‖v a i j‖
          ≤ (((((j : ℕ) : ℝ) + 1) / δ) ^ (j : ℕ) * y ^ (ρ + δ)) * M := by
            gcongr ?_ * ?_
            · exact norm_cpow_mul_log_pow_le hy0 hy1 hδ ρ _ hre (j : ℕ)
            · exact hM a i j
        _ = M * ((((j : ℕ) : ℝ) + 1) / δ) ^ (j : ℕ) * y ^ (ρ + δ) := by ring

  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun a _ => norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i _ => norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i _ =>
    Finset.sum_le_sum fun j _ => hterm a i j).trans ?_
  have hj : ∑ j : Fin J, M * ((((j : ℕ) : ℝ) + 1) / δ) ^ (j : ℕ) * y ^ (ρ + δ)
      = M * (∑ j : Fin J, ((((j : ℕ) : ℝ) + 1) / δ) ^ (j : ℕ)) * y ^ (ρ + δ) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, hj, nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  apply le_of_eq
  ring

end S_RegularSingular_norm_sum_shifted_sub_sum_reindexed_le
end P2MW
export P2MW.S_RegularSingular_norm_sum_shifted_sub_sum_reindexed_le (solution)
