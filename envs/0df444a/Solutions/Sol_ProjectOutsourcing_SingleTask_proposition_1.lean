-- Prove2me | solution 1 for ProjectOutsourcing.SingleTask.proposition_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T22:54:37.188833+00:00
-- url     : https://prove2.me/submissions/ae3b8bcc-8345-4d63-86ea-2fa8c6952ef9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ProjectOutsourcing_SingleTask_Setting
import Theorems.Thm_ProjectOutsourcing_SingleTask_prop1_fp_tfplus
import Theorems.Thm_ProjectOutsourcing_SingleTask_prop1_tb
import Theorems.Thm_ProjectOutsourcing_SingleTask_prop1_tf_cs
import Theorems.Thm_ProjectOutsourcing_SingleTask_prop1_costplus

open ProjectOutsourcing.SingleTask

theorem solution (M : Model) (hM : M.Valid) (rStar : ℝ) (hr : IsSystemOpt M rStar) :
    -- FP and TF+
    Phi M .FP = {1} ∧ Phi M .TFplus = {1} ∧
      (∀ x, IsNashSol M .FP 1 x → x.1.1 = M.Q) ∧
      (∀ x, IsNashSol M .TFplus 1 x → x.1 = (M.Q, 0)) ∧
      -- TB: the set of θ with θΠ* a value of δ^TB_S on [0, ∞), equal to the printed interval
      -- [δ̲^TB_S/Π*, 1] when the minimum in (4) is attained
      Phi M .TB =
        {θ | θ ∈ Set.Icc 0 1 ∧ ∃ β, 0 ≤ β ∧ deltaTB M rStar β = θ * sysProfit M rStar} ∧
      (∀ β₀, 0 ≤ β₀ → IsMinOn (deltaTB M rStar) (Set.Ici 0) β₀ →
        Phi M .TB = Set.Icc (deltaTB M rStar β₀ / sysProfit M rStar) 1) ∧
      (∀ θ ∈ Phi M .TB, ∀ x, IsNashSol M .TB θ x →
        0 ≤ x.1.2 ∧ deltaTB M rStar x.1.2 = θ * sysProfit M rStar ∧
          x.1.1 = M.alpha * discZ M M.alpha rStar /
            ((M.alpha + x.1.2) * discZ M (M.alpha + x.1.2) rStar) * M.Q) ∧
      -- TF and CS
      Phi M .TF = Set.Icc 0 1 ∧ Phi M .CS = Set.Icc 0 1 ∧
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ x, IsNashSol M .TF θ x →
        x.1 = (M.Q, -(1 - θ) * sysProfit M rStar)) ∧
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ x, IsNashSol M .CS θ x → x.1 = (θ * M.Q, 1 - θ)) ∧
      -- C+
      Phi M .Cplus = {0} ∧ (∀ x, IsNashSol M .Cplus 0 x → x.1 = (0, 1)) ∧
      -- outside Φ^m no bargaining solution coordinates (FP, TF+, TB)
      (∀ m ∈ ({.FP, .TFplus, .TB} : Set Form), ∀ θ ∈ Set.Icc (0 : ℝ) 1, θ ∉ Phi M m →
        ∀ x, IsNashSol M m θ x → ¬ IsSystemOpt M x.2) := by
  obtain ⟨hFP, hTFp, hFPsol, hTFpsol, hFPno, hTFpno⟩ := prop1_fp_tfplus M hM
  obtain ⟨hTB1, hTB2, hTB3, hTB4⟩ := prop1_tb M hM rStar hr
  obtain ⟨hTF, hCS, hTFsol, hCSsol⟩ := prop1_tf_cs M hM rStar hr
  obtain ⟨hCp, hCpsol⟩ := prop1_costplus M hM
  refine ⟨hFP, hTFp, hFPsol, hTFpsol, hTB1, hTB2, hTB3, hTF, hCS, hTFsol, hCSsol, hCp, hCpsol, ?_⟩
  intro m hm θ hθ hnot x hx
  have hlt : θ ∈ Set.Icc (0:ℝ) 1 → θ ≠ 1 → θ ∈ Set.Ico (0:ℝ) 1 := fun h h1 =>
    ⟨h.1, lt_of_le_of_ne h.2 h1⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with rfl | rfl | rfl
  · rw [hFP] at hnot
    exact hFPno θ (hlt hθ hnot) x hx
  · rw [hTFp] at hnot
    exact hTFpno θ (hlt hθ hnot) x hx
  · exact hTB4 θ hθ hnot x hx
