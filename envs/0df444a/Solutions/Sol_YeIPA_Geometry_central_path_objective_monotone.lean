-- Prove2me | solution 1 for YeIPA.Geometry.central_path_objective_monotone
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T11:51:09.832606+00:00
-- url     : https://prove2.me/submissions/8ea35d28-f216-4659-bf1e-3fff1fd7f1fa

import Mathlib
import Definitions.Def_YeIPA_Geometry_CentralPath

open Matrix
open YeIPA.Geometry

theorem solution : ¬ (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hrank : A.rank = m) (hmn : m < n)
    (hP : ∃ x, PrimalInterior A b x) (hD : ∃ y s, DualInterior A c y s)
    (μ' μ : ℝ) (hμ' : 0 < μ') (hμ'μ : μ' < μ)
    (x' : Fin n → ℝ) (y' : Fin m → ℝ) (s' : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ)
    (h' : IsCentralPathPoint A b c μ' x' y' s') (h : IsCentralPathPoint A b c μ x y s),
    c ⬝ᵥ x' < c ⬝ᵥ x ∧ b ⬝ᵥ y < b ⬝ᵥ y') := by
  intro H
  have hA : (0 : Matrix (Fin 0) (Fin 1) ℝ).rank = 0 := Matrix.rank_zero
  have key := @H 0 1 0 0 (fun _ => 1) hA (by norm_num)
    ⟨fun _ => 1, by ext i; exact i.elim0, fun _ => one_pos⟩
    ⟨0, fun _ => 1, by ext j; simp, fun _ => one_pos⟩
    1 2 one_pos one_lt_two
    (fun _ => 1) 0 (fun _ => 1) (fun _ => 2) 0 (fun _ => 1)
    ⟨⟨by ext i; exact i.elim0, fun _ => one_pos⟩, ⟨by ext j; simp, fun _ => one_pos⟩,
      fun _ => by norm_num⟩
    ⟨⟨by ext i; exact i.elim0, fun _ => two_pos⟩, ⟨by ext j; simp, fun _ => one_pos⟩,
      fun _ => by norm_num⟩
  exact lt_irrefl _ key.2
