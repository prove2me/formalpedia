-- Prove2me | solution 1 for Teletriage.OneShot.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T16:29:49.408312+00:00
-- url     : https://prove2.me/submissions/acb2c362-0280-4e2a-a932-6cd8c9f1426e

import Mathlib
import Definitions.Def_Teletriage_OneShot_Model
import Theorems.Thm_Teletriage_OneShot_ed_integral
import Theorems.Thm_Teletriage_OneShot_dd_integral

namespace Teletriage.OneShot.Dev

open Teletriage.OneShot

variable (P : Params)

theorem m_proposition_3 (P : Params) (hS : P.Standing) (hI : P.Informative) (l u : ℝ)
    (hl : 0 ≤ l) (hu : u ≤ 1)
    (h1 : bLow P < l) (h2 : l < b0 P) (h3 : b0 P < u) (h4 : u < bHigh P) :
    (0 < avg (piED P) l u - avg (piEDtt P) l u ↔ P.β < betaSup0 P l u) ∧
    (0 < avg (piDD P) l u - avg (piDDtt P) l u ↔ P.α < alphaSup0 P l u) := by
  obtain ⟨eE, hB⟩ := Teletriage.OneShot.ed_integral P hS hI l u hl hu h1 h2 h3 h4
  have eD := Teletriage.OneShot.dd_integral P hS hI l u hl hu h1 h2 h3 h4
  have hul : 0 < u - l := by linarith
  have hu2 : 0 < u ^ 2 - l ^ 2 := by nlinarith
  rw [eE, eD]
  unfold betaSup0 alphaSup0
  rw [div_pos_iff_of_pos_right hul, div_pos_iff_of_pos_right (by linarith),
    lt_div_iff₀ hB, lt_div_iff₀ hu2]
  constructor <;> constructor <;> intro h <;> linarith


end Teletriage.OneShot.Dev

open Teletriage.OneShot

theorem solution (P : Params) (hS : P.Standing) (hI : P.Informative) (l u : ℝ)
    (hl : 0 ≤ l) (hu : u ≤ 1)
    (h1 : bLow P < l) (h2 : l < b0 P) (h3 : b0 P < u) (h4 : u < bHigh P) :
    (0 < avg (piED P) l u - avg (piEDtt P) l u ↔ P.β < betaSup0 P l u) ∧
    (0 < avg (piDD P) l u - avg (piDDtt P) l u ↔ P.α < alphaSup0 P l u) :=
  Teletriage.OneShot.Dev.m_proposition_3 P hS hI l u hl hu h1 h2 h3 h4
