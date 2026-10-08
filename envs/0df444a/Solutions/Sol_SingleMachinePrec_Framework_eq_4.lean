-- Prove2me | solution 1 for SingleMachinePrec.Framework.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T02:34:41.200747+00:00
-- url     : https://prove2.me/submissions/88561199-18e3-4436-adc5-7db21ea8ef52

import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_Poset

open SingleMachinePrec.Framework Classical in
theorem solution {N : Type*} [Fintype N] (P : N → N → Prop) (k t : ℕ)
    (L : Fin t → LinearExtension P) (hL : IsKFoldRealizer P k t L) (u : IncPair P) :
    (k : ℝ) / t ≤ (1 / (t : ℝ)) * (Finset.univ.filter (fun i => (L i).Reverses u)).card := by
  have h := hL.2 u
  rw [div_eq_mul_one_div, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast h
