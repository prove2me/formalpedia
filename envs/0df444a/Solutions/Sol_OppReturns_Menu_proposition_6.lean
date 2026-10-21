-- Prove2me | solution 1 for OppReturns.Menu.proposition_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:59:19.961162+00:00
-- url     : https://prove2.me/submissions/43dc02d3-cb20-4eee-809b-21d80e683f99
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OppReturns_Menu_Model
import Theorems.Thm_OppReturns_Menu_uniform_optimum_exists
import Theorems.Thm_OppReturns_Menu_proposition_5
import Theorems.Thm_OppReturns_Menu_upper_bounds
import Theorems.Thm_OppReturns_Menu_targeted_gain

open OppReturns.Menu

theorem solution (P : Params) (hS : Standing P) (hB : UniformBinds P) :
    (∃ Q p r, IsOptU P Q p r) ∧
    ∀ Q p r, IsOptU P Q p r →
      PiU P ≤ PiM P ∧ PiM P ≤ PiT P ∧
      ((PiM P < PiT P ∧ PiM P = PiU P) ↔ r < P.s) ∧
      (P.s < r → PiT P = PiM P ∧ PiU P < PiM P) ∧
      (r = P.s → PiT P = PiM P) := by
  refine ⟨uniform_optimum_exists P hS, fun Q p r hU => ?_⟩
  obtain ⟨-, -, -, hMT, hUT⟩ := upper_bounds P hS
  obtain ⟨h5a, h5b⟩ := proposition_5 P hS hB Q p r hU
  have hUM : PiU P ≤ PiM P := by
    rcases lt_or_ge r P.s with h | h
    · exact (h5a h).1.symm.le
    · rw [(h5b h).1]; exact hUT
  refine ⟨hUM, hMT, ⟨fun ⟨hlt, heq⟩ => ?_, fun h => ?_⟩, fun h => ?_, fun h => ?_⟩
  · by_contra hc
    have := (h5b (not_lt.mp hc)).1
    exact absurd this (ne_of_lt hlt)
  · have e := (h5a h).1
    exact ⟨e ▸ targeted_gain P hS Q p r hU (ne_of_lt h), e⟩
  · have e := (h5b h.le).1
    exact ⟨e.symm, e ▸ targeted_gain P hS Q p r hU (ne_of_gt h)⟩
  · exact (h5b h.ge).1.symm
