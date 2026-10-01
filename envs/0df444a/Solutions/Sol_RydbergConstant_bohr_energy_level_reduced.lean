-- Prove2me | solution 1 for RydbergConstant.bohr_energy_level_reduced
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:23:02.986996+00:00
-- url     : https://prove2.me/submissions/b3fc45f6-53a5-4c9c-9b05-ddc6e1ecd13e

import Definitions.Def_RydbergConstant_Defs

set_option autoImplicit false

open RydbergConstant

private lemma energia_orbita (K : Constants) (massa : ℝ) (hmassa : 0 < massa)
    (n : ℕ) (hn : 0 < n) (r v : ℝ) (horbita : IsBohrOrbit K massa n r v) :
    orbitEnergy K massa r v = -(massa * K.e ^ 4 / (8 * K.ε0 ^ 2 * K.h ^ 2)) / (n : ℝ) ^ 2 := by
  obtain ⟨hr, hv, hforca, hquant⟩ := horbita
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have heps := K.ε0_pos
  have hh := K.h_pos
  have hpi := Real.pi_pos
  have he := K.e_pos
  have hforca' : 4 * Real.pi * K.ε0 * massa * v ^ 2 * r = K.e ^ 2 := by
    field_simp at hforca
    nlinarith
  have hquant' : 2 * Real.pi * massa * v * r = (n : ℝ) * K.h := by
    unfold hbar at hquant
    field_simp at hquant
    nlinarith
  have hvel : v = K.e ^ 2 / (2 * K.ε0 * (n : ℝ) * K.h) := by
    apply (eq_div_iff (by positivity)).2
    have hproduto := congrArg (fun z : ℝ => (2 * K.ε0 * v) * z) hquant'
    nlinarith [hforca', hproduto]
  have hpot : K.e ^ 2 / (4 * Real.pi * K.ε0 * r) = massa * v ^ 2 := by
    apply (div_eq_iff (by positivity)).2
    nlinarith [hforca']
  unfold orbitEnergy
  rw [hpot, hvel]
  field_simp
  <;> ring

theorem solution (K : Constants) (M : ℝ) (hM : 0 < M)
    (n : ℕ) (hn : 0 < n) (r v : ℝ) (horb : IsBohrOrbit K (reducedMass K M) n r v) :
    orbitEnergy K (reducedMass K M) r v = -(K.h * K.c * rydbergM K M) / (n : ℝ) ^ 2 := by
  have hm : 0 < reducedMass K M := by
    unfold reducedMass
    exact one_div_pos.mpr (add_pos (one_div_pos.mpr K.me_pos) (one_div_pos.mpr hM))
  rw [energia_orbita K (reducedMass K M) hm n hn r v horb]
  unfold rydbergM rydbergInf
  have hme := K.me_pos
  have heps := K.ε0_pos
  have hh := K.h_pos
  have hc := K.c_pos
  congr 1
  field_simp
  <;> ring
