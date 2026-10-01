-- Prove2me | solution 1 for RydbergConstant.bohr_rydberg_formula
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:22:59.320986+00:00
-- url     : https://prove2.me/submissions/95004c50-7308-4072-b04e-83f622d38e42

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

theorem solution (K : Constants) (M : ℝ) (hM : 0 < M) (n₁ n₂ : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hne : n₁ ≠ n₂) (r₁ v₁ r₂ v₂ : ℝ)
    (h₁ : IsBohrOrbit K (reducedMass K M) n₁ r₁ v₁)
    (h₂ : IsBohrOrbit K (reducedMass K M) n₂ r₂ v₂) :
    (orbitEnergy K (reducedMass K M) r₂ v₂ - orbitEnergy K (reducedMass K M) r₁ v₁) /
        (K.h * K.c) =
      rydbergM K M * (1 / (n₁ : ℝ) ^ 2 - 1 / (n₂ : ℝ) ^ 2) := by
  have hm : 0 < reducedMass K M := by
    unfold reducedMass
    exact one_div_pos.mpr (add_pos (one_div_pos.mpr K.me_pos) (one_div_pos.mpr hM))
  rw [energia_orbita K (reducedMass K M) hm n₁ hn₁ r₁ v₁ h₁,
    energia_orbita K (reducedMass K M) hm n₂ hn₂ r₂ v₂ h₂]
  unfold rydbergM rydbergInf
  have hme := K.me_pos
  have heps := K.ε0_pos
  have hh := K.h_pos
  have hc := K.c_pos
  have hn1 : (0 : ℝ) < n₁ := by exact_mod_cast hn₁
  have hn2 : (0 : ℝ) < n₂ := by exact_mod_cast hn₂
  field_simp
  <;> ring
