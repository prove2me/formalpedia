-- Prove2me | solution 1 for RydbergConstant.isotopic_shift
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:17:00.771982+00:00
-- url     : https://prove2.me/submissions/f19bc44d-2b55-4550-a02a-4610c1b9be00

import Mathlib
import Definitions.Def_RydbergConstant_Defs

open RydbergConstant

theorem W4a_RydbergConstant_level (K : Constants) (n : ℕ) (hn : 0 < n) (r v : ℝ)
    (horb : IsBohrOrbit K K.me n r v) :
    orbitEnergy K K.me r v = -rydbergEnergy K / (n : ℝ) ^ 2 := by
  obtain ⟨hr, hv, hF, hL⟩ := horb
  have hme := K.me_pos
  have he := K.e_pos
  have hε := K.ε0_pos
  have hh := K.h_pos
  have hc := K.c_pos
  have hpi := Real.pi_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hA : (0 : ℝ) < 4 * Real.pi * K.ε0 := by positivity
  have hF' := hF
  rw [div_eq_div_iff hr.ne' (by positivity)] at hF'
  have key1 : K.me * v ^ 2 * r * (4 * Real.pi * K.ε0) = K.e ^ 2 := by
    apply mul_right_cancel₀ hr.ne'
    linear_combination hF'
  have key2 : v * ((n : ℝ) * hbar K) * (4 * Real.pi * K.ε0) = K.e ^ 2 := by
    linear_combination key1 - v * (4 * Real.pi * K.ε0) * hL
  have hhb : 0 < hbar K := by unfold hbar; positivity
  have hv' : v = K.e ^ 2 / (4 * Real.pi * K.ε0 * ((n : ℝ) * hbar K)) := by
    rw [eq_div_iff (by positivity)]
    linear_combination key2
  have hE : orbitEnergy K K.me r v = -(K.me * v ^ 2) / 2 := by
    unfold orbitEnergy
    rw [← key1]
    field_simp
    ring
  rw [hE, hv']
  unfold rydbergEnergy rydbergInf hbar
  field_simp
  ring

theorem W4a_RydbergConstant_bohr_energy_level (K : Constants) (n : ℕ) (hn : 0 < n) (r v : ℝ)
    (horb : IsBohrOrbit K K.me n r v) :
    orbitEnergy K K.me r v = -rydbergEnergy K / (n : ℝ) ^ 2 :=
  W4a_RydbergConstant_level K n hn r v horb

theorem W4a_RydbergConstant_bohr_rydberg_formula_inf (K : Constants) (n₁ n₂ : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hne : n₁ ≠ n₂) (r₁ v₁ r₂ v₂ : ℝ)
    (h₁ : IsBohrOrbit K K.me n₁ r₁ v₁) (h₂ : IsBohrOrbit K K.me n₂ r₂ v₂) :
    (orbitEnergy K K.me r₂ v₂ - orbitEnergy K K.me r₁ v₁) / (K.h * K.c) =
        rydbergEnergy K * (1 / (K.h * K.c)) * (1 / (n₁ : ℝ) ^ 2 - 1 / (n₂ : ℝ) ^ 2) ∧
    (orbitEnergy K K.me r₂ v₂ - orbitEnergy K K.me r₁ v₁) / (K.h * K.c) =
        K.me * K.e ^ 4 / (8 * K.ε0 ^ 2 * K.h ^ 3 * K.c) *
          (1 / (n₁ : ℝ) ^ 2 - 1 / (n₂ : ℝ) ^ 2) := by
  rw [W4a_RydbergConstant_level K n₁ hn₁ r₁ v₁ h₁, W4a_RydbergConstant_level K n₂ hn₂ r₂ v₂ h₂]
  have hh := K.h_pos
  have hc := K.c_pos
  have hε := K.ε0_pos
  constructor
  · ring
  · unfold rydbergEnergy rydbergInf
    field_simp
    ring

theorem W4a_RydbergConstant_rydbergEnergy_alt (K : Constants) :
    rydbergEnergy K = 1 / 2 * K.me * K.c ^ 2 * fineStructure K ^ 2 ∧
    rydbergEnergy K = 1 / 2 * (K.e ^ 4 * K.me / ((4 * Real.pi * K.ε0) ^ 2 * hbar K ^ 2)) ∧
    rydbergEnergy K = 1 / 2 * (K.me * K.c ^ 2 * classicalElectronRadius K / bohrRadius K) ∧
    rydbergEnergy K = 1 / 2 * (K.h * K.c * fineStructure K ^ 2 / comptonWavelength K) ∧
    rydbergEnergy K = 1 / 2 * K.h * comptonFrequency K * fineStructure K ^ 2 ∧
    rydbergEnergy K = 1 / 2 * hbar K * comptonAngularFrequency K * fineStructure K ^ 2 := by
  have hme := K.me_pos.ne'
  have he := K.e_pos.ne'
  have hε := K.ε0_pos.ne'
  have hh := K.h_pos.ne'
  have hc := K.c_pos.ne'
  have hpi := Real.pi_pos.ne'
  unfold rydbergEnergy rydbergInf fineStructure hbar classicalElectronRadius bohrRadius
    comptonWavelength comptonFrequency comptonAngularFrequency
  unfold hbar comptonFrequency
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

theorem W4a_RydbergConstant_rydbergInf_alt (K : Constants) :
    rydbergInf K = fineStructure K ^ 2 * K.me * K.c / (2 * K.h) ∧
    rydbergInf K = fineStructure K ^ 2 / (2 * comptonWavelength K) ∧
    rydbergInf K = fineStructure K / (4 * Real.pi * bohrRadius K) ∧
    1 / rydbergInf K = 4 * Real.pi / fineStructure K * bohrRadius K := by
  have hme := K.me_pos.ne'
  have he := K.e_pos.ne'
  have hε := K.ε0_pos.ne'
  have hh := K.h_pos.ne'
  have hc := K.c_pos.ne'
  have hpi := Real.pi_pos.ne'
  unfold rydbergInf fineStructure hbar bohrRadius comptonWavelength
  unfold hbar
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

theorem W4a_RydbergConstant_rydbergEnergy_eq_alpha (K : Constants) :
    rydbergEnergy K = fineStructure K ^ 2 * K.me * K.c ^ 2 / 2 := by
  have hme := K.me_pos.ne'
  have he := K.e_pos.ne'
  have hε := K.ε0_pos.ne'
  have hh := K.h_pos.ne'
  have hc := K.c_pos.ne'
  have hpi := Real.pi_pos.ne'
  unfold rydbergEnergy rydbergInf fineStructure hbar
  field_simp
  ring

theorem W4a_RydbergConstant_rydbergM_forms (K : Constants) (M : ℝ) (hM : 0 < M) :
    rydbergM K M = rydbergInf K / (1 + K.me / M) ∧
    rydbergM K M = M / (K.me + M) * rydbergInf K := by
  have hme := K.me_pos
  have h1 : K.me + M ≠ 0 := by positivity
  have h2 : 1 + K.me / M ≠ 0 := by positivity
  unfold rydbergM reducedMass
  constructor <;> field_simp <;> ring

theorem solution (K : Constants) (M₁ M₂ : ℝ) (h₁ : 0 < M₁)
    (h₁₂ : M₁ < M₂) :
    rydbergM K M₁ < rydbergM K M₂ ∧ rydbergM K M₂ < rydbergInf K := by
  have hme := K.me_pos
  have h₂ : 0 < M₂ := h₁.trans h₁₂
  have hR : 0 < rydbergInf K := by
    have := K.e_pos; have := K.ε0_pos; have := K.h_pos; have := K.c_pos
    unfold rydbergInf; positivity
  rw [(W4a_RydbergConstant_rydbergM_forms K M₁ h₁).2, (W4a_RydbergConstant_rydbergM_forms K M₂ h₂).2]
  constructor
  · apply mul_lt_mul_of_pos_right _ hR
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · have : M₂ / (K.me + M₂) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    nlinarith
