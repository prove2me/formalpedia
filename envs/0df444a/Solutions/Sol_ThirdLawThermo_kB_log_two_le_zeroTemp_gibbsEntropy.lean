-- Prove2me | solution 1 for ThirdLawThermo.kB_log_two_le_zeroTemp_gibbsEntropy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:13:57.388096+00:00
-- url     : https://prove2.me/submissions/6450331c-dd54-423b-a83c-e28cd10759df

import Definitions.Def_ThirdLawThermo_Defs
import Mathlib

open Filter Topology
open ThirdLawThermo

namespace LUHelp

open Classical in
theorem gibbs_limit {ι : Type*} [Fintype ι] [Nonempty ι]
    (kB : ℝ) (hkB : 0 < kB) (E : ι → ℝ) :
    Tendsto (fun T => gibbsEntropy kB E T) (𝓝[>] 0)
      (𝓝 (kB * Real.log (groundStates E).card)) := by
  set E₀ := groundEnergy E with hE₀
  set G := groundStates E with hG
  have hmemG : ∀ i, i ∈ G ↔ E i = E₀ := fun i => by
    simp [hG, groundStates, hE₀]
  have hge : ∀ i, E₀ ≤ E i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  have hGne : G.Nonempty := by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty E
    exact ⟨i, (hmemG i).2 hi.symm⟩
  set g : ℝ := (G.card : ℝ) with hg
  have hgpos : 0 < g := by
    rw [hg]; exact_mod_cast hGne.card_pos
  let f : ι → ℝ → ℝ := fun i T => Real.exp (-(E i - E₀) / (kB * T))
  let L : ι → ℝ := fun i => if i ∈ G then 1 else 0
  have hp : ∀ T i, gibbsProb kB E T i = f i T / ∑ j, f j T := by
    intro T i
    have hfac : ∀ j, Real.exp (-E j / (kB * T)) = f j T * Real.exp (-E₀ / (kB * T)) := by
      intro j
      simp only [f]
      rw [← Real.exp_add]
      congr 1
      ring
    unfold gibbsProb partitionFunction
    simp_rw [hfac]
    rw [← Finset.sum_mul, mul_div_mul_right _ _ (Real.exp_pos _).ne']
  have hf : ∀ i, Tendsto (fun T => f i T) (𝓝[>] 0) (𝓝 (L i)) := by
    intro i
    by_cases hi : i ∈ G
    · have h0 : E i - E₀ = 0 := by rw [(hmemG i).1 hi]; ring
      simp only [f, L, hi, if_true, h0, neg_zero, zero_div, Real.exp_zero]
      exact tendsto_const_nhds
    · have hd : 0 < E i - E₀ := by
        have := hge i
        have hne : E i ≠ E₀ := fun h => hi ((hmemG i).2 h)
        exact sub_pos.2 (lt_of_le_of_ne this (Ne.symm hne))
      simp only [f, L, hi, if_false]
      have h1 : Tendsto (fun T : ℝ => (E i - E₀) / kB * T⁻¹) (𝓝[>] 0) atTop :=
        tendsto_inv_nhdsGT_zero.const_mul_atTop (div_pos hd hkB)
      have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with T (hT : 0 < T)
      simp only [Function.comp]
      congr 1
      field_simp
  have hsumL : ∑ j, L j = g := by
    simp only [L]
    rw [Finset.sum_boole]
    simp [hg]
  have hsum : Tendsto (fun T => ∑ j, f j T) (𝓝[>] 0) (𝓝 g) := by
    rw [← hsumL]
    exact tendsto_finset_sum _ (fun j _ => hf j)
  have hpl : ∀ i, Tendsto (fun T => gibbsProb kB E T i) (𝓝[>] 0) (𝓝 (L i / g)) := by
    intro i
    simp_rw [hp]
    exact (hf i).div hsum hgpos.ne'
  have hent : Tendsto (fun T => gibbsEntropy kB E T) (𝓝[>] 0)
      (𝓝 (-kB * ∑ i, L i / g * Real.log (L i / g))) := by
    unfold gibbsEntropy
    apply Tendsto.const_mul
    apply tendsto_finset_sum
    intro i _
    exact (Real.continuous_mul_log.tendsto _).comp (hpl i)
  convert hent using 2
  have : ∑ i, L i / g * Real.log (L i / g) = ∑ i ∈ G, (1 / g) * Real.log (1 / g) := by
    rw [← Finset.sum_subset (Finset.subset_univ G)]
    · apply Finset.sum_congr rfl
      intro i hi
      simp [L, hi]
    · intro i _ hi
      simp [L, hi]
  rw [this, Finset.sum_const, nsmul_eq_mul, ← hg, one_div, Real.log_inv]
  field_simp

end LUHelp
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι]
    (kB : ℝ) (hkB : 0 < kB) (E : ι → ℝ) (hE : 2 ≤ (groundStates E).card) :
    ∃ S₀ : ℝ, Tendsto (fun T => gibbsEntropy kB E T) (𝓝[>] 0) (𝓝 S₀) ∧
      kB * Real.log 2 ≤ S₀ := by
  refine ⟨_, LUHelp.gibbs_limit kB hkB E, ?_⟩
  apply mul_le_mul_of_nonneg_left _ hkB.le
  apply Real.log_le_log (by norm_num)
  exact_mod_cast hE
