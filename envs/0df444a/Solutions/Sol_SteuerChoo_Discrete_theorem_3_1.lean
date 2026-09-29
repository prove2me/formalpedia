-- Prove2me | solution 1 for SteuerChoo.Discrete.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:12:49.056061+00:00
-- url     : https://prove2.me/submissions/90c02529-24d3-4157-8b54-34490229c512

import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff

namespace SteuerChoo.Discrete

theorem aux_sc31_tcheb_mono {k : ℕ} [NeZero k] (lam zstar z w : Fin k → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hzw : ∀ i, w i ≤ z i) :
    tcheb lam zstar z ≤ tcheb lam zstar w := by
  unfold tcheb
  apply Finset.sup'_le
  intro i _
  refine le_trans ?_ (Finset.le_sup' (fun i => lam i * (zstar i - w i)) (Finset.mem_univ i))
  exact mul_le_mul_of_nonneg_left (by linarith [hzw i]) (hlam i)

end SteuerChoo.Discrete

open SteuerChoo.Discrete

theorem solution {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (hZ : Z.Nonempty)
    (lam : Fin k → ℝ) (hlam : lam ∈ stdSimplex ℝ (Fin k)) (zstar : Fin k → ℝ) :
    ∃ zbar ∈ Z, (∀ z ∈ Z, tcheb lam zstar zbar ≤ tcheb lam zstar z) ∧ zbar ∈ nondominated Z := by
  classical
  have hl : ∀ i, 0 ≤ lam i := hlam.1
  obtain ⟨z0, hz0, hmin⟩ := Finset.exists_min_image Z (fun z => tcheb lam zstar z) hZ
  set M := Z.filter (fun z => ∀ w ∈ Z, tcheb lam zstar z ≤ tcheb lam zstar w) with hM
  have hMne : M.Nonempty := ⟨z0, Finset.mem_filter.mpr ⟨hz0, hmin⟩⟩
  obtain ⟨zb, hzbM, hmax⟩ := Finset.exists_max_image M (fun z => ∑ i, z i) hMne
  rw [Finset.mem_filter] at hzbM
  obtain ⟨hzbZ, hzbmin⟩ := hzbM
  refine ⟨zb, hzbZ, hzbmin, ?_⟩
  unfold nondominated
  rw [Finset.mem_filter]
  refine ⟨hzbZ, ?_⟩
  rintro ⟨z, hzZ, hle, j, hj⟩
  have hzt : tcheb lam zstar z ≤ tcheb lam zstar zb := aux_sc31_tcheb_mono lam zstar z zb hl hle
  have hzM : z ∈ M := Finset.mem_filter.mpr ⟨hzZ, fun w hw => le_trans hzt (hzbmin w hw)⟩
  have h1 := hmax z hzM
  have h2 : ∑ i, zb i < ∑ i, z i :=
    Finset.sum_lt_sum (fun i _ => hle i) ⟨j, Finset.mem_univ j, hj⟩
  linarith
