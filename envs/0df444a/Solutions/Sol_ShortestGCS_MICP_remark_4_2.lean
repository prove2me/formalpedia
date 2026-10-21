-- Prove2me | solution 1 for ShortestGCS.MICP.remark_4_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:09:08.335685+00:00
-- url     : https://prove2.me/submissions/a97ac29f-2aa6-4823-8527-24f2d42c6d2d

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective

set_option autoImplicit false
open Pointwise ShortestGCS.MICP

theorem solution {n : ℕ} (X : Set (Fin n → ℝ)) (hclosed : IsClosed X)
    (hbdd : Bornology.IsBounded X) :
    perspectiveSet X = {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2 ∧ q.1 ∈ q.2 • X} := by
  unfold perspectiveSet
  apply IsClosed.closure_eq
  apply isClosed_of_closure_subset
  intro q hq
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hq
  obtain ⟨R, hR⟩ := hbdd.exists_norm_le
  have hu' : ∀ k, 0 ≤ (u k).2 ∧ ∃ b ∈ X, (u k).2 • b = (u k).1 := by
    intro k
    obtain ⟨h1, h2⟩ := hu k
    exact ⟨h1, by simpa [Set.mem_smul_set] using h2⟩
  have hl : Filter.Tendsto (fun k => (u k).2) Filter.atTop (nhds q.2) :=
    (continuous_snd.tendsto q).comp hlim
  have hx : Filter.Tendsto (fun k => (u k).1) Filter.atTop (nhds q.1) :=
    (continuous_fst.tendsto q).comp hlim
  have hq2 : 0 ≤ q.2 := ge_of_tendsto' hl (fun k => (hu' k).1)
  refine ⟨hq2, ?_⟩
  obtain ⟨b0, hb0, _⟩ := (hu' 0).2
  rcases hq2.eq_or_lt with h0 | hpos
  · -- λ = 0
    have hx0 : q.1 = 0 := by
      have hz : Filter.Tendsto (fun k => (u k).1) Filter.atTop (nhds 0) := by
        apply squeeze_zero_norm (a := fun k => (u k).2 * R)
        · intro k
          obtain ⟨hk, b, hb, hbk⟩ := hu' k
          rw [← hbk, norm_smul, Real.norm_of_nonneg hk]
          exact mul_le_mul_of_nonneg_left (hR b hb) hk
        · have := hl.mul_const R
          rw [← h0] at this
          simpa using this
      exact tendsto_nhds_unique hx hz
    rw [← h0, Set.zero_smul_set ⟨b0, hb0⟩, hx0]
    simp
  · -- λ > 0
    have hev : ∀ᶠ k in Filter.atTop, 0 < (u k).2 := hl.eventually (lt_mem_nhds hpos)
    have hb : Filter.Tendsto (fun k => (u k).2⁻¹ • (u k).1) Filter.atTop (nhds (q.2⁻¹ • q.1)) :=
      (hl.inv₀ hpos.ne').smul hx
    have hmem : q.2⁻¹ • q.1 ∈ X := by
      refine hclosed.mem_of_tendsto hb ?_
      filter_upwards [hev] with k hk
      obtain ⟨_, b, hbX, hbk⟩ := hu' k
      rw [← hbk, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
      exact hbX
    rw [Set.mem_smul_set]
    exact ⟨_, hmem, by rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]⟩
