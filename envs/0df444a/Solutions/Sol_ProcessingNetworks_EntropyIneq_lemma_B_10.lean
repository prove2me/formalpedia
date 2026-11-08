-- Prove2me | solution 1 for ProcessingNetworks.EntropyIneq.lemma_B_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:18:50.624916+00:00
-- url     : https://prove2.me/submissions/fa8cac01-c878-4fc4-b8c9-082357ef4f7a

import Mathlib
import Definitions.Def_ProcessingNetworks_EntropyIneq_SectionB4Assumptions
import Definitions.Def_ProcessingNetworks_EntropyIneq_outflow

open Matrix

open ProcessingNetworks.EntropyIneq in
theorem solution {I : ℕ} (lam : Fin I → ℝ) (P : Matrix (Fin I) (Fin I) ℝ)
    (hB4 : SectionB4Assumptions lam P) (d : Fin I → ℝ) :
    ∑ i, d i + ∑ i, lam i =
      ∑ i, traffic lam P i * (∑ j, P i j * (d j / traffic lam P j) + outflow P i) +
        ∑ i, d i * (lam i / traffic lam P i) := by
  have hpos := hB4.traffic_pos
  have hU : IsUnit (1 - P.transpose).det := by
    by_contra hne
    have h0 : traffic lam P = 0 := by
      unfold traffic
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hne, Matrix.zero_mulVec]
    have := hpos ⟨0, hB4.pos_I⟩
    rw [h0] at this
    exact lt_irrefl 0 this
  have hfix : ∀ j, ∑ i, traffic lam P i * P i j = traffic lam P j - lam j := by
    have h1 : (1 - P.transpose) *ᵥ traffic lam P = lam := by
      unfold traffic
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
    intro j
    have h2 := congrFun h1 j
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply] at h2
    have h3 : (P.transpose *ᵥ traffic lam P) j = ∑ i, traffic lam P i * P i j := by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [h3] at h2
    linarith
  have hA : ∑ i, traffic lam P i * ∑ j, P i j * (d j / traffic lam P j)
      = ∑ j, d j - ∑ j, d j * (lam j / traffic lam P j) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have e : ∑ i, traffic lam P i * (P i j * (d j / traffic lam P j))
        = (∑ i, traffic lam P i * P i j) * (d j / traffic lam P j) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e, hfix j]
    have := (hpos j).ne'
    field_simp <;> ring
  have hB : ∑ i, traffic lam P i * outflow P i = ∑ i, lam i := by
    unfold outflow
    have e : ∀ i, traffic lam P i * (1 - ∑ j, P i j)
        = traffic lam P i - ∑ j, traffic lam P i * P i j := by
      intro i; rw [mul_sub, mul_one, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_sub_distrib, Finset.sum_comm,
      Finset.sum_congr rfl (fun j _ => hfix j), Finset.sum_sub_distrib]
    ring
  have hsplit : ∑ i, traffic lam P i * (∑ j, P i j * (d j / traffic lam P j) + outflow P i)
      = ∑ i, traffic lam P i * ∑ j, P i j * (d j / traffic lam P j)
        + ∑ i, traffic lam P i * outflow P i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsplit, hA, hB]
  ring
