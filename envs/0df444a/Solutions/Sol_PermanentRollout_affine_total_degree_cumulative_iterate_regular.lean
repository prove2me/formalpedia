-- Prove2me | solution 1 for PermanentRollout.affine_total_degree_cumulative_iterate_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/280a631c-4a96-476b-a399-465ba885e51d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_affine_total_degree_filtered_bot_finrank
import Theorems.Thm_PermanentRollout_affine_cumulative_iterate_le_degree_product
import Theorems.Thm_PermanentRollout_affine_total_degree_hilbert_mono
import Theorems.Thm_PermanentRollout_affine_total_degree_hilbert_regular_step

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (I : ℕ → Ideal (MvPolynomial ι ℂ))
    (g : ℕ → MvPolynomial ι ℂ)
    (n : ℕ)
    (hzero : I 0 = ⊥)
    (hnext : ∀ i, i < n →
      I (i + 1) = I i ⊔ Ideal.span ({g i} : Set (MvPolynomial ι ℂ)))
    (hregular : ∀ i, i < n →
      IsSMulRegular (MvPolynomial ι ℂ ⧸ I i) (g i))
    (M : ℕ) :
    (affineCumulative^[n]) (affineTotalDegreeHilbert (I n)) M ≤
      (∏ i ∈ Finset.range n, (g i).totalDegree) *
        (M + Fintype.card ι).choose (Fintype.card ι) := by
  have hbound := affine_cumulative_iterate_le_degree_product
    (fun i => affineTotalDegreeHilbert (I i))
    (fun i => (g i).totalDegree) n
    (fun i _ => affine_total_degree_hilbert_mono (I i))
    (by
      intro i hi m
      rw [hnext i hi]
      exact affine_total_degree_hilbert_regular_step
        (I i) (g i) (hregular i hi) m)
    M
  have hbase :
      affineTotalDegreeHilbert (I 0) M =
        (M + Fintype.card ι).choose (Fintype.card ι) := by
    rw [hzero]
    exact affine_total_degree_filtered_bot_finrank M
  rwa [hbase] at hbound
end PermanentRollout
