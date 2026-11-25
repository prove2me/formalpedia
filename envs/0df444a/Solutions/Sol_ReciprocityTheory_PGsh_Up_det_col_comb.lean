-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.det_col_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:45:30.72715+00:00
-- url     : https://prove2.me/submissions/d4f20458-3cc9-4f29-8741-d83a5bde7b0c

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (i₀ : Fin n)
    (c₀ : R) (β : Fin n → R) :
    (A.updateCol i₀
      (fun k => c₀ * A k i₀ - ∑ i ∈ Finset.univ.erase i₀, β i * A k i)).det = c₀ * A.det := by
  have e : (fun k => c₀ * A k i₀ - ∑ i ∈ Finset.univ.erase i₀, β i * A k i) =
      fun k => ∑ i, (if i = i₀ then c₀ else -β i) • A k i := by
    funext k
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), if_pos rfl, smul_eq_mul, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_neg (Finset.ne_of_mem_erase hi), smul_eq_mul, neg_mul]
  rw [e, Matrix.det_updateCol_sum, if_pos rfl, smul_eq_mul]
end ReciprocityTheory.PGsh.Up
