-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.mem_of_sum_single_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:31:46.25343+00:00
-- url     : https://prove2.me/submissions/ec78db7b-d7d8-44c0-b1c0-01bafd161bed

import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_MemOfSumSingleEqZero

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
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {m : ℕ} (c : Fin m → R) (r : Fin m → R)
    (h : ∑ k, r k • (Pi.single k (1 : R ⧸ Ideal.span {c k}) :
      (i : Fin m) → R ⧸ Ideal.span {c i}) = 0) : ∀ i, r i ∈ Ideal.span {c i} := by
  intro i
  have h1 := congrFun h i
  rw [Finset.sum_apply, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne' hj]) (by simp)] at h1
  simp [Algebra.smul_def] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp h1
end ReciprocityTheory.PGsh.Up
