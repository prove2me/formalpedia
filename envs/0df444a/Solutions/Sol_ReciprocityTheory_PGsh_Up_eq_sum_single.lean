-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.eq_sum_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:40:02.973921+00:00
-- url     : https://prove2.me/submissions/d1622525-018d-4df6-a5e9-759e95743a26

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
theorem _root_.solution {m : ℕ} (c : Fin m → R) (x : (i : Fin m) → R ⧸ Ideal.span {c i}) :
    x = ∑ i, (Quotient.out (x i) : R) • (Pi.single i (1 : R ⧸ Ideal.span {c i}) :
      (i : Fin m) → R ⧸ Ideal.span {c i}) := by
  funext k
  rw [Finset.sum_apply, Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_eq_of_ne' hj]) (by simp)]
  simp [Algebra.smul_def]
end ReciprocityTheory.PGsh.Up
