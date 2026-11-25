-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.herm_cGP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:40:22.840856+00:00
-- url     : https://prove2.me/submissions/cfe8fedf-66c5-4a5c-95b4-2d8e1ddab99b

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegF
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (a b : Fin r) :
    S.c (((P.map S.c)ᵀ * S.G * P) a b) = ((P.map S.c)ᵀ * S.G * P) b a := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    S.c_invol, S.G_herm, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end ReciprocityTheory.MultiplicativeHeights.SemiPt
