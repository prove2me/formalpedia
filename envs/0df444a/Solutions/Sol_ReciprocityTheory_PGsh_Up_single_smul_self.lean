-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.single_smul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:40:04.302497+00:00
-- url     : https://prove2.me/submissions/aaabaa39-c7f6-4593-8e75-1359e98ea9b7

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
theorem _root_.solution {m : ℕ} (c : Fin m → R) (i : Fin m) :
    c i • (Pi.single i (1 : R ⧸ Ideal.span {c i}) : (i : Fin m) → R ⧸ Ideal.span {c i}) = 0 := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
  · simp [Pi.single_eq_of_ne hk]
end ReciprocityTheory.PGsh.Up
