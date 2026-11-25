-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sc_col_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:05:55.831804+00:00
-- url     : https://prove2.me/submissions/f5546db3-02b3-4d86-826d-036c37e8271b

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} [Fintype ι]
    (σ : K →+* ℂ) (N : Matrix (Fin r) (Fin r) K) (c : ι → Fin r → K) :
    embCols σ (fun j => N *ᵥ c j) = N.map σ * embCols σ c := by
  ext a j
  simp [embCols, Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
end ReciprocityTheory.MultiplicativeHeights
