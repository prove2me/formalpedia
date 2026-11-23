-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.wa_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:37.475741+00:00
-- url     : https://prove2.me/submissions/588e33ea-a9ee-48bc-ac16-6c1c1ec26d3b

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : S.h y x = S.c (S.h x y) := by
  unfold HermForm.h
  simp only [map_sum, map_mul, S.c_invol, S.G_herm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end ReciprocityTheory.MultiplicativeHeights
