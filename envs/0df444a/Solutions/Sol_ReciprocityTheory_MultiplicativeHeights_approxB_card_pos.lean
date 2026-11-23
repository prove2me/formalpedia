-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_card_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:17.331713+00:00
-- url     : https://prove2.me/submissions/05812d7c-7341-4ec2-9397-dd3079485052

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA

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
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r p : ℕ} (hp : p ≤ r) : Fintype.card (ApproxPosIdx r p) = p := by
  let e : ApproxPosIdx r p ≃ Fin p :=
    { toFun := fun j => ⟨j.1, j.2⟩
      invFun := fun i => ⟨⟨i, lt_of_lt_of_le i.2 hp⟩, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_fin]
end ReciprocityTheory.MultiplicativeHeights
