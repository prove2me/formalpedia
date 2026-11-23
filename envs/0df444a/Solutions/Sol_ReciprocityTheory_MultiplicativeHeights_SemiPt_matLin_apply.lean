-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.matLin_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:27.38742+00:00
-- url     : https://prove2.me/submissions/3f2ac47b-abce-4e0c-8be1-dbe384728f33

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegG
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegT

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ}
    (Q : Matrix (Fin r) (Fin r) K) (x : Fin r → K) : matLin Q x = Q *ᵥ x := rfl
end ReciprocityTheory.MultiplicativeHeights.SemiPt
