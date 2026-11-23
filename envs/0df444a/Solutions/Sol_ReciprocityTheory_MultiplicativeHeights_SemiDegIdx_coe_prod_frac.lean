-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.coe_prod_frac
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:44.522841+00:00
-- url     : https://prove2.me/submissions/ca3c939e-7b18-439e-8cd2-094d7a7a8e3d

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCD
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors Pointwise
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] {k : ℕ}
    (F : Fin k → FractionalIdeal (𝓞 K)⁰ K) :
    ((∏ i, F i : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = ∏ i, (F i : Submodule (𝓞 K) K) :=
  map_prod (FractionalIdeal.coeSubmoduleHom (𝓞 K)⁰ K) F Finset.univ
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
