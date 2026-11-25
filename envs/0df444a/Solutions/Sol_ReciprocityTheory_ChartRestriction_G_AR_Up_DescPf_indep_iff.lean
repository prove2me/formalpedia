-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.DescPf.indep_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:48:51.958806+00:00
-- url     : https://prove2.me/submissions/d031c6a9-b672-419a-b5fb-c7077e0156f5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DescentStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DescentStatementPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DescPf
open scoped TensorProduct
open Module
variable {F F' V : Type} [Field F] [Field F'] [Algebra F F'] [AddCommGroup V] [Module F V]
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DescPf
theorem _root_.solution {ι : Type} (v : ι → V) :
    LinearIndependent F v ↔ LinearIndependent F' (fun i => (1 : F') ⊗ₜ[F] v i) := by
  constructor
  · intro hv
    exact Module.Flat.linearIndependent_one_tmul hv
  · intro h
    have h' : LinearIndependent F (fun i => (1 : F') ⊗ₜ[F] v i) :=
      h.restrict_scalars' F
    exact LinearIndependent.of_comp (TensorProduct.mk F F' V 1) h'
end ReciprocityTheory.ChartRestriction.G.AR.Up.DescPf
