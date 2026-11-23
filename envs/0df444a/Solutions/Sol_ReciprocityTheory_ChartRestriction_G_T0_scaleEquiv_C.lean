-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.scaleEquiv_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:36.933739+00:00
-- url     : https://prove2.me/submissions/ad711685-0428-4587-b659-b910cd99beea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
section Scale
variable {S σ : Type*} [CommRing S]
private theorem scaleEquiv_apply' (P : σ → Prop) [DecidablePred P] (u : Sˣ)
    (p : MvPolynomial σ S) :
    scaleEquiv P u p = aeval (fun v => if P v then C (u : S) * X v else X v) p := rfl
end Scale
section Blocks
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
end Blocks
section Norm
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
end Norm
namespace Data
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (NumberField.RingOfIntegers K) (A c)]
variable (d : Data K ι Ω WT A)
end Data
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {S σ : Type*} [CommRing S]
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (P : σ → Prop) [DecidablePred P] (u : Sˣ) (a : S) :
    scaleEquiv P u (C a) = C a := by
  first
    | (rw [scaleEquiv_apply', MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]; done)
    | exact (scaleEquiv P u).commutes a
end ReciprocityTheory.ChartRestriction.G.T0
