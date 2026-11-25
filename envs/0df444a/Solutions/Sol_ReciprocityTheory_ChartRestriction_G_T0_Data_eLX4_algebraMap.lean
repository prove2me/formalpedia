-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.eLX4_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:58:55.992311+00:00
-- url     : https://prove2.me/submissions/4ed0237f-c689-43dd-a2c4-87e5dc7e8a28

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OffBaseSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FracFieldPositiveRowsOmega
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FractionFieldVariableLift_isFractionRing_toFracY


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (P : KTp K d.D d.N) :
    d.eLX4 (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P) =
      FractionFieldVariableLift.toFracY d.PolyRingPositiveRowsBase (Fin (d.N + 1)) (FractionFieldVariableLift.hL K d.D d.N P) := by
  letI := (FractionFieldVariableLift.toFracY d.PolyRingPositiveRowsBase (Fin (d.N + 1))).toAlgebra
  haveI := FractionFieldVariableLift.isFractionRing_toFracY (A := d.PolyRingPositiveRowsBase) (σ := Fin (d.N + 1))
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (FractionFieldVariableLift.hL K d.D d.N) P
end ReciprocityTheory.ChartRestriction.G.T0.Data
