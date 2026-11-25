-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.tauF_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:31:21.481191+00:00
-- url     : https://prove2.me/submissions/ca7a0c91-2691-46d6-8d0d-0cbaddea4c66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_scaleEquiv_C
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
end Scale
section Blocks
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
end Blocks
section Norm
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
private theorem tauF_algebraMap' (b : Fin (D + 1)) (u : Kˣ)
    (q : MvPolynomial (SVar D N) Ω) :
    tauF (Ω := Ω) (D := D) (N := N) b u (algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) q) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
        (scaleEquiv (InBlock b) (Units.map (algebraMap K Ω).toMonoidHom u) q) := by
  unfold tauF
  first
    | (rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]; rfl)
    | exact IsLocalization.ringEquivOfRingEquiv_eq _ _
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
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (b : Fin (D + 1)) (u : Kˣ) (r : Ω) :
    tauF (Ω := Ω) (D := D) (N := N) b u (algebraMap Ω (OmS Ω D N) r) =
      algebraMap Ω (OmS Ω D N) r := by
  have h1 : algebraMap Ω (OmS Ω D N) r =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (MvPolynomial.C r) := by
    first
      | exact IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) (OmS Ω D N) r
      | rfl
  rw [h1, tauF_algebraMap', scaleEquiv_C]
end ReciprocityTheory.ChartRestriction.G.T0
