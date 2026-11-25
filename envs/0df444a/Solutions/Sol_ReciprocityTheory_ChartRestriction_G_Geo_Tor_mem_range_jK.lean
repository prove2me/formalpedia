-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_range_jK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:04:13.9868+00:00
-- url     : https://prove2.me/submissions/32463ce4-b789-4950-b4f4-ddf9ee45a51f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {k : Type} [Field k] (x : Sp (PowerSeries k)) (hx : PowerSeries.X ∉ x.asIdeal) :
    x ∈ Set.range (Out.jK (PowerSeries k)) := by
  have hXu : ¬ IsUnit (PowerSeries.X : PowerSeries k) := by
    intro hu
    first
      | (have h1 := hu.map (PowerSeries.constantCoeff k); simp at h1)
      | (have h1 := hu.map (PowerSeries.constantCoeff (R := k)); simp at h1)
  have hbot : x.asIdeal = ⊥ := by
    by_contra hne
    have hmax : x.asIdeal.IsMaximal := x.isPrime.isMaximal hne
    apply hx
    rw [IsLocalRing.eq_maximalIdeal hmax, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hXu
  have hx' : x ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))) := by
    rw [PrimeSpectrum.localization_comap_range (FractionRing (PowerSeries k))
      (nonZeroDivisors (PowerSeries k))]
    show Disjoint _ _
    rw [hbot, Set.disjoint_left]
    intro a ha ha'
    exact nonZeroDivisors.ne_zero ha ((Submodule.mem_bot _).1 ha')
  obtain ⟨y, hy⟩ := hx'
  exact ⟨y, hy⟩
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
