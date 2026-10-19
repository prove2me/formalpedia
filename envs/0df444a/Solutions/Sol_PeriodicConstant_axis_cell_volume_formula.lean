-- Prove2me | solution 1 for PeriodicConstant.axis_cell_volume_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/99dbcfb1-710d-45ca-a7da-a6f3afe41544

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicConstant_axis_cell_eq_coordinate_preimage
namespace CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory
open scoped FourierTransform SchwartzMap Topology
end
noncomputable section
end
noncomputable section
open MeasureTheory
open scoped FourierTransform
end
noncomputable section
open Filter MeasureTheory
open scoped FourierTransform SchwartzMap
end
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace ENNReal NNReal
end
noncomputable section
open MeasureTheory Metric
open scoped ENNReal
end
noncomputable section
open Filter MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal
end
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace
end
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
end
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Interval Topology
end
noncomputable section
open Filter
open scoped Topology
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
end
noncomputable section
open Filter MeasureTheory
open scoped Topology
end
noncomputable section
open Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal
end
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
end
noncomputable section
end
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
end
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
end
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
end
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
end
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
end
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
end
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology
end
noncomputable section
open Filter MeasureTheory Set intervalIntegral
open scoped Topology
end
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
end
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
end
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
end
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
end
noncomputable section
open Filter Set
open scoped Topology
end
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
end
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
end
noncomputable section
open Filter
open scoped Topology
end
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology
end
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
end
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
end
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
end
noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal Interval Topology
end
noncomputable section
open Set
end
noncomputable section
open Filter
open scoped Nat Topology
end
noncomputable section
open Filter Function MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace Pointwise ContDiff
end
noncomputable section
end
noncomputable section
open Filter
open scoped Topology
end
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology
end
noncomputable section
open Filter
open scoped Topology
end
end CohnElkies
section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
section
open Metric MeasureTheory
variable {r : ℝ} {ι : Type*} [Fintype ι]
end
section
open MeasureTheory Metric Filter
open Module
open scoped BigOperators ENNReal Pointwise
section Definitions
variable {d : ℕ}
attribute [instance] PeriodicSpherePacking.lattice_discrete
attribute [instance] PeriodicSpherePacking.lattice_isZLattice
end Definitions
section Scaling
variable {d : ℕ}
open Real
end Scaling
noncomputable section Density
variable {d : ℕ} (S : SpherePacking d)
end Density
section DensityLemmas
namespace SpherePacking
end DensityLemmas.SpherePacking
section BasicResults
open scoped ENNReal
open EuclideanSpace
variable {d : ℕ} (S : SpherePacking d)
end BasicResults
end
section
end
section
namespace ENat
open Function Set
section tsum
variable {ι : Sort*} {α β : Type*} {f g : α → ℕ∞} {s t : Set α}
variable {ι : Type*}
end ENat.tsum
open Function
end
section
open ZSpan
variable {E ι K : Type*} [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [NormedAddCommGroup E] [NormedSpace K E] (b : Module.Basis ι K E) [FloorRing K] [Fintype ι]
section BasisIndexEquiv
variable {d : ℕ}
namespace ZLattice
end ZLattice
end BasisIndexEquiv
end
section
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
section aux_lemmas
variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))
end aux_lemmas
section Pointwise
open scoped Pointwise
variable {d : ℕ}
end Pointwise
section instances
variable {d : ℕ} (S : PeriodicSpherePacking d)
open scoped Pointwise
end instances
section centerOrbitCardinality
open scoped Pointwise
open Finset Set
variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))
end centerOrbitCardinality
section numReps_aux
variable {d : ℕ}
end numReps_aux
section theorem_2_3
variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))
open scoped Pointwise
end theorem_2_3
section theorem_2_2
open scoped Pointwise
variable {d : ℕ} (S : PeriodicSpherePacking d)
  {ι : Type*} [Finite ι]
  (D : Set (EuclideanSpace ℝ (Fin d))) {L : ℝ} (R : ℝ)
open ZSpan
variable (b : Basis ι ℤ S.lattice)
section finiteDensity_limit
open MeasureTheory Measure Metric ZSpan
variable
  {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)
open Filter Topology
section VolumeBallRatio
open scoped Topology NNReal
open Asymptotics Filter ENNReal EuclideanSpace
end VolumeBallRatio
end finiteDensity_limit
end theorem_2_2
end
section
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open Filter
open scoped Pointwise
open scoped Topology
variable {d : ℕ}
section DensityEqFdDensity
variable
  {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)
end DensityEqFdDensity
section ConstantEqNormalizedConstant
end ConstantEqNormalizedConstant
section Disjoint_Covering_of_Centers
end Disjoint_Covering_of_Centers
section Fundamental_Domains_in_terms_of_Basis
open Submodule
variable (S : PeriodicSpherePacking d) (b : Basis (Fin d) ℤ S.lattice)
end Fundamental_Domains_in_terms_of_Basis
section Periodic_Density_Formula
end Periodic_Density_Formula
section Empty_Centers
end Empty_Centers
end
section
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
section PeriodicConstantAux
open MeasureTheory Metric EuclideanSpace
open scoped Pointwise
variable {d : ℕ}
end PeriodicConstantAux
section PeriodicConstantCube
open scoped Pointwise
variable {d : ℕ}
end PeriodicConstantCube
section Periodic_Constant_Eq_Constant
open scoped Pointwise
namespace PeriodicConstant
variable {d : ℕ}
private lemma coordinate_preimage_volume (s : Set (Fin d → ℝ)) (hs : MeasurableSet s) :
    volume ((fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹' s) = volume s := by
  simpa using! (PiLp.volume_preserving_ofLp (ι := Fin d)).measure_preimage hs.nullMeasurableSet
end PeriodicConstant
section PeriodicConstantApprox
open scoped Pointwise
open MeasureTheory Metric
namespace PeriodicConstantApprox
variable {d : ℕ}
end PeriodicConstantApprox
end PeriodicConstantApprox
end Periodic_Constant_Eq_Constant
end
section
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise Topology
variable {d : ℕ}
namespace PeriodicConstantApprox
section CoordCubeCover
open Metric
variable (L : ℝ) (hL : 0 < L)
end CoordCubeCover
section CoverVolumeBound
open scoped BigOperators
end CoverVolumeBound
section BoundaryControl
open scoped ENNReal Pointwise BigOperators
variable (S : SpherePacking d)
end BoundaryControl
end PeriodicConstantApprox
namespace SpherePacking
open Filter
variable {d : ℕ}
end SpherePacking
namespace PeriodicConstantApprox
open Filter
variable {d : ℕ}
section BoundaryControlShellVec
open scoped ENNReal Pointwise BigOperators
open SpherePacking EuclideanSpace MeasureTheory Metric
variable {d : ℕ}
variable (S : SpherePacking d)
end BoundaryControlShellVec
section CubeLatticeCovolume
open scoped ENNReal
open ZSpan
end CubeLatticeCovolume
section PeriodizeCubeDensity
open scoped ENNReal Pointwise
open SpherePacking EuclideanSpace MeasureTheory Metric Bornology
variable {d : ℕ}
end PeriodizeCubeDensity
end PeriodicConstantApprox
namespace SpherePacking
open Filter
open scoped ENNReal BigOperators
variable {d : ℕ}
end SpherePacking
end
section
open scoped BigOperators Real
open MeasureTheory
namespace SchwartzMap.UnitAddTorus
end SchwartzMap.UnitAddTorus
end
section
namespace SpherePacking.ForMathlib.Fourier
open scoped FourierTransform
open MeasureTheory
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
end SpherePacking.ForMathlib.Fourier
end
section
open scoped BigOperators
open MeasureTheory
namespace SchwartzMap
variable {d : ℕ}
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
section StandardLattice
namespace referenceIntegerLattice
end StandardLattice.referenceIntegerLattice
section PoissonSummation
namespace PoissonSummation
namespace Standard
end SchwartzMap.PoissonSummation.PoissonSummation.Standard
namespace SchwartzMap
open TopologicalSpace MeasureTheory
variable {d : ℕ}
namespace PoissonSummation.Standard
open UnitAddTorus
end SchwartzMap.PoissonSummation.Standard
namespace SchwartzMap
variable {d : ℕ}
namespace PoissonSummation.Standard
open UnitAddTorus
end SchwartzMap.PoissonSummation.Standard
end
section
open scoped BigOperators FourierTransform
open MeasureTheory
namespace SchwartzMap.PoissonSummation.Standard
variable {d : ℕ}
open UnitAddTorus
variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
end SchwartzMap.PoissonSummation.Standard
namespace SchwartzMap.PoissonSummation.Standard
variable {d : ℕ}
open UnitAddTorus
variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
end SchwartzMap.PoissonSummation.Standard
end
section
open scoped BigOperators FourierTransform Real
open MeasureTheory Module
namespace SchwartzMap
variable {d : ℕ}
section FundamentalDomain
end FundamentalDomain
section CovolumeDet
variable (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]
end CovolumeDet
section PoissonSummationLattices
variable (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]
end SchwartzMap.PoissonSummationLattices
end
section
variable {d : ℕ} [Fact (0 < d)]
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
noncomputable section
open scoped BigOperators FourierTransform
namespace SchwartzMap
section FourierSchwartz
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
  (f : 𝓢(V, E))
end FourierSchwartz
end SchwartzMap
section Positivity_on_Nhd
variable {E : Type*} [TopologicalSpace E]
open MeasureTheory
variable [MeasureSpace E] [BorelSpace E]
end Positivity_on_Nhd
section Integration
open MeasureTheory Filter
variable {E : Type*} [NormedAddCommGroup E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [MeasureSpace E] [BorelSpace E]
variable [(volume : Measure E).IsAddLeftInvariant] [(volume : Measure E).Regular]
  [NeZero (volume : Measure E)]
end Integration
section Misc
omit [Fact (0 < d)]
end Misc
end
end
section
open scoped RealInnerProductSpace
open Module
namespace SpherePacking.CohnElkies
variable {d : ℕ}
end SpherePacking.CohnElkies
end
section
open scoped SchwartzMap
open scoped FourierTransform
open BigOperators
namespace SpherePacking.CohnElkies
variable {d : ℕ}
namespace LPBoundAux
section ZLatticeSummability
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]
end SpherePacking.CohnElkies.LPBoundAux.ZLatticeSummability
end
section
open scoped Real
open scoped SchwartzMap FourierTransform
namespace SpherePacking.CohnElkies
end SpherePacking.CohnElkies
end
section
open scoped BigOperators FourierTransform SchwartzMap Real
open Complex MeasureTheory
namespace SpherePacking.CohnElkies
variable {d : ℕ}
end SpherePacking.CohnElkies
end
section
open scoped BigOperators
open scoped SchwartzMap
namespace SpherePacking.CohnElkies
variable {d : ℕ}
namespace LPBoundSummability
open SpherePacking.CohnElkies.LPBoundAux
section ZLattice
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]
variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (a : EuclideanSpace ℝ (Fin d))
end SpherePacking.CohnElkies.LPBoundSummability.ZLattice
end
section
namespace SpherePacking.CohnElkies
noncomputable section
open scoped BigOperators SchwartzMap
variable {d : ℕ}
end
end SpherePacking.CohnElkies
end
section
open scoped BigOperators SchwartzMap
namespace SpherePacking.CohnElkies
variable {d : ℕ}
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)}
section FundamentalDomain
variable {P : PeriodicSpherePacking d}
variable {D : Set (EuclideanSpace ℝ (Fin d))}
end FundamentalDomain
end SpherePacking.CohnElkies
end
section
open scoped FourierTransform ENNReal SchwartzMap BigOperators
open SpherePacking MeasureTheory Complex Real Bornology Module
variable {d : ℕ}
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} (hne_zero : f ≠ 0)
variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))
variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)
section Complex_Function_Helpers
end Complex_Function_Helpers
section Nonnegativity
end Nonnegativity
section Fundamental_Domain_Dependent
variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)
end Fundamental_Domain_Dependent
section Main_Theorem_For_One_Packing
variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ P hP D hD_isBounded
  hD_unique_covers
end Main_Theorem_For_One_Packing
section Main_Theorem
include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂
end Main_Theorem
end
end
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped FourierTransform SchwartzMap Topology
namespace PackingBounds.RadialMain
end PackingBounds.RadialMain
end
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric
open scoped ENNReal FourierTransform SchwartzMap Topology
namespace PackingBounds.PackingBridge
end PackingBounds.PackingBridge
end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap Topology
namespace PackingBounds
end PackingBounds
end
end
noncomputable section
open scoped FourierTransform Real Topology
namespace SpherePacking.Alternative
end SpherePacking.Alternative
end
noncomputable section
open Set Matrix MeasureTheory
namespace SpherePacking.Alternative
end SpherePacking.Alternative
end
noncomputable section
open Filter MeasureTheory
open scoped ContDiff Topology
namespace SpherePacking.Alternative
end SpherePacking.Alternative
end
noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Real Topology
namespace SpherePacking.Alternative
end SpherePacking.Alternative
namespace SpherePacking.Alternative
section ProbabilityAverage
variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α) [IsProbabilityMeasure μ]
variable {d : ℕ} (g : α → Schwartz d) (C : ℕ → ℕ → ℝ)
end ProbabilityAverage
end SpherePacking.Alternative
end
noncomputable section
open MeasureTheory
open scoped Topology
namespace SpherePacking.Alternative
end SpherePacking.Alternative
end
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace SpherePacking.Alternative
end SpherePacking.Alternative
end
noncomputable section
open MeasureTheory
open scoped FourierTransform Topology
namespace SpherePacking.Alternative
end SpherePacking.Alternative
end
noncomputable section
open MeasureTheory
open scoped FourierTransform Real Topology
namespace SpherePacking.Alternative
end SpherePacking.Alternative
end
noncomputable section
open Filter MeasureTheory
open scoped FourierTransform Real Topology
namespace SpherePacking.Alternative
end SpherePacking.Alternative
end
section
namespace CohnElkies
open Real
end CohnElkies
end
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace CohnElkies
end CohnElkies
end
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
end CohnElkies
end
noncomputable section
open MeasureTheory
open scoped FourierTransform Real Topology
namespace SpherePacking.Alternative
end SpherePacking.Alternative
namespace SpherePacking.Alternative
end SpherePacking.Alternative
namespace SpherePacking.Alternative
end SpherePacking.Alternative
end
noncomputable section
open Filter
open scoped FourierTransform SchwartzMap Topology
namespace PackingBounds
namespace FullMain
end FullMain
end PackingBounds
end
noncomputable section
open Filter
open scoped Topology
namespace PackingBounds
end PackingBounds
end
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise
open PeriodicConstant
variable {d : ℕ}
namespace PeriodicConstant
theorem _root_.solution (L : ℝ) :
    volume (axisAlignedCell (d := d) L) = (ENNReal.ofReal L) ^ d := by
  have hmeas : MeasurableSet (Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ) L) := by
    simpa using! (MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Ico)
  have hpre :
      volume (axisAlignedCell (d := d) L) =
        volume (Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ) L) := by
    simpa [axis_cell_eq_coordinate_preimage (d := d) (L := L)] using!
      (coordinate_preimage_volume (d := d) (s := Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ) L) hmeas)
  rw [hpre, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico, sub_zero]
end PeriodicConstant
