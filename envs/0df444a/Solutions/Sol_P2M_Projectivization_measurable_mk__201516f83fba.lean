-- Prove2me | solution 1 for P2M_Projectivization_measurable_mk__201516f83fba
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:21.887942+00:00
-- url     : https://prove2.me/submissions/4d8b8326-a524-4fc8-b74f-4e1d6bfc5615

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_Topology
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MeasureSpace

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Topology
open scoped LinearAlgebra.Projectivization
open Projectivization
variable {K V : Type*}
variable [RCLike K] [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]
omit [FiniteDimensional K V]
namespace Projectivization
theorem _root_.solution [MeasurableSpace V] [BorelSpace V] :
    Measurable (mk' K : { v : V // v ≠ 0 } → ℙ K V) :=
  continuous_mk'.measurable
end Projectivization
