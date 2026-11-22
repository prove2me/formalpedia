-- Prove2me | solution 1 for P2M_Projectivization_borel_eq_map_mk__60a95bc3fc91
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:49.881802+00:00
-- url     : https://prove2.me/submissions/ddfc0328-c76c-40fd-a442-8e71d506efa1

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
namespace Projectivization
theorem _root_.solution :
    MeasurableSpace.map
      (mk' K : { v : V // v ≠ 0 } → ℙ K V)
      (borel _) = borel (ℙ K V) := by
  have : ProperSpace V := FiniteDimensional.proper_rclike K V
  have : PolishSpace V := inferInstance
  have : PolishSpace ({ v : V // v ≠ 0 }) :=
    isClosed_singleton.isOpen_compl.polishSpace
  exact continuous_mk'.map_borel_eq Quot.mk_surjective
end Projectivization
