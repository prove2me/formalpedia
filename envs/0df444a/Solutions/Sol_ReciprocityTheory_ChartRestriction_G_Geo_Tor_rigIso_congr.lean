-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.rigIso_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:51.477503+00:00
-- url     : https://prove2.me/submissions/33b161e6-25ad-4c3c-9e6c-4c3886d3ce74

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr

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
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {LG PP : RigLB G} (hL : LG = PP) {PP' : RigLB G'} (m : CubeMap G' G) {c : CubicalStr G PP}
    {c' : CubicalStr G' PP'} (h : m.IsPullCubical c' c) {F : G'.left ⟶ G.left} (hF : F = m.F) {e : S' ⟶ S}
    (he : e = m.e) : ∃ (w : LB.Iso PP'.L (LG.L.pull F)) (h₀ : eSec G' ≫ F = e ≫ eSec G), w.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) PP'.rig (rigPullOf F e h₀ LG.L LG.rig) := by
  subst hL hF he
  obtain ⟨w, h₁, h₂, -⟩ := h
  exact ⟨w, m.e_comm, h₁, h₂⟩
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
