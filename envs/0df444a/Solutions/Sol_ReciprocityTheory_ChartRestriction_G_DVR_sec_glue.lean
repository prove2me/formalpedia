-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.sec_glue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:19.320789+00:00
-- url     : https://prove2.me/submissions/a9df431c-eb5e-40b5-a83b-dd8e8ed69b3f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {Y : Scheme.{0}} (W : Y.Opens) {ι : Type} (V : ι → Y.Opens) (hle : ∀ i, V i ≤ W)
    (hcov : W ≤ ⨆ i, V i) (f : ∀ i, Γ(Y, V i))
    (hf : ∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op).hom (f i) =
      (Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op).hom (f j)) :
    ∃! g : Γ(Y, W), ∀ i, (Y.presheaf.map (homOfLE (hle i)).op).hom g = f i := by
  have := TopCat.Sheaf.existsUnique_gluing' Y.sheaf V W (fun i => homOfLE (hle i)) hcov f (fun i j => hf i j)
  exact this
end ReciprocityTheory.ChartRestriction.G.DVR
