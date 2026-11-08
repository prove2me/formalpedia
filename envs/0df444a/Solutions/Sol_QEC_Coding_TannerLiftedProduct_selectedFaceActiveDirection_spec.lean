-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.selectedFaceActiveDirection_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:08:16.653523+00:00
-- url     : https://prove2.me/submissions/8051ef50-b9ad-4f94-87cf-69f6e6cb1c19

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat)
    (v : {v // v ∈ nonactiveLabelledVertices label c m}) :
    IsFaceActiveVerticalEdgeAt label c v.1
      (selectedFaceActiveDirection label c m v) := by
  classical
  have hvData := Finset.mem_sdiff.mp v.2
  have hvIncident := labelledVertices_nonactive_incident
    label c m v.1 hvData.1 hvData.2
  exact Classical.choose_spec hvIncident
end QEC.Coding.TannerLiftedProduct
