-- Prove2me | solution 1 for OrderClosures.gaoMinimalDominators_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:42.016496+00:00
-- url     : https://prove2.me/submissions/70031c80-2469-4166-8488-7e974e408196

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution
    (ξ γ : Ordinal.{u}) (b : C(GaoCompactSpace ξ, ℝ)) :
    (gaoMinimalDominators ξ γ b).Pairwise
      (fun μ ν ↦ ¬ cnfExtensionLE μ.1 ν.1) := by
  intro μ hμ ν hν hne hμν
  exact hne (hν.2 μ hμ.1 hμν)
end OrderClosures
