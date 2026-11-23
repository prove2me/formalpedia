-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.blk_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:55.093181+00:00
-- url     : https://prove2.me/submissions/aca2d4e7-b6f6-49b6-a1ef-7299f6b83ab4

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_ParAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW Matrix
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
variable {K : Type} [CommRing K] {M : ℕ}
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution {a b c d a' b' c' d' : K} {r s u w r' s' u' w' : Fin M → K} {U U' : Matrix (Fin M) (Fin M) K}
    (h : blk a b r c d s u w U = blk a' b' r' c' d' s' u' w' U') :
    a = a' ∧ b = b' ∧ r = r' ∧ c = c' ∧ d = d' ∧ s = s' ∧ u = u' ∧ w = w' ∧ U = U' :=
  ⟨congrFun (congrFun h 0) 0, congrFun (congrFun h 0) 1, funext fun j => congrFun (congrFun h 0) j.succ.succ,
    congrFun (congrFun h 1) 0, congrFun (congrFun h 1) 1, funext fun j => congrFun (congrFun h 1) j.succ.succ,
    funext fun i => congrFun (congrFun h i.succ.succ) 0, funext fun i => congrFun (congrFun h i.succ.succ) 1,
    Matrix.ext fun i j => congrFun (congrFun h i.succ.succ) j.succ.succ⟩
end PositivityTheory.PlacePermOperatorBicommutantSpan
