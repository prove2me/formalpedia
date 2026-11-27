-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyKaehlerFree_proof_c4ee53097b0f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:58:22.127569+00:00
-- url     : https://prove2.me/submissions/71516722-1f3e-4a02-85c0-a3535fa2e8bb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyKaehlerFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolyKaehlerFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open KaehlerDifferential TensorProduct
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace PolyKaehlerFree
theorem _root_.solution : PolyKaehlerFree.Statement := by
  intro R k _ _ _ n
  set B := MvPolynomial (Fin n) k

  have hinj : Function.Injective (mapBaseChange R k B) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R k B x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  have hex := exact_mapBaseChange_map R k B

  obtain ⟨l, hl⟩ := Module.projective_lifting_property ((map R k B B).restrictScalars B)
    LinearMap.id (map_surjective R k B)
  let e := ((hex.splitSurjectiveEquiv hinj) ⟨l, hl⟩).1
  have : Module.Free B Ω[B⁄k] := Module.Free.of_basis (mvPolynomialBasis k (Fin n))
  exact Module.Free.of_equiv e.symm
end PolyKaehlerFree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
