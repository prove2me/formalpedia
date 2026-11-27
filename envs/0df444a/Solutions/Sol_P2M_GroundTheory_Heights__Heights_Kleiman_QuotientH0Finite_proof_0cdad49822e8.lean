-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Finite_proof_0cdad49822e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:02:27.128777+00:00
-- url     : https://prove2.me/submissions/9ce50d3b-01af-428b-83be-5c585d263429

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotientH0FiniteHypothesesLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanishCech
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_FiniteHZeroOfExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_finite_H_zero_of_exact_4a1baee195e4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w v₁ v₂ v₃
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace QuotientH0Finite
theorem _root_.solution : QuotientH0Finite.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ F G hGF hF hG
  have key := Cech.finite_H_zero_of_exact (A := fun I => ↥(G.sub I)) (B := fun I => ↥(F.sub I))
    (C := fun I => ↥(F.sub I) ⧸ SubSystem.quotSub F G I) G.res F.res (SubSystem.quotRes F G)
    (fun _ _ _ _ _ _ => rfl)
    (fun I => { toFun := fun y => ⟨y, hGF I y.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl })
    (fun I => (SubSystem.quotSub F G I).mkQ) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun I a b hab => Subtype.ext (congrArg (fun y : F.sub I => (y : E)) hab))
    (fun I => Submodule.mkQ_surjective _)
    (fun I b => ⟨fun h => ⟨⟨b, (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F G I)).mp h⟩, rfl⟩,
      fun ⟨a, ha⟩ => (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F G I)).mpr (ha ▸ a.2)⟩)
    hF hG
  exact key
end QuotientH0Finite
end GroundTheory.Heights₂.Heights.Kleiman
