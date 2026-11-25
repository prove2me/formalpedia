-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_tensorSub_9c5ba360f068
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:32:47.634889+00:00
-- url     : https://prove2.me/submissions/019e8555-8a3f-4cb7-aaf7-7247c2b22f7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_twistSys_73f82ae90cab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_twist_0c712aa04adf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial Kleiman
open scoped Pointwise
noncomputable section
variable {S : Type*} [CommRing S] {O : Type*} [CommRing O] [Algebra S O] {Ω : Type*} [Field Ω]
  [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
theorem _root_.solution {n : ℕ} (L : Fin n → SubSystem S x Ω) (T : Finset (Fin n)) :
    tensorSub (fun i => (L i).baseChange O) T = (tensorSub L T).baseChange O := by
  have key : ∀ (l : List (Fin n)) (F : SubSystem S x Ω),
      l.foldl (fun G i => G.twist ((L i).baseChange O)) (F.baseChange O) =
        (l.foldl (fun G i => G.twist (L i)) F).baseChange O := by
    intro l
    induction l with
    | nil => intro F; rfl
    | cons a l ih =>
      intro F
      rw [List.foldl_cons, List.foldl_cons, ← baseChange_twist, ih]
  unfold tensorSub
  rw [← baseChange_twistSys (S := S) (O := O) 0]
  exact key _ _
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
