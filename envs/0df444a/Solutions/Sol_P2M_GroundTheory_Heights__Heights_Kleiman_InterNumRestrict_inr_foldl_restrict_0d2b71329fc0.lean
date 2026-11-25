-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_InterNumRestrict_inr_foldl_restrict_0d2b71329fc0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:33:57.84655+00:00
-- url     : https://prove2.me/submissions/e38c9e1e-1540-4a2d-8b91-dc0cc610347f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PInterNumRestrict
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_proof_16e6dc336e3c


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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.InterNumRestrict
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {K' : Type w} [Field K'] [Algebra k K'] {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}
namespace GroundTheory.Heights₂.Heights.Kleiman.InterNumRestrict
theorem _root_.solution {n : ℕ} (L : Fin n → LineBundle k x) (L' : Fin n → LineBundle k y)
    (rr : Fin n → Ω → K') (hL : ∀ i, RestrictData (L i).toSubSystem hxy (L' i).toSubSystem (rr i)) :
    ∀ (l : List (Fin n)) (Q : LineBundle k x) (Q' : LineBundle k y) (r : Ω → K'),
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r →
      ∃ (P : LineBundle k x) (P' : LineBundle k y) (s : Ω → K'),
        l.foldl (fun F i => F.twist (L i).toSubSystem) Q.toSubSystem = P.toSubSystem ∧
        l.foldl (fun F i => F.twist (L' i).toSubSystem) Q'.toSubSystem = P'.toSubSystem ∧
        RestrictData P.toSubSystem hxy P'.toSubSystem s
  | [], Q, Q', r, h => ⟨Q, Q', r, rfl, rfl, h⟩
  | i :: l, Q, Q', r, h => by
    obtain ⟨s, hs⟩ := RestrictTwist.proof.2 k Ω N x K' y hxy Q (L i) Q' (L' i) r (rr i) h (hL i)
    exact solution L L' rr hL l (Q.tensorProd (L i)) (Q'.tensorProd (L' i)) s hs
end GroundTheory.Heights₂.Heights.Kleiman.InterNumRestrict
