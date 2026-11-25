-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_InterNumRestrict_proof_e88a9c0914bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:53.998919+00:00
-- url     : https://prove2.me/submissions/e37ecb37-0d1b-4509-893f-bcfb0bcec8ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PInterNumRestrict
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumRestrict_inr_foldl_restrict_0d2b71329fc0
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
theorem _root_.solution (hRL : RestrLenRestrict.Statement.{u, w}) : InterNumRestrict.Statement.{u, w} := by
  intro k _ Ω _ _ N x K' _ _ y hxy hle pp n hsub L L' rr hL
  have hT : ∀ T : Finset (Fin n), ∀ᶠ c : ℕ in atTop,
      restrLen pp ((tensorSub (fun i => (L' i).toSubSystem) T).twist (twistSys k y (c : ℤ))) =
        restrLen pp ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys k x (c : ℤ))) := by
    intro T
    obtain ⟨r0, h0⟩ := RestrictTwist.proof.1 k Ω N x K' y hxy hle 0
    obtain ⟨P, P', s, hP, hP', hs⟩ := inr_foldl_restrict L L' rr hL
      ((List.finRange n).filter (· ∈ T)) (twistBundle k x 0) (twistBundle k y 0) r0 h0
    have e1 : tensorSub (fun i => (L i).toSubSystem) T = P.toSubSystem := hP
    have e2 : tensorSub (fun i => (L' i).toSubSystem) T = P'.toSubSystem := hP'
    rw [e1, e2]
    exact hRL k Ω N x K' y hxy hle pp n hsub P P' s hs
  have hall : ∀ᶠ c : ℕ in atTop, interSum pp (fun i => (L' i).toSubSystem) c =
      interSum pp (fun i => (L i).toSubSystem) c := by
    filter_upwards [Filter.eventually_all.2 hT] with c hc
    unfold interSum
    exact Finset.sum_congr rfl fun T _ => by rw [hc T]
  unfold interNum limUnder
  rw [Filter.map_congr hall]
end GroundTheory.Heights₂.Heights.Kleiman.InterNumRestrict
