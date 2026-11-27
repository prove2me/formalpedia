-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_TheoremTLower_proof_40036f6145c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:09:24.253738+00:00
-- url     : https://prove2.me/submissions/f8279021-fdb2-480a-b14e-190a886d081b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_StatementsEnd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_ExistsDominantSubSmul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_exists_dominant_sub_smul_52005d976b5b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.TheoremB
namespace TheoremTLower
theorem _root_.solution (hL : LimitTheorem.Statement) : TheoremTLower.Statement := by
  intro d S u g B0 hyp _ hI1 hI2
  obtain ⟨C3, s0, hs0, hb⟩ := hI2
  obtain ⟨s1, hs1, hdom⟩ := exists_dominant_sub_smul d u S.shiftW hyp.1
  have key := hL (Idx d) (S.Ptwo B0) (fun p => (u p : ℝ)) (fun p => (S.shiftW p : ℝ))
    (S.Mbar B0 u) C3 (min s0 s1) (lt_min hs0 hs1) (by
      intro s hs hsle
      have h := hb s hs (le_trans hsle (min_le_left _ _))
        (hdom s hs (le_trans hsle (min_le_right _ _)))
      have hfun : (fun o : Option (Idx d) => o.elim (s : ℝ) (fun p => ((u - s • S.shiftW) p : ℝ))) =
          (fun o : Option (Idx d) => o.elim (s : ℝ) (fun p => (u p : ℝ) - s * (S.shiftW p : ℝ))) := by
        funext o
        cases o with
        | none => rfl
        | some p => simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rwa [hfun] at h)
  unfold bigP
  rw [← hI1 u]
  exact key
end TheoremTLower
end GroundTheory.Heights₂.Heights.TheoremB
