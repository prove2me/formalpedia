-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_image_exps_fbf5ec376f1c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:01:25.722928+00:00
-- url     : https://prove2.me/submissions/1ccd4ae3-6ccb-413c-9ea3-840caef60f93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_sum_expToInt_3adccb6b246c

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
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
variable {S : Type u} [CommRing S] {N : ℕ}
attribute [local instance] algP
namespace GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
theorem _root_.solution (c : ℤ) :
    expToInt N '' {d | Finsupp.weight (fun _ : Fin (N + 1) => (1 : ℤ)) d = c} = laurentExps N c ∅ := by
  ext a
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨(sum_expToInt d).trans hd, fun j _ => by simp [expToInt]⟩
  · rintro ⟨hs, hnn⟩
    have ha : expToInt N (Finsupp.equivFunOnFinite.symm fun j => (a j).toNat) = a := by
      funext j; simp [expToInt, Int.toNat_of_nonneg (hnn j (Finset.notMem_empty j))]
    refine ⟨Finsupp.equivFunOnFinite.symm fun j => (a j).toNat, ?_, ha⟩
    change _ = c
    rw [← sum_expToInt, ha, hs]
end GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
