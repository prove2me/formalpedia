-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_homog_varMono_d425fcc92f17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:35:43.851378+00:00
-- url     : https://prove2.me/submissions/7c3521e6-b746-468b-a550-fef9b485fd77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsLocalizationConeVarMap
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_homog_X_910d45ab2133
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_homog_pow_a41869706b16


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]
variable {P W}
namespace GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
theorem _root_.solution (v : ∀ k, ι k) (e : K →₀ ℕ) : IsMultiHomog (varMono v e : MRing ι) ⇑e := by
  classical
  have h : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, v k⟩ : MRing ι) ^ e k)
      (∑ k ∈ s, e k • (Pi.single k 1 : K → ℕ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (homog_one (ι := ι))
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact homog_mul (homog_pow (homog_X k (v k)) (e k)) ih
  have e' : (∑ k, e k • (Pi.single k 1 : K → ℕ)) = ⇑e := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have := h Finset.univ
  rwa [e'] at this
end GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
