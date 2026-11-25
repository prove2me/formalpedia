-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_De_eq_zero_of_semiPos_off_f1c76f1ce662
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:18:13.28501+00:00
-- url     : https://prove2.me/submissions/b9ecf101-71d0-412a-bd92-c754abe9c315

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_DeEqZeroOfSemiPosOff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_De_eq_zero_of_semiPos_5482b118f49c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSmoothHerm_tensor


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {n : ℕ}
  {A A' : HermLine ι} {s s' : MRing ι}
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (hAdd : DeSlotAdd.Statement) (hTw : SemiPosTwist.Statement)
    (hLe : DeLeSemiPos.Statement) (hP : IsArithVar P (n + 2)) (hA : IsSmoothHerm A)
    (hA' : IsSmoothHerm A') (hs : IsSectionOn P A s) (hs' : IsSectionOn P A' s')
    (hnc : ∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) (S : Finset (Fin n)) :
    ∀ L : Fin n → HermLine ι, (∀ j, IsSmoothHerm (L j)) → (∀ j, j ∉ S → IsSemiPosHerm (L j)) →
      De P L A A' s s' = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    intro L hL hLp
    exact De_eq_zero_of_semiPos hLe hP hL (fun j => hLp j (Finset.notMem_empty j)) hA hA' hs hs' hnc
  | @insert j S hj ih =>
    intro L hL hLp
    obtain ⟨T, hT, hTp, hLTp⟩ := hTw K ι (L j) (hL j)
    have hadd := hAdd K ι P n L j (L j) T A A' s s' hP hL (hL j) hT hA hA' hs hs' hnc
    rw [Function.update_eq_self] at hadd
    have hsm : ∀ X : HermLine ι, IsSmoothHerm X → ∀ i, IsSmoothHerm (Function.update L j X i) := by
      intro X hX i
      rcases eq_or_ne i j with rfl | hij
      · simpa using hX
      · rw [Function.update_of_ne hij]
        exact hL i
    have hpos : ∀ X : HermLine ι, IsSemiPosHerm X → ∀ i, i ∉ S →
        IsSemiPosHerm (Function.update L j X i) := by
      intro X hX i hi
      rcases eq_or_ne i j with rfl | hij
      · simpa using hX
      · rw [Function.update_of_ne hij]
        exact hLp i (by simp [Finset.mem_insert, hij, hi])
    rw [ih _ (hsm _ (isSmoothHerm_tensor (hL j) hT)) (hpos _ hLTp),
      ih _ (hsm _ hT) (hpos _ hTp)] at hadd
    linarith
end GroundTheory.Heights₂.Heights.Inter
