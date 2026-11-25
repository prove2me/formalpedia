-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_spreadIso_model_iff_eee980e8fcc9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:13:36.638165+00:00
-- url     : https://prove2.me/submissions/f2c1feac-d702-46e7-b4f6-f7438317c840

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_SpreadIsoModelIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory AlgebraicGeometry
local notation "along" => GroundTheory.Heights₂.Heights.Model.pullbackIsoAlong
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
theorem _root_.solution : GroundTheory.Heights₂.Heights.Model.SpreadIso.Statement ↔
    ∀ (X : Scheme.{0}), IsFiniteTypeOverZ X → ∀ (a : ℕ), 0 < a →
    ∀ (F G : (invOpen X a).toScheme.Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ (t : genFib X ⟶ (invOpen X a).toScheme), t ≫ (invOpen X a).ι = genTo X →
    ∀ α : (Scheme.Modules.pullback t).obj F ≅ (Scheme.Modules.pullback t).obj G,
    ∃ m' : ℕ, 0 < m' ∧ ∃ ψ : (Scheme.Modules.pullback (X.homOfLE (invOpen_le X a m'))).obj F ≅
        (Scheme.Modules.pullback (X.homOfLE (invOpen_le X a m'))).obj G,
      ∀ (t' : genFib X ⟶ (invOpen X (a * m')).toScheme)
        (e : t' ≫ X.homOfLE (invOpen_le X a m') = t), along e ψ = α := by
  constructor
  · intro hA X hX a ha F G hF hG t ht α
    have := hX.1
    have := hX.2
    have hu : IsUnit (((a : ℤ) : ℚ)) :=
      GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat a (by exact_mod_cast ha.ne')
    obtain rfl : t = GroundTheory.Heights₂.Heights.Model.toInvOpen (toSpecZ X) ℚ (a : ℤ) hu :=
      (cancel_mono (invOpen X a).ι).mp
        (ht.trans (GroundTheory.Heights₂.Heights.Model.toInvOpen_ι (toSpecZ X) ℚ (a : ℤ) hu).symm)
    obtain ⟨m', hm', ψ, hrel⟩ := hA X (toSpecZ X) a ha F G hF hG α
    refine ⟨m', hm', ψ, fun t' e => ?_⟩
    have ht' : t' ≫ (invOpen X (a * m')).ι = genTo X := by
      have := congrArg (· ≫ (invOpen X a).ι) e
      simp only [Category.assoc, Scheme.homOfLE_ι] at this
      exact this.trans ht
    have hu' : IsUnit ((((a : ℤ) * (m' : ℤ) : ℤ) : ℚ)) :=
      GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat _ (by positivity)
    obtain rfl : t' = GroundTheory.Heights₂.Heights.Model.toInvOpen (toSpecZ X) ℚ ((a : ℤ) * (m' : ℤ)) hu' :=
      (cancel_mono (invOpen X (a * m')).ι).mp
        (ht'.trans (GroundTheory.Heights₂.Heights.Model.toInvOpen_ι (toSpecZ X) ℚ _ hu').symm)
    exact hrel
  · intro H X f _ _ a ha F G hF hG α
    obtain rfl : f = toSpecZ X := specZ_hom_ext _ _
    have hu : IsUnit (((a : ℤ) : ℚ)) :=
      GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat a (by exact_mod_cast ha.ne')
    obtain ⟨m', hm', ψ, h⟩ := H X ⟨‹_›, ‹_›⟩ a ha F G hF hG
      (GroundTheory.Heights₂.Heights.Model.toInvOpen (toSpecZ X) ℚ (a : ℤ) hu)
      (GroundTheory.Heights₂.Heights.Model.toInvOpen_ι (toSpecZ X) ℚ (a : ℤ) hu) α
    exact ⟨m', hm', ψ, h _ (GroundTheory.Heights₂.Heights.Model.toInvOpen_homOfLE (toSpecZ X) ℚ
      (GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat _ (by positivity)) hu
      (GroundTheory.Heights₂.Heights.Model.invOpen_mul_le_left (toSpecZ X) a m'))⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
