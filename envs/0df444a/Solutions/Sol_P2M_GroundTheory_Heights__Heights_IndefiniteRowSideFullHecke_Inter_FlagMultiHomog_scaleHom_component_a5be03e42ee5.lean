-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_scaleHom_component_a5be03e42ee5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:44.694633+00:00
-- url     : https://prove2.me/submissions/c571f3ca-ca95-4b25-9878-dced950951de

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMultiHomog
import Theorems.Thm_GroundTheory_Arith_Iwasawa_IsDistinguished_mul


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
variable {L : Type} [DecidableEq L] {κ : L → Type} {R : Type} [CommRing R]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
theorem _root_.solution (φ : MvPolynomial (Σ b, κ b) ℤ →+* R) (b : L → ℕ)
    (f : MvPolynomial (Σ b, κ b) ℤ) :
    scaleHom φ (weightedHomogeneousComponent (NumbersDVR.blockWeight κ) b f) =
      weightedHomogeneousComponent (fun c : L => (Pi.single c 1 : L → ℕ)) b (scaleHom φ f) := by
  set ω : L → L → ℕ := fun c => Pi.single c 1
  have he : ∀ q : Σ b, κ b, IsWeightedHomogeneous ω (C (φ (X q)) * X q.1 : MvPolynomial L R)
      (NumbersDVR.blockWeight κ q) := fun q => by
    have := (isWeightedHomogeneous_C ω (φ (X q))).mul (isWeightedHomogeneous_X R ω q.1)
    rwa [zero_add] at this
  induction f using MvPolynomial.induction_on' with
  | monomial d c =>
    have hmon : IsWeightedHomogeneous ω (scaleHom φ (monomial d c))
        (Finsupp.weight (NumbersDVR.blockWeight κ) d) := by
      rw [scaleHom, coe_eval₂Hom, eval₂_monomial, Finsupp.weight_apply, eq_intCast,
        ← map_intCast (C : R →+* MvPolynomial L R)]
      have := (isWeightedHomogeneous_C ω (c : R)).mul (IsWeightedHomogeneous.prod d.support
        (fun q => (C (φ (X q)) * X q.1 : MvPolynomial L R) ^ d q)
        (fun q => d q • NumbersDVR.blockWeight κ q) (fun q _ => (he q).pow (d q)))
      rw [zero_add] at this
      exact this
    by_cases hdm : Finsupp.weight (NumbersDVR.blockWeight κ) d = b
    · have hmon' : IsWeightedHomogeneous ω (scaleHom φ (monomial d c)) b := hdm ▸ hmon
      rw [(isWeightedHomogeneous_monomial _ d c hdm).weightedHomogeneousComponent_same,
        hmon'.weightedHomogeneousComponent_same]
    · rw [(isWeightedHomogeneous_monomial (NumbersDVR.blockWeight κ) d c
        (m := Finsupp.weight (NumbersDVR.blockWeight κ) d) rfl).weightedHomogeneousComponent_ne b
        (Ne.symm hdm), hmon.weightedHomogeneousComponent_ne b (Ne.symm hdm), map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
