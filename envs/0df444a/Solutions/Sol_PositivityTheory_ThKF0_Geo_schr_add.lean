-- Prove2me | solution 1 for PositivityTheory.ThKF0.Geo.schr_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:10.876743+00:00
-- url     : https://prove2.me/submissions/04985e1f-b196-4c9a-ae8e-ad886ef1379f

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_GeoAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM Module
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Geo
variable {F : Type} [Field F] {A : Type} [CommRing A] [Algebra F A]
variable {VA : Type} [AddCommGroup VA] [Module A VA] [Module F VA] [IsScalarTower F A VA] {BA : VA → VA → A}
  {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module F V]
namespace PositivityTheory.ThKF0.Geo
theorem _root_.solution [Invertible (2 : A)] (ψ : AddChar A ℂ) (a b : (κ → A) × (κ → A))
    (h : a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 = 0) (φ : (κ → A) → ℂ) : schr ψ (a + b) φ = schr ψ a (schr ψ b φ) := by
  funext x
  have e1 : x ⬝ᵥ (a + b).2 + ⅟(2 : A) * ((a + b).1 ⬝ᵥ (a + b).2) =
      (x ⬝ᵥ a.2 + ⅟(2 : A) * (a.1 ⬝ᵥ a.2)) + ((x + a.1) ⬝ᵥ b.2 + ⅟(2 : A) * (b.1 ⬝ᵥ b.2)) := by
    have h2 : ⅟(2 : A) * 2 = 1 := invOf_mul_self 2
    simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    linear_combination (-⅟(2 : A)) * h + (a.1 ⬝ᵥ b.2) * h2
  have e2 : x + (a + b).1 = x + a.1 + b.1 := by rw [Prod.fst_add, add_assoc]
  simp only [schr]
  rw [e1, e2, AddChar.map_add_eq_mul, mul_assoc]
end PositivityTheory.ThKF0.Geo
