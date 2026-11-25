-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_d_toCochain_e72723e9ad9d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:21:59.90478+00:00
-- url     : https://prove2.me/submissions/1dfbdce5-4bfc-4290-9d70-19a154e73dae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LengthQuotientEqLengthH0

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
open GroundTheory.Heights₂.Heights.Kleiman.QuotientH0Length
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.QuotientH0Length
theorem _root_.solution (F₁ F₂ : SubSystem S x Ω) (t : F₁.secs) :
    Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (SubSystem.quotRes F₁ F₂) 0
      (toCochain F₁ F₂ t) = 0 := by
  have hv : ∀ (I J : Chart x) (h : I.1 ⊆ J.1),
      SubSystem.quotRes F₁ F₂ I J h (secsTo F₁ F₂ I t) = secsTo F₁ F₂ J t := fun _ _ _ => rfl
  exact Cech.d_zero_of_compat (fun I => secsTo F₁ F₂ I t) hv
end GroundTheory.Heights₂.Heights.Kleiman.QuotientH0Length
