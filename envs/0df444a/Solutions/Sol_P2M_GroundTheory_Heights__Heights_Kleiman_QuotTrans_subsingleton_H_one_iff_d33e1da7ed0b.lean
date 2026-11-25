-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_subsingleton_H_one_iff_d33e1da7ed0b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:11:23.419297+00:00
-- url     : https://prove2.me/submissions/52a9d02e-a814-4832-84ca-3e33a8582885

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotTransSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PQuotTrans

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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.QuotTrans
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
namespace GroundTheory.Heights₂.Heights.Kleiman.QuotTrans
theorem _root_.solution :
    Subsingleton (Cech.H G ρ 1) ↔
      ∀ z : Cech.Cochain G 1, Cech.d G ρ 1 z = 0 → ∃ w : Cech.Cochain G 0, Cech.d G ρ 0 w = z := by
  unfold Cech.H
  rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]
  constructor
  · intro h z hz
    exact h (LinearMap.mem_ker.mpr hz)
  · intro h z hz
    exact h z (LinearMap.mem_ker.mp hz)
end GroundTheory.Heights₂.Heights.Kleiman.QuotTrans
