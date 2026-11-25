-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_length_secs_eq_72584acc7dfe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:46.330184+00:00
-- url     : https://prove2.me/submissions/c685f788-d4de-476a-9fdf-117a1a94145a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrLenRestrict
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_length_quotient_eq_length_H0_0b4d02d4c4c7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_d_toCochain_b5411ff145ec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_toCochain_eq_zero_iff_1f4dc8cca31b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_exists_toCochain_eq_128651034dbd

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
open GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type w} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
set_option maxHeartbeats 1000000
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
theorem _root_.solution (F₁ F₂ : SubSystem S x E)
    (hlift : ∀ s : Chart x → E, (∀ I, s I ∈ F₁.sub I) →
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ F₂.sub I₂) →
      ∃ t ∈ F₁.secs, ∀ I, t - s I ∈ F₂.sub I) :
    Module.length S (F₁.secs ⧸ F₂.secs.comap F₁.secs.subtype) =
      Module.length S (SubSystem.quotH F₁ F₂ 0) := by
  have h := length_quotient_eq_length_H0 (R := S) (G := fun I => ↥(F₁.sub I) ⧸ SubSystem.quotSub F₁ F₂ I)
    (ρ := qres F₁ F₂) (M := F₁.secs) (toCochain F₁ F₂)
    (fun t => by exact d_toCochain F₁ F₂ t)
    (fun z hz => by exact exists_toCochain_eq F₁ F₂ hlift z hz)
    (F₂.secs.comap F₁.secs.subtype)
    (fun t => by exact toCochain_eq_zero_iff F₁ F₂ t)
  exact h
end GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
