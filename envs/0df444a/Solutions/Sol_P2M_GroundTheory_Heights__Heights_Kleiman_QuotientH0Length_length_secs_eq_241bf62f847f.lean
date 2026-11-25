-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_length_secs_eq_241bf62f847f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:39:52.126953+00:00
-- url     : https://prove2.me/submissions/606e848d-34a3-4a1e-9f20-f37c41c0af88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LengthQuotientEqLengthH0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_length_quotient_eq_length_H0_043239cd666a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_d_toCochain_e72723e9ad9d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_toCochain_eq_zero_iff_a664a5497ed5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_exists_toCochain_eq_12232183b7b7

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
set_option maxHeartbeats 400000
namespace GroundTheory.Heights₂.Heights.Kleiman.QuotientH0Length
theorem _root_.solution (F₁ F₂ : SubSystem S x Ω)
    (hlift : ∀ s : Chart x → Ω, (∀ I, s I ∈ F₁.sub I) →
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ F₂.sub I₂) →
      ∃ t ∈ F₁.secs, ∀ I, t - s I ∈ F₂.sub I) :
    Module.length S (F₁.secs ⧸ F₂.secs.comap F₁.secs.subtype) =
      Module.length S (SubSystem.quotH F₁ F₂ 0) := by
  have hφ := d_toCochain F₁ F₂
  have hh := exists_toCochain_eq F₁ F₂ hlift
  have hK := toCochain_eq_zero_iff F₁ F₂
  have e : Module.length S (F₁.secs ⧸ F₂.secs.comap F₁.secs.subtype) =
      Module.length S (Cech.H (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I)
        (SubSystem.quotRes F₁ F₂) 0) :=
    length_quotient_eq_length_H0 (toCochain F₁ F₂) hφ hh _ hK
  rw [e]
  rfl
end GroundTheory.Heights₂.Heights.Kleiman.QuotientH0Length
