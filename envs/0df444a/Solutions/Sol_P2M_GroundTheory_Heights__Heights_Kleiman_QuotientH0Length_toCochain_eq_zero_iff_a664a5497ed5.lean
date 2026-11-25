-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_toCochain_eq_zero_iff_a664a5497ed5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:15:45.831408+00:00
-- url     : https://prove2.me/submissions/f92ee2b4-845c-488d-b418-39e9b7f3cf0b

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
    toCochain F₁ F₂ t = 0 ↔ t ∈ F₂.secs.comap F₁.secs.subtype := by
  rw [Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · intro h
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro T
    obtain ⟨a, haT⟩ := T.2.1
    have ha : a ∈ support x := T.2.2 haT
    have h1 : (Submodule.Quotient.mk (⟨(t : Ω), mem_sub_of_mem_secs t.2 _⟩ : F₁.sub (sing ha).1) :
        F₁.sub (sing ha).1 ⧸ SubSystem.quotSub F₁ F₂ (sing ha).1) = 0 := congrFun h (sing ha)
    have h2 : (t : Ω) ∈ F₂.sub (sing ha).1 :=
      (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ (sing ha).1)).mp h1
    exact F₂.mono _ T (Finset.singleton_subset_iff.mpr haT) _ h2
  · intro h
    funext I
    show (Submodule.Quotient.mk (⟨(t : Ω), mem_sub_of_mem_secs t.2 _⟩ : F₁.sub I.1) :
        F₁.sub I.1 ⧸ SubSystem.quotSub F₁ F₂ I.1) = 0
    exact (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ I.1)).mpr (mem_sub_of_mem_secs h I.1)
end GroundTheory.Heights₂.Heights.Kleiman.QuotientH0Length
