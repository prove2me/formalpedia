-- Prove2me | solution 1 for UpperTheory.Reformulated.B.JointEigenvalueBoundsFromAnyDatum.length_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:01:38.391085+00:00
-- url     : https://prove2.me/submissions/40068ef4-4217-40d0-8adb-2ccb09d55da6

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ChainLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.JointEigenvalueBoundsFromAnyDatum
theorem _root_.solution :
    ∀ {O X : Type} [inst : CommRing O] [inst_1 : AddCommGroup X]
    [inst_2 : _root_.Module O X] {A B C : Submodule O X},
    A ≤ B →
      B ≤ C →
        Module.length O (↥C ⧸ Submodule.comap C.subtype A) =
          Module.length O (↥B ⧸ Submodule.comap B.subtype A) + Module.length O (↥C ⧸ Submodule.comap C.subtype B) := by
  intro O X _ _ _ A B C hAB hBC
  let f : (↥B ⧸ Submodule.comap B.subtype A) →ₗ[O] (↥C ⧸ Submodule.comap C.subtype A) :=
    Submodule.mapQ _ _ (Submodule.inclusion hBC) (fun x hx => hx)
  let g : (↥C ⧸ Submodule.comap C.subtype A) →ₗ[O] (↥C ⧸ Submodule.comap C.subtype B) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => hAB hx)
  refine Module.length_eq_add_of_exact f g ?_ ?_ ?_
  · rw [injective_iff_map_eq_zero]
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      intro h
      have h' : Submodule.Quotient.mk (p := Submodule.comap C.subtype A)
          (Submodule.inclusion hBC x) = 0 := h
      rw [Submodule.Quotient.mk_eq_zero] at h' ⊢
      exact h'
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      constructor
      · intro h
        have h' : Submodule.Quotient.mk (p := Submodule.comap C.subtype B) x = 0 := h
        rw [Submodule.Quotient.mk_eq_zero] at h'
        exact ⟨Submodule.Quotient.mk ⟨x.1, h'⟩, rfl⟩
      · rintro ⟨z, hz⟩
        rw [← hz]
        induction z using Submodule.Quotient.induction_on with
        | H w =>
          have : Submodule.Quotient.mk (p := Submodule.comap C.subtype B)
              (Submodule.inclusion hBC w) = 0 :=
            (Submodule.Quotient.mk_eq_zero _).2 w.2
          exact this
end UpperTheory.Reformulated.B.JointEigenvalueBoundsFromAnyDatum
