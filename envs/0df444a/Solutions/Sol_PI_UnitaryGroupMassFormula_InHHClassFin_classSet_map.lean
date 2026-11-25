-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.classSet_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:20.228788+00:00
-- url     : https://prove2.me/submissions/a44109f4-2a29-497c-8d96-e42469cec577

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_ClassSetFinIdx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
open DoubleCoset
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution {G G' : Type} [Group G] [Group G'] (Φ : G ≃* G') (Γ K : Subgroup G) :
    Finite (Formalism.UG.ClassSet (Γ.map Φ.toMonoidHom) (K.map Φ.toMonoidHom)) →
      Finite (Formalism.UG.ClassSet Γ K) := by
  intro hfin
  have himg : ∀ a : G, Φ '' DoubleCoset.doubleCoset a (Γ : Set G) (K : Set G) =
      DoubleCoset.doubleCoset (Φ a) ((Γ.map Φ.toMonoidHom : Subgroup G') : Set G')
        ((K.map Φ.toMonoidHom : Subgroup G') : Set G') := by
    intro a
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hx
      exact DoubleCoset.mem_doubleCoset.2 ⟨Φ h, ⟨h, hh, rfl⟩, Φ k, ⟨k, hk, rfl⟩, by simp [map_mul]⟩
    · intro hy
      obtain ⟨h', ⟨h, hh, rfl⟩, k', ⟨k, hk, rfl⟩, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hy
      exact ⟨h * a * k, DoubleCoset.mem_doubleCoset.2 ⟨h, hh, k, hk, rfl⟩, by simp [map_mul]⟩
  let f : Formalism.UG.ClassSet Γ K → Formalism.UG.ClassSet (Γ.map Φ.toMonoidHom) (K.map Φ.toMonoidHom) :=
    Quotient.map' Φ (fun a b hab => by
      show DoubleCoset.doubleCoset (Φ a) _ _ = DoubleCoset.doubleCoset (Φ b) _ _
      rw [← himg, ← himg]
      exact congrArg (fun s => Φ '' s) hab)
  refine Finite.of_injective f (fun x y hxy => ?_)
  induction x using Quotient.inductionOn' with
  | h a =>
    induction y using Quotient.inductionOn' with
    | h b =>
      apply Quotient.sound'
      have h1 : DoubleCoset.doubleCoset (Φ a) ((Γ.map Φ.toMonoidHom : Subgroup G') : Set G')
          ((K.map Φ.toMonoidHom : Subgroup G') : Set G') =
          DoubleCoset.doubleCoset (Φ b) ((Γ.map Φ.toMonoidHom : Subgroup G') : Set G')
          ((K.map Φ.toMonoidHom : Subgroup G') : Set G') := Quotient.exact' hxy
      rw [← himg, ← himg] at h1
      exact (Set.image_injective.2 Φ.injective) h1
end PI.UnitaryGroupMassFormula.InHHClassFin
