-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.classSet_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:22.684561+00:00
-- url     : https://prove2.me/submissions/e9be89a9-b6b4-49b5-aa48-0f97df15de35

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
theorem _root_.solution {G : Type} [Group G] (Γ K K' : Subgroup G) (h : K ≤ K') :
    Finite (Formalism.UG.ClassSet Γ K) → Finite (Formalism.UG.ClassSet Γ K') := by
  intro hfin
  let f : Formalism.UG.ClassSet Γ K → Formalism.UG.ClassSet Γ K' := Quotient.map' id (fun a b hab => by
    have hb : b ∈ DoubleCoset.doubleCoset a (Γ : Set G) (K : Set G) := by
      rw [show DoubleCoset.doubleCoset a (Γ : Set G) (K : Set G) = DoubleCoset.doubleCoset b Γ K from hab]
      exact DoubleCoset.mem_doubleCoset_self Γ K b
    obtain ⟨x, hx, y, hy, hxy⟩ := DoubleCoset.mem_doubleCoset.mp hb
    have hb' : b ∈ DoubleCoset.doubleCoset a (Γ : Set G) (K' : Set G) :=
      DoubleCoset.mem_doubleCoset.mpr ⟨x, hx, y, h hy, hxy⟩
    exact (DoubleCoset.doubleCoset_eq_of_mem hb').symm)
  refine Finite.of_surjective f (fun q => ?_)
  induction q using Quotient.inductionOn' with
  | h x => exact ⟨Quotient.mk'' x, rfl⟩
end PI.UnitaryGroupMassFormula.InHHClassFin
