-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.bindDependent_kraus_operator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:18:09.943819+00:00
-- url     : https://prove2.me/submissions/dde23110-80b1-4de8-bd55-5b63c40c49cd

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Sequential_DependentComposition

set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {κ₂ : Ω → Type x} [∀ outcome, Fintype (κ₂ outcome)]
variable {Ξ : Ω → Type y} [∀ outcome, Fintype (Ξ outcome)]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) (Ξ outcome) K L)
    (firstIndex : κ) (secondIndex : κ₂ (I.observe firstIndex)) :
    (I.bindDependent J).kraus.operator ⟨firstIndex, secondIndex⟩ =
      ((J (I.observe firstIndex)).kraus.operator secondIndex).comp
        (I.kraus.operator firstIndex) :=
  rfl
end QEC.Semantics.FiniteInstrument
