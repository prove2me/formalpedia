-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.bindDependent_sum_bornWeight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:49:46.368205+00:00
-- url     : https://prove2.me/submissions/ca9d8fc8-b510-436a-bc7b-acc6a2d11395

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Sequential_DependentComposition
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_one


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
    (hI : I.kraus.Complete)
    (hJ : ∀ outcome, (J outcome).kraus.Complete)
    (rho : DensityOperator H) :
    ∑ outcome, (I.bindDependent J).bornWeight outcome rho = 1 :=
  (I.bindDependent J).sum_bornWeight_eq_one (I.bindDependent_complete J hI hJ) rho
end QEC.Semantics.FiniteInstrument
