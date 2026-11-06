-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensor_sum_bornWeight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:45:55.140443+00:00
-- url     : https://prove2.me/submissions/4d3e331f-5131-4ceb-9ea7-ec4a49460f78

import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_one


set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {κ' : Type x} [Fintype κ']
variable {Ξ : Ω → Type y} [∀ outcome, Fintype (Ξ outcome)]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
variable {Ω' : Type y} [Fintype Ω']
variable {R S : Type u}
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution (I : FiniteInstrument κ Ω H K)
    (J : FiniteInstrument κ' Ω' R S)
    (hI : I.kraus.Complete) (hJ : J.kraus.Complete)
    (rho : DensityOperator (CompositeSystem H R)) :
    ∑ outcome, (I.tensor J).bornWeight outcome rho = 1 :=
  (I.tensor J).sum_bornWeight_eq_one (I.tensor_complete J hI hJ) rho
end QEC.Semantics.FiniteInstrument
