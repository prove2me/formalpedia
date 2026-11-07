-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryTripleSupport_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:23:50.788684+00:00
-- url     : https://prove2.me/submissions/eff555d6-f64f-47a7-8eda-22a1695df126

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTriples

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding
open scoped BigOperators
universe u
variable (J : Type u)
variable [Fintype J]
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution {x y : J × Fin 512} (hne : x ≠ y) :
    Disjoint (binaryTripleSupport J x) (binaryTripleSupport J y) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hx hy
  obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hx
  obtain ⟨b, _, hb⟩ := Finset.mem_map.mp hy
  have h : binaryTripleVertex J x a = binaryTripleVertex J y b := ha.trans hb.symm
  have ht : a = b := congrArg Prod.fst h
  subst b
  have hc := congrArg Prod.snd h
  apply hne
  cases a with
  | first => exact hc
  | second => exact (binaryPi2 J).symm.injective hc
  | third => exact (binaryPi3 J).symm.injective hc
end QEC.Distillation.Ngu24Binary
