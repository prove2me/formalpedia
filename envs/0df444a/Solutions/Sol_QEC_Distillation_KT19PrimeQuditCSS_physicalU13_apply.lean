-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.physicalU13_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:42:20.681652+00:00
-- url     : https://prove2.me/submissions/447a0ee3-c4a8-42fb-8997-21344bb05504

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
noncomputable section
namespace QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] primeQuditRegisterLabelFintype
private theorem composeU13AtTransports_apply (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] (sites : List Site)
    (psi : PrimeQuditRegister p Site) (label : PrimeQuditRegisterLabel p Site) :
    UnitaryTransport.composeList (sites.map (u13AtTransport p)) psi label =
      (sites.map fun site => u13AtAmplitude p site label).prod * psi label := by
  induction sites generalizing psi with
  | nil => simp [UnitaryTransport.composeList]
  | cons site sites ih =>
      change UnitaryTransport.composeList (sites.map (u13AtTransport p))
          (u13AtTransport p site psi) label = _
      rw [ih]
      simp only [u13AtTransport_apply, List.map_cons, List.prod_cons]
      ring
namespace CubicRowFamily
variable {p : Nat} [NeZero p] {Logical Stabilizer Site : Type u}
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site]
end CubicRowFamily
namespace CubicRowFamily
variable {p : Nat} [NeZero p] {Logical Stabilizer Site : Type u}
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site] [DecidableEq Site]
end CubicRowFamily
namespace CubicRowFamily
variable {p : Nat} [NeZero p] {Logical Stabilizer Site : Type u}
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site] [DecidableEq Site]
end CubicRowFamily
namespace fiveSiteSingleLogical
end fiveSiteSingleLogical
end QEC.Distillation.KT19PrimeQuditCSS
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] primeQuditRegisterLabelFintype
namespace QEC.Distillation.KT19PrimeQuditCSS
theorem _root_.solution (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site]
    (psi : PrimeQuditRegister p Site) (label : PrimeQuditRegisterLabel p Site) :
    physicalU13 p psi label =
      (∏ site : Site, u13AtAmplitude p site label) * psi label := by
  rw [physicalU13, UnitaryTransport.composeFamily]
  have hlist :
      List.ofFn (fun j : Fin (Fintype.card Site) =>
        u13AtTransport p (siteEquivFin Site j)) =
        (List.ofFn (siteEquivFin Site)).map (u13AtTransport p) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    rfl
  rw [hlist, composeU13AtTransports_apply]
  rw [List.map_ofFn, Fin.prod_ofFn]
  congr 1
  exact Fintype.prod_equiv (siteEquivFin Site) _ _ (fun _ => rfl)
end QEC.Distillation.KT19PrimeQuditCSS
