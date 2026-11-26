-- Prove2me | solution 1 for WreathAssoc.Phi_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:06.81186+00:00
-- url     : https://prove2.me/submissions/ac418296-80e6-493a-b83d-2b3d0e707602

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_Cayley
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_FactorTower

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.unusedSectionVars false
universe u
open Green
open WreathAssoc
variable (G B' B Y X : Type u) [Monoid G] [Monoid B'] [Monoid B]
  [MulAction B' Y] [MulAction B X]
attribute [local instance] actW
namespace WreathAssoc
theorem _root_.solution : Function.Injective (Phi G B' B Y X) := by
  intro F1 F2 h
  apply WreathProduct.ext
  · funext x
    apply WreathProduct.ext
    · funext y
      exact congrArg (fun w => WreathProduct.func w (y, x)) h
    · exact congrArg (fun w => (WreathProduct.base w).func x) h
  · exact congrArg (fun w => (WreathProduct.base w).base) h
end WreathAssoc
