-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsPrimeCuspShift_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:50:05.052217+00:00
-- url     : https://prove2.me/submissions/f34d8816-620b-471c-88cd-b764b53876e9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (r : Fin q) (hr : r≠0) :
    r.val.Coprime (q^2) := by
  have hp : 0<r.val := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hr (Fin.ext hz)
  have hn : ¬q∣r.val := by
    intro h
    exact (Nat.le_of_dvd hp h).not_gt r.isLt
  exact (Fact.out : q.Prime).coprime_pow_of_not_dvd hn
end QEC.Coding.TannerLiftedProduct
