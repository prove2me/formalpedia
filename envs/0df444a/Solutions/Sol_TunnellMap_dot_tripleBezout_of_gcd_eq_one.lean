-- Prove2me | solution 1 for TunnellMap.dot_tripleBezout_of_gcd_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:42.764449+00:00
-- url     : https://prove2.me/submissions/ae3bafc5-6b42-444e-8bf3-431f0053060e

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_tau
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_tau



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {p : Triple} (hp : tripleGCD p = 1) :
    dot p (tripleBezout p) = 1 := by
  have hxy := Int.gcd_eq_gcd_ab p.x p.y
  have hall := Int.gcd_eq_gcd_ab (Int.gcd p.x p.y : ℤ) p.z
  calc
    dot p (tripleBezout p) =
        (p.x * p.x.gcdA p.y + p.y * p.x.gcdB p.y) *
            (Int.gcd p.x p.y : ℤ).gcdA p.z +
          p.z * (Int.gcd p.x p.y : ℤ).gcdB p.z := by
            simp [dot, tripleBezout]
            ring
    _ = (Int.gcd p.x p.y : ℤ) * (Int.gcd p.x p.y : ℤ).gcdA p.z +
          p.z * (Int.gcd p.x p.y : ℤ).gcdB p.z := by rw [← hxy]
    _ = (tripleGCD p : ℤ) := hall.symm
    _ = 1 := by exact_mod_cast hp
end TunnellMap
