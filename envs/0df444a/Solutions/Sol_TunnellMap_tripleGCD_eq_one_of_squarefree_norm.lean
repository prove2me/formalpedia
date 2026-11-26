-- Prove2me | solution 1 for TunnellMap.tripleGCD_eq_one_of_squarefree_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:56.617619+00:00
-- url     : https://prove2.me/submissions/efeb4390-97bd-469a-8100-7332a6b57e32

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
theorem _root_.solution {p : Triple} {n : ℤ}
    (hn : Squarefree n) (hnorm : dot p p = n) : tripleGCD p = 1 := by
  let g : ℤ := tripleGCD p
  have hgxy : (tripleGCD p : ℤ) ∣ (Int.gcd p.x p.y : ℤ) :=
    Int.gcd_dvd_left (Int.gcd p.x p.y : ℤ) p.z
  have hgx : g ∣ p.x := hgxy.trans (Int.gcd_dvd_left p.x p.y)
  have hgy : g ∣ p.y := hgxy.trans (Int.gcd_dvd_right p.x p.y)
  have hgz : g ∣ p.z := Int.gcd_dvd_right (Int.gcd p.x p.y : ℤ) p.z
  have hgxx : g * g ∣ p.x * p.x := mul_dvd_mul hgx hgx
  have hgyy : g * g ∣ p.y * p.y := mul_dvd_mul hgy hgy
  have hgzz : g * g ∣ p.z * p.z := mul_dvd_mul hgz hgz
  have hgnorm : g * g ∣ dot p p := by
    simpa [dot] using dvd_add (dvd_add hgxx hgyy) hgzz
  have hunit : IsUnit g := hn g (by simpa [hnorm] using hgnorm)
  have hgCases : g = 1 ∨ g = -1 := Int.isUnit_iff.mp hunit
  have hgNonneg : 0 ≤ g := by
    dsimp [g]
    exact Int.natCast_nonneg _
  rcases hgCases with hg | hg
  · have hg' : (tripleGCD p : ℤ) = 1 := by simpa [g] using hg
    exact Int.ofNat_inj.mp (by simpa using hg')
  · omega
end TunnellMap
