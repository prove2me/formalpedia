-- Prove2me | solution 1 for WeierstrassEllipticZeta.wp_addition_formula
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-05T00:51:29.722654+00:00
-- url     : https://prove2.me/submissions/9e1a23ca-a429-46dd-9e19-56fd952bfdf8

import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_derivWeierstrassP
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_formula

noncomputable section

open Filter
open scoped Topology

namespace WeierstrassEllipticZeta

/-- Differentiating the multiplied zeta addition identity gives the elliptic
addition identity, without any division by a difference of ℘ values. -/
theorem wp_addition_of_zeta_addition
    (hadd : ∀ (L : PeriodPair) (z v : ℂ),
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (L : PeriodPair) (z v : ℂ)
    (hz : z ∉ L.lattice) (hv : v ∉ L.lattice) (hzv : z + v ∉ L.lattice) :
    4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
      -4 * (L.weierstrassP z + L.weierstrassP v) *
        (L.weierstrassP v - L.weierstrassP z) ^ 2 +
      (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2 := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hP : HasDerivAt L.weierstrassP (L.derivWeierstrassP v) v := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (hopen.mem_nhds hv)).hasDerivAt
  have hD := hasDerivAt_derivWeierstrassP L v hv
  have hZ := hasDerivAt_weierstrassZeta L v hv
  have hZv : HasDerivAt (fun w ↦ weierstrassZeta L (z + w))
      (-L.weierstrassP (z + v)) v := by
    convert! (hasDerivAt_weierstrassZeta L (z + v) hzv).comp v
      ((hasDerivAt_const v z).add (hasDerivAt_id v)) using 1
    simp
  have hvnear : ∀ᶠ w in 𝓝 v, w ∉ L.lattice := hopen.mem_nhds hv
  have hzvnear : ∀ᶠ w in 𝓝 v, z + w ∉ L.lattice :=
    (continuousAt_const.add continuousAt_id).eventually (hopen.mem_nhds hzv)
  have heq : (fun w ↦
      2 * (L.weierstrassP w - L.weierstrassP z) * weierstrassZeta L (z + w))
      =ᶠ[𝓝 v] (fun w ↦
      2 * (weierstrassZeta L z + weierstrassZeta L w) *
        (L.weierstrassP w - L.weierstrassP z) +
      L.derivWeierstrassP w - L.derivWeierstrassP z) := by
    filter_upwards [hvnear, hzvnear] with w hw hzw
    exact hadd L z w hz hw hzw
  have hleft := ((hP.sub_const (L.weierstrassP z)).const_mul 2).mul hZv
  have hright := (((((hasDerivAt_const v (weierstrassZeta L z)).add hZ).const_mul 2).mul
    (hP.sub_const (L.weierstrassP z))).add hD).sub_const (L.derivWeierstrassP z)
  have hdiff := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  simp only [Pi.add_apply] at hdiff
  have hvalue := hadd L z v hz hv hzv
  have hcubev := L.derivWeierstrassP_sq v hv
  have hcubez := L.derivWeierstrassP_sq z hz
  linear_combination -2 * (L.weierstrassP v - L.weierstrassP z) * hdiff +
    2 * L.derivWeierstrassP v * hvalue + hcubev - hcubez

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

theorem solution (L : PeriodPair) (z v : ℂ)
    (hz : z ∉ L.lattice) (hv : v ∉ L.lattice)
    (hzv : z + v ∉ L.lattice) :
    4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
      -4 * (L.weierstrassP z + L.weierstrassP v) *
        (L.weierstrassP v - L.weierstrassP z) ^ 2 +
      (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2 := by
  exact wp_addition_of_zeta_addition zeta_addition_formula L z v hz hv hzv
