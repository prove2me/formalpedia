-- Prove2me | solution 2 for WeierstrassEllipticZeta.zeta_addition_formula
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-05T01:36:29.328399+00:00
-- url     : https://prove2.me/submissions/3e265975-e555-4611-9952-cf6f82bfc11d

import Theorems.Thm_WeierstrassEllipticZeta_frobenius_stickelberger
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta

noncomputable section

open Filter
open scoped Topology

namespace WeierstrassEllipticZeta

private lemma frobenius_stickelberger_derivative (L : PeriodPair) (z v : ℂ)
    (hz : z ∉ L.lattice) (hv : v ∉ L.lattice) (hzv : z + v ∉ L.lattice) :
    2 * (weierstrassZeta L (z + v) - weierstrassZeta L z - weierstrassZeta L v) *
      (-L.weierstrassP (z + v) + L.weierstrassP v) =
        L.derivWeierstrassP v + L.derivWeierstrassP (z + v) := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hZ := hasDerivAt_weierstrassZeta L v hv
  have hZv : HasDerivAt (fun w ↦ weierstrassZeta L (z + w))
      (-L.weierstrassP (z + v)) v := by
    convert! (hasDerivAt_weierstrassZeta L (z + v) hzv).comp v
      ((hasDerivAt_const v z).add (hasDerivAt_id v)) using 1
    simp
  have hP : HasDerivAt L.weierstrassP (L.derivWeierstrassP v) v := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (hopen.mem_nhds hv)).hasDerivAt
  have hPv : HasDerivAt (fun w ↦ L.weierstrassP (z + w))
      (L.derivWeierstrassP (z + v)) v := by
    have hh : HasDerivAt L.weierstrassP (L.derivWeierstrassP (z + v)) (z + v) := by
      simpa using (L.differentiableOn_weierstrassP.differentiableAt
        (hopen.mem_nhds hzv)).hasDerivAt
    convert! hh.comp v ((hasDerivAt_const v z).add (hasDerivAt_id v)) using 1
    simp
  have hnear : ∀ᶠ w in 𝓝 v, w ∉ L.lattice := hopen.mem_nhds hv
  have hnearv : ∀ᶠ w in 𝓝 v, z + w ∉ L.lattice :=
    (continuousAt_const.add continuousAt_id).eventually (hopen.mem_nhds hzv)
  have heq : (fun w ↦
      (weierstrassZeta L (z + w) - weierstrassZeta L z - weierstrassZeta L w) ^ 2)
      =ᶠ[𝓝 v] (fun w ↦ L.weierstrassP z + L.weierstrassP w + L.weierstrassP (z + w)) := by
    filter_upwards [hnear, hnearv] with w hw hzw
    exact frobenius_stickelberger L z w hz hw hzw
  have hleft := ((hZv.sub_const (weierstrassZeta L z)).sub hZ).pow 2
  have hright := ((hasDerivAt_const v (L.weierstrassP z)).add hP).add hPv
  have he := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  simp only [Pi.sub_apply, Nat.cast_ofNat, show 2 - 1 = (1 : ℕ) by decide,
    pow_one, sub_neg_eq_add, zero_add] at he
  exact he

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

theorem solution (L : PeriodPair) (z v : ℂ)
    (hz : z ∉ L.lattice) (hv : v ∉ L.lattice) (hzv : z + v ∉ L.lattice) :
    2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
      2 * (weierstrassZeta L z + weierstrassZeta L v) *
        (L.weierstrassP v - L.weierstrassP z) +
      L.derivWeierstrassP v - L.derivWeierstrassP z := by
  have hdv := frobenius_stickelberger_derivative L z v hz hv hzv
  have hdz := frobenius_stickelberger_derivative L v z hv hz (by simpa [add_comm] using hzv)
  rw [add_comm v z] at hdz
  linear_combination hdv - hdz
