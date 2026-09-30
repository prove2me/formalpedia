-- Prove2me | solution 1 for WeierstrassEllipticZeta.zeta_addition_formula
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-05T00:01:54.100761+00:00
-- url     : https://prove2.me/submissions/6d3cbd7b-37c4-4330-9191-b6ff21a9d13e

import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_nondegenerate

noncomputable section

open Filter
open scoped Topology

namespace WeierstrassEllipticZeta

/-- Each fiber of `℘` is isolated away from the lattice. The identity theorem
rules out a constant germ because `℘` has a double pole at zero. -/
lemma weierstrassP_eventually_ne (L : PeriodPair) (v c : ℂ) (hv : v ∉ L.lattice) :
    ∀ᶠ w in 𝓝[≠] v, L.weierstrassP w ≠ c := by
  by_contra h
  have hf : ∃ᶠ w in 𝓝[≠] v, L.weierstrassP w = c := by simpa using h
  have hconnected : IsPreconnected (L.lattice : Set ℂ)ᶜ :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
  have heq : Set.EqOn L.weierstrassP (fun _ ↦ c) L.latticeᶜ :=
    L.analyticOnNhd_weierstrassP.eqOn_of_preconnected_of_frequently_eq
      (fun _ _ ↦ analyticAt_const) hconnected hv hf
  have hregular : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∉ L.lattice := by
    have hnhds : ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ ((L.lattice : Set ℂ) \ {0})ᶜ :=
      L.compl_lattice_sdiff_singleton_mem_nhds 0
    filter_upwards [hnhds.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hw hw0
    intro hwL
    exact hw ⟨hwL, hw0⟩
  have hnear : L.weierstrassP =ᶠ[𝓝[≠] (0 : ℂ)] (fun _ ↦ c) :=
    hregular.mono fun w hw ↦ heq hw
  have ho := meromorphicOrderAt_congr hnear
  rw [L.order_weierstrassP 0 L.lattice.zero_mem, meromorphicOrderAt_const] at ho
  split_ifs at ho <;> norm_num at ho

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

theorem solution (L : PeriodPair) (z v : ℂ)
    (hz : z ∉ L.lattice) (hv : v ∉ L.lattice)
    (hzv : z + v ∉ L.lattice) :
    2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
      2 * (weierstrassZeta L z + weierstrassZeta L v) *
        (L.weierstrassP v - L.weierstrassP z) +
      L.derivWeierstrassP v - L.derivWeierstrassP z := by
  have hgeneric := zeta_addition_nondegenerate
  have hopen := L.isClosed_lattice.isOpen_compl
  have hP := (L.differentiableOn_weierstrassP.differentiableAt (hopen.mem_nhds hv)).continuousAt
  have hD := (L.differentiableOn_derivWeierstrassP.differentiableAt
    (hopen.mem_nhds hv)).continuousAt
  have hZ := (hasDerivAt_weierstrassZeta L v hv).continuousAt
  have hZv := (hasDerivAt_weierstrassZeta L (z + v) hzv).continuousAt.comp
    (continuousAt_const.add continuousAt_id)
  have hleft : ContinuousAt (fun w ↦
      2 * (L.weierstrassP w - L.weierstrassP z) * weierstrassZeta L (z + w)) v :=
    (continuousAt_const.mul (hP.sub continuousAt_const)).mul hZv
  have hright : ContinuousAt (fun w ↦
      2 * (weierstrassZeta L z + weierstrassZeta L w) *
        (L.weierstrassP w - L.weierstrassP z) +
      L.derivWeierstrassP w - L.derivWeierstrassP z) v :=
    (((continuousAt_const.mul (continuousAt_const.add hZ)).mul
      (hP.sub continuousAt_const)).add hD).sub continuousAt_const
  have hvnear : ∀ᶠ w in 𝓝 v, w ∉ L.lattice := hopen.mem_nhds hv
  have hzvnear : ∀ᶠ w in 𝓝 v, z + w ∉ L.lattice :=
    (continuousAt_const.add continuousAt_id).eventually (hopen.mem_nhds hzv)
  have heq : (fun w ↦
      2 * (L.weierstrassP w - L.weierstrassP z) * weierstrassZeta L (z + w))
      =ᶠ[𝓝[≠] v] (fun w ↦
      2 * (weierstrassZeta L z + weierstrassZeta L w) *
        (L.weierstrassP w - L.weierstrassP z) +
      L.derivWeierstrassP w - L.derivWeierstrassP z) := by
    filter_upwards [hvnear.filter_mono nhdsWithin_le_nhds,
      hzvnear.filter_mono nhdsWithin_le_nhds,
      weierstrassP_eventually_ne L v (L.weierstrassP z) hv] with w hw hzw hne
    rw [hgeneric L z w hz hw hzw hne]
    have hdelta : L.weierstrassP w - L.weierstrassP z ≠ 0 := sub_ne_zero.mpr hne
    field_simp
    ring
  exact tendsto_nhds_unique (hleft.tendsto.mono_left nhdsWithin_le_nhds)
    ((hright.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm)
