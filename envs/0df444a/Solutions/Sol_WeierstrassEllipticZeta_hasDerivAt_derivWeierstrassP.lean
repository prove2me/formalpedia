-- Prove2me | solution 1 for WeierstrassEllipticZeta.hasDerivAt_derivWeierstrassP
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-05T00:47:58.885832+00:00
-- url     : https://prove2.me/submissions/98325dca-1845-4734-9e55-5fe1964e52fa

import Definitions.Def_WeierstrassEllipticZeta_Defs

noncomputable section

open Filter
open scoped Topology

namespace WeierstrassEllipticZeta

/-- The derivative of ℘ has isolated zeros on the complement of the lattice.
Its triple pole at zero rules out the identically zero alternative. -/
lemma derivWeierstrassP_eventually_ne_zero (L : PeriodPair) (v : ℂ)
    (hv : v ∉ L.lattice) :
    ∀ᶠ w in 𝓝[≠] v, L.derivWeierstrassP w ≠ 0 := by
  by_contra h
  have hf : ∃ᶠ w in 𝓝[≠] v, L.derivWeierstrassP w = 0 := by simpa using h
  have hconnected : IsPreconnected (L.lattice : Set ℂ)ᶜ :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
  have heq : Set.EqOn L.derivWeierstrassP (fun _ ↦ 0) L.latticeᶜ :=
    L.analyticOnNhd_derivWeierstrassP.eqOn_of_preconnected_of_frequently_eq
      (fun _ _ ↦ analyticAt_const) hconnected hv hf
  have hregular : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∉ L.lattice := by
    have hnhds : ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ ((L.lattice : Set ℂ) \ {0})ᶜ :=
      L.compl_lattice_sdiff_singleton_mem_nhds 0
    filter_upwards [hnhds.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hw hw0
    intro hwL
    exact hw ⟨hwL, hw0⟩
  have hnear : L.derivWeierstrassP =ᶠ[𝓝[≠] (0 : ℂ)] (fun _ ↦ 0) :=
    hregular.mono fun w hw ↦ heq hw
  have ho := meromorphicOrderAt_congr hnear
  have hpole : meromorphicOrderAt L.derivWeierstrassP 0 = ((-3 : ℤ) : WithTop ℤ) := by
    rw [← L.deriv_weierstrassP]
    exact meromorphicOrderAt_deriv (n := -3) (by norm_num)
      (by simpa using L.order_weierstrassP 0 L.lattice.zero_mem)
  rw [hpole, meromorphicOrderAt_const] at ho
  norm_num at ho

private lemma second_derivative_of_ne_zero (L : PeriodPair) (v : ℂ)
    (hv : v ∉ L.lattice) (hne : L.derivWeierstrassP v ≠ 0) :
    deriv L.derivWeierstrassP v = 6 * L.weierstrassP v ^ 2 - L.g₂ / 2 := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hP : HasDerivAt L.weierstrassP (L.derivWeierstrassP v) v := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (hopen.mem_nhds hv)).hasDerivAt
  have hD := (L.differentiableOn_derivWeierstrassP.differentiableAt
    (hopen.mem_nhds hv)).hasDerivAt
  have hnear : ∀ᶠ w in 𝓝 v, w ∉ L.lattice := hopen.mem_nhds hv
  have heq : (fun w ↦ L.derivWeierstrassP w ^ 2) =ᶠ[𝓝 v]
      (fun w ↦ 4 * L.weierstrassP w ^ 3 - L.g₂ * L.weierstrassP w - L.g₃) :=
    hnear.mono fun w hw ↦ L.derivWeierstrassP_sq w hw
  have hh := ((hD.pow 2).congr_of_eventuallyEq heq.symm).unique
    ((((hP.pow 3).const_mul 4).sub (hP.const_mul L.g₂)).sub_const L.g₃)
  have hprod : L.derivWeierstrassP v *
      (deriv L.derivWeierstrassP v - (6 * L.weierstrassP v ^ 2 - L.g₂ / 2)) = 0 := by
    linear_combination hh / 2
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hne)

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

theorem solution (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    HasDerivAt L.derivWeierstrassP (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) z := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hD := L.differentiableOn_derivWeierstrassP.differentiableAt (hopen.mem_nhds hz)
  have hleft : ContinuousAt (deriv L.derivWeierstrassP) z :=
    (L.analyticOnNhd_derivWeierstrassP z hz).deriv.continuousAt
  have hright : ContinuousAt (fun w ↦ 6 * L.weierstrassP w ^ 2 - L.g₂ / 2) z :=
    ((L.analyticOnNhd_weierstrassP z hz).continuousAt.pow 2 |>.const_mul 6).sub
      continuousAt_const
  have hnear : ∀ᶠ w in 𝓝 z, w ∉ L.lattice := hopen.mem_nhds hz
  have heq : deriv L.derivWeierstrassP =ᶠ[𝓝[≠] z]
      (fun w ↦ 6 * L.weierstrassP w ^ 2 - L.g₂ / 2) := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
      derivWeierstrassP_eventually_ne_zero L z hz] with w hw hne
    exact second_derivative_of_ne_zero L w hw hne
  have hvalue := tendsto_nhds_unique (hleft.tendsto.mono_left nhdsWithin_le_nhds)
    ((hright.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm)
  exact hD.hasDerivAt.congr_deriv hvalue
