-- Prove2me | solution 1 for WeierstrassEllipticZeta.regularization_preserves_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T11:57:30.418906+00:00
-- url     : https://prove2.me/submissions/d1888442-0976-4aed-816c-516c72328910

import Definitions.Def_WeierstrassEllipticZeta_Defs
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.NormNum

noncomputable section
open Filter
open scoped Topology

open WeierstrassEllipticZeta

private theorem p2m_wp_not_constant_germ (L : PeriodPair) (z c : ℂ) (hz : z ∉ L.lattice) :
    ¬ L.weierstrassP =ᶠ[𝓝 z] (fun _ => c) := by
  intro h
  have hconnected : IsPreconnected (L.lattice : Set ℂ)ᶜ :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
  have heq : Set.EqOn L.weierstrassP (fun _ => c) L.latticeᶜ :=
    L.analyticOnNhd_weierstrassP.eqOn_of_preconnected_of_frequently_eq
      (fun _ _ => analyticAt_const) hconnected hz
        (h.filter_mono nhdsWithin_le_nhds).frequently
  have hregular : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∉ L.lattice := by
    have hnhds : ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ ((L.lattice : Set ℂ) \ {0})ᶜ :=
      L.compl_lattice_sdiff_singleton_mem_nhds 0
    filter_upwards [hnhds.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hw hw0
    exact fun hwL => hw ⟨hwL, hw0⟩
  have hnear : L.weierstrassP =ᶠ[𝓝[≠] (0 : ℂ)] (fun _ => c) :=
    hregular.mono fun w hw => heq hw
  have ho := meromorphicOrderAt_congr hnear
  rw [L.order_weierstrassP 0 L.lattice.zero_mem, meromorphicOrderAt_const] at ho
  split_ifs at ho <;> norm_num at ho

theorem solution
    (L : PeriodPair) (v : ℂ) (F σ G : ℂ → ℂ) (e M : ℕ)
    (hF : ∀ z : ℂ, z + v ∉ L.lattice → ContinuousAt F z)
    (hσ : ∀ z : ℂ, z ∉ L.lattice → σ z ≠ 0)
    (hG : ∀ z : ℂ, z ∉ L.lattice → z + v ∉ L.lattice →
      G z = σ z ^ e * (2 * (L.weierstrassP v - L.weierstrassP z)) ^ (3 * M) * F z)
    (h_nonzero : ∃ z : ℂ, z + v ∉ L.lattice ∧ F z ≠ 0) :
    G ≠ 0 := by
  intro hzero
  obtain ⟨z, hz, hFz⟩ := h_nonzero
  have hopen := L.isClosed_lattice.isOpen_compl
  have hshift : ∀ᶠ w in 𝓝 z, w + v ∉ L.lattice :=
    (continuousAt_id.add continuousAt_const).eventually (hopen.mem_nhds hz)
  have hFn : ∀ᶠ w in 𝓝 z, F w ≠ 0 := (hF z hz).eventually_ne hFz
  have hregular : ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice := by
    have hnhds : ∀ᶠ w in 𝓝 z, w ∈ ((L.lattice : Set ℂ) \ {z})ᶜ :=
      L.compl_lattice_sdiff_singleton_mem_nhds z
    filter_upwards [hnhds.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hw hwz
    exact fun hwL => hw ⟨hwL, hwz⟩
  obtain ⟨x, hx, hxv, hFx⟩ := (hregular.and
    ((hshift.and hFn).filter_mono nhdsWithin_le_nhds)).exists
  apply p2m_wp_not_constant_germ L x (L.weierstrassP v) hx
  have hshiftx : ∀ᶠ w in 𝓝 x, w + v ∉ L.lattice :=
    (continuousAt_id.add continuousAt_const).eventually (hopen.mem_nhds hxv)
  filter_upwards [hopen.mem_nhds hx, hshiftx, (hF x hxv).eventually_ne hFx]
    with w hw hwv hFw
  have hproduct : σ w ^ e *
      (2 * (L.weierstrassP v - L.weierstrassP w)) ^ (3 * M) * F w = 0 := by
    rw [← hG w hw hwv, hzero]
    rfl
  have hpower := (mul_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hFw)).resolve_left
    (pow_ne_zero e (hσ w hw))
  have hfactor : 2 * (L.weierstrassP v - L.weierstrassP w) = 0 :=
    eq_zero_of_pow_eq_zero hpower
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left (by norm_num))).symm

