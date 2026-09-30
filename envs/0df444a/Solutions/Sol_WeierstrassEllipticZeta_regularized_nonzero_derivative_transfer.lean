-- Prove2me | solution 1 for WeierstrassEllipticZeta.regularized_nonzero_derivative_transfer
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T02:12:03.042912+00:00
-- url     : https://prove2.me/submissions/33e3158b-89dd-4308-98dc-a53531f5c3ba

import Definitions.Def_WeierstrassEllipticZeta_Defs
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic.Ring

noncomputable section
open Filter Set
open scoped Topology

open WeierstrassEllipticZeta

private theorem p2m_regular_punctured_neighborhood (L : PeriodPair) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice := by
  have h : ∀ᶠ w in 𝓝 z, w ∈ ((L.lattice : Set ℂ) \ {z})ᶜ :=
    L.compl_lattice_sdiff_singleton_mem_nhds z
  filter_upwards [h.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hwz
  exact fun hwL => hw ⟨hwL, hwz⟩

private theorem p2m_analytic_factor_nonzero_derivative
    (F G H : ℂ → ℂ) (z : ℂ)
    (hF : AnalyticAt ℂ F z) (hG : AnalyticAt ℂ G z) (hH : AnalyticAt ℂ H z)
    (hidentity : G =ᶠ[𝓝 z] H * F) (t : ℕ)
    (ht : iteratedDeriv t G z ≠ 0) :
    ∃ n ≤ t, iteratedDeriv n F z ≠ 0 := by
  by_contra! hzero
  have hoF : ((t + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt F z :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hF).mpr
      (fun n hn => hzero n (by omega))
  have hoG : ((t + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt G z := by
    rw [analyticOrderAt_congr hidentity, analyticOrderAt_mul hH hF]
    exact hoF.trans le_add_self
  exact ht ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hG).mp hoG t
    (by omega))

theorem solution
    (L : PeriodPair) (v : ℂ) (F σ S G : ℂ → ℂ) (e M : ℕ)
    (he : 6 * M ≤ e)
    (hF : AnalyticOnNhd ℂ F {z : ℂ | z + v ∉ L.lattice})
    (hσ : AnalyticOnNhd ℂ σ univ)
    (hS : AnalyticOnNhd ℂ S univ)
    (hG : AnalyticOnNhd ℂ G univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → S z = σ z ^ 2 * L.weierstrassP z)
    (hG_value : ∀ z : ℂ, z ∉ L.lattice → z + v ∉ L.lattice →
      G z = σ z ^ e * (2 * (L.weierstrassP v - L.weierstrassP z)) ^ (3 * M) * F z) :
    ∀ z : ℂ, z + v ∉ L.lattice → ∀ t : ℕ, iteratedDeriv t G z ≠ 0 →
      ∃ n ≤ t, iteratedDeriv n F z ≠ 0 := by
  let H : ℂ → ℂ := fun z => σ z ^ (e - 6 * M) *
    (2 * (L.weierstrassP v * σ z ^ 2 - S z)) ^ (3 * M)
  have hH : AnalyticOnNhd ℂ H univ := by
    intro z hz
    exact ((hσ z hz).pow _).mul
      ((analyticAt_const.mul ((analyticAt_const.mul ((hσ z hz).pow 2)).sub
        (hS z hz))).pow _)
  have hfactor (w : ℂ) (hw : w ∉ L.lattice) (hwv : w + v ∉ L.lattice) :
      G w = H w * F w := by
    rw [hG_value w hw hwv]
    have hexp : e = (e - 6 * M) + 2 * (3 * M) := by omega
    have hp : 2 * (L.weierstrassP v * σ w ^ 2 - S w) =
        σ w ^ 2 * (2 * (L.weierstrassP v - L.weierstrassP w)) := by
      rw [hS_value w hw]
      ring
    dsimp only [H]
    rw [hp, mul_pow (σ w ^ 2), ← pow_mul, ← mul_assoc, ← pow_add, ← hexp]
  intro z hz t ht
  have hFz := hF z hz
  have hGz := hG z (mem_univ z)
  have hHz := hH z (mem_univ z)
  have hpunct : G =ᶠ[𝓝[≠] z] H * F := by
    have hshift : ∀ᶠ w in 𝓝 z, w + v ∉ L.lattice :=
      (continuousAt_id.add continuousAt_const).eventually
        (L.isClosed_lattice.isOpen_compl.mem_nhds hz)
    filter_upwards [p2m_regular_punctured_neighborhood L z,
      hshift.filter_mono nhdsWithin_le_nhds] with w hw hwv
    exact hfactor w hw hwv
  have hidentity : G =ᶠ[𝓝 z] H * F :=
    (hGz.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (hHz.mul hFz).continuousAt).mp hpunct
  exact p2m_analytic_factor_nonzero_derivative F G H z hFz hGz hHz hidentity t ht

