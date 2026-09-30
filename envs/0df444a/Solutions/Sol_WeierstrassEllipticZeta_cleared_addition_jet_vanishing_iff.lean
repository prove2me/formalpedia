-- Prove2me | solution 1 for WeierstrassEllipticZeta.cleared_addition_jet_vanishing_iff
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T12:49:26.538387+00:00
-- url     : https://prove2.me/submissions/51d778f4-365b-4e43-88e5-1317af554408

import Definitions.Def_WeierstrassEllipticZeta_DifferentialPolynomials
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.LinearCombination

noncomputable section

open Filter
open scoped Topology

open WeierstrassEllipticZeta

private lemma zeta_analytic (L : PeriodPair)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z) :
    AnalyticOnNhd ℂ (weierstrassZeta L) L.latticeᶜ :=
  (show DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ from
    fun z hz => (hzeta z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
      L.isClosed_lattice.isOpen_compl

private lemma wp_not_constant_germ (L : PeriodPair) (z c : ℂ) (hz : z ∉ L.lattice) :
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

private lemma wp_difference_ne (L : PeriodPair)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (hadd : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (z v : ℂ) (hz : z ∉ L.lattice) (hv : v ∉ L.lattice)
    (hplus : z + v ∉ L.lattice) (hminus : z - v ∉ L.lattice) :
    L.weierstrassP v - L.weierstrassP z ≠ 0 := by
  intro heq
  let f : ℂ → ℂ := fun w => L.weierstrassP w - L.weierstrassP v
  let a : ℂ → ℂ := fun w => weierstrassZeta L (w + v) +
    weierstrassZeta L (w - v) - 2 * weierstrassZeta L w -
      weierstrassZeta L v - weierstrassZeta L (-v)
  have hf : AnalyticAt ℂ f z := (L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const
  have ha : AnalyticAt ℂ a z := by
    have hZ := zeta_analytic L hzeta
    have hp : AnalyticAt ℂ (fun w => weierstrassZeta L (w + v)) z :=
      (hZ _ hplus).comp (f := fun w : ℂ => w + v) (show AnalyticAt ℂ (fun w : ℂ => w + v) z from
        analyticAt_id.add analyticAt_const)
    have hm : AnalyticAt ℂ (fun w => weierstrassZeta L (w - v)) z :=
      (hZ _ hminus).comp (f := fun w : ℂ => w - v) (show AnalyticAt ℂ (fun w : ℂ => w - v) z from
        analyticAt_id.sub analyticAt_const)
    exact ((((hp.add hm).sub (analyticAt_const.mul (hZ _ hz))).sub
      analyticAt_const).sub analyticAt_const)
  have hzero : f z = 0 := by dsimp [f]; linear_combination -heq
  have hfinite : analyticOrderAt f z ≠ ⊤ := by
    intro ho
    apply wp_not_constant_germ L z (L.weierstrassP v) hz
    filter_upwards [analyticOrderAt_eq_top.mp ho] with w hw
    exact sub_eq_zero.mp hw
  have hderiv : deriv f =ᶠ[𝓝 z] f * a := by
    have hopen := L.isClosed_lattice.isOpen_compl
    filter_upwards [hopen.mem_nhds hz,
      (continuousAt_id.add continuousAt_const).eventually (hopen.mem_nhds hplus),
      (continuousAt_id.sub continuousAt_const).eventually (hopen.mem_nhds hminus)]
        with w hw hwp hwm
    have h1 := hadd w v hw hv hwp
    have h2 := hadd w (-v) hw (by simpa using hv) (by simpa [sub_eq_add_neg] using hwm)
    rw [L.weierstrassP_neg, L.derivWeierstrassP_neg] at h2
    have hD : HasDerivAt L.weierstrassP (L.derivWeierstrassP w) w := by
      simpa using (L.differentiableOn_weierstrassP.differentiableAt
        (hopen.mem_nhds hw)).hasDerivAt
    change deriv (fun w => L.weierstrassP w - L.weierstrassP v) w = f w * a w
    rw [(hD.sub_const _).deriv]
    dsimp [f, a]
    simp only [sub_eq_add_neg] at h2 ⊢
    linear_combination (h1 + h2) / 2
  have ho : analyticOrderAt (deriv f) z + 1 = analyticOrderAt f z := by
    simpa [hzero] using hf.analyticOrderAt_deriv_add_one
  rw [analyticOrderAt_congr hderiv, analyticOrderAt_mul hf ha] at ho
  have hle : analyticOrderAt f z + 1 ≤ analyticOrderAt f z := by
    calc
      _ ≤ (analyticOrderAt f z + analyticOrderAt a z) + 1 :=
        add_le_add (show analyticOrderAt f z ≤ analyticOrderAt f z + analyticOrderAt a z from
          le_self_add) le_rfl
      _ = _ := ho
  exact (lt_irrefl _ ((ENat.add_one_le_iff hfinite).mp hle))

theorem solution
    (L : PeriodPair)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (hadd : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (z v : ℂ) (hz : z ∉ L.lattice) (hv : v ∉ L.lattice)
    (hp : z + v ∉ L.lattice) (hn : z - v ∉ L.lattice)
    (M T : ℕ) {ι : Type} [Fintype ι]
    (l₀ l₂ l₃ : ι → ℕ) (c : ι → ℂ) :
    (2 * (L.weierstrassP v - L.weierstrassP z)) ^ (3 * M) ≠ 0 ∧
    ((∀ n < T, ∑ i, c i *
        iteratedDeriv n (clearedAdditionMonomial L v M (l₀ i) (l₂ i) (l₃ i))
          z = 0) ↔
      ∀ n < T, iteratedDeriv n (fun w =>
        ∑ i, c i * w ^ l₀ i * L.weierstrassP w ^ l₂ i *
          weierstrassZeta L w ^ l₃ i) (z + v) = 0) := by
  classical
  have hunit : (2 * (L.weierstrassP v - L.weierstrassP z)) ^ (3 * M) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (by norm_num) (wp_difference_ne L hzeta hadd _ _ hz hv hp hn))
  refine ⟨hunit, ?_⟩
  let A : ℂ → ℂ := fun w => (2 * (L.weierstrassP v - L.weierstrassP w)) ^ (3 * M)
  let F : ℂ → ℂ := fun w => ∑ i, c i * w ^ l₀ i *
    L.weierstrassP w ^ l₂ i * weierstrassZeta L w ^ l₃ i
  let G : ℂ → ℂ := fun w => F (w + v)
  have hA : AnalyticAt ℂ A z :=
    (analyticAt_const.mul (analyticAt_const.sub
      (L.analyticOnNhd_weierstrassP _ hz))).pow _
  have hF : AnalyticAt ℂ F (z + v) := by
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact (((analyticAt_const.mul (analyticAt_id.pow _)).mul
      ((L.analyticOnNhd_weierstrassP _ hp).pow _)).mul
      ((zeta_analytic L hzeta _ hp).pow _))
  have hG : AnalyticAt ℂ G z :=
    hF.comp (f := fun w : ℂ => w + v) (show AnalyticAt ℂ (fun w : ℂ => w + v) z from
      analyticAt_id.add analyticAt_const)
  have hmono (i : ι) : AnalyticAt ℂ
      (clearedAdditionMonomial L v M (l₀ i) (l₂ i) (l₃ i)) z := by
    have haddA : AnalyticAt ℂ (fun w : ℂ => w + v) z :=
      analyticAt_id.add analyticAt_const
    exact ((((haddA.pow _).mul hA).mul
      (((L.analyticOnNhd_weierstrassP _ hp).comp (f := fun w : ℂ => w + v) haddA).pow _)).mul
      (((zeta_analytic L hzeta _ hp).comp (f := fun w : ℂ => w + v) haddA).pow _))
  have hsum (n : ℕ) : iteratedDeriv n (A * G) z =
      ∑ i, c i * iteratedDeriv n
        (clearedAdditionMonomial L v M (l₀ i) (l₂ i) (l₃ i)) z := by
    have heq : A * G = fun w => ∑ i, c i *
        clearedAdditionMonomial L v M (l₀ i) (l₂ i) (l₃ i) w := by
      funext w
      simp only [Pi.mul_apply, A, G, F, Finset.mul_sum, clearedAdditionMonomial]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq, iteratedDeriv_fun_sum (f := fun i w => c i *
      clearedAdditionMonomial L v M (l₀ i) (l₂ i) (l₃ i) w)
        (fun i _ => (analyticAt_const.mul (hmono i)).contDiffAt)]
    apply Finset.sum_congr rfl
    intro i hi
    exact iteratedDeriv_const_mul_field _ _
  have horder : analyticOrderAt (A * G) z = analyticOrderAt G z := by
    rw [analyticOrderAt_mul hA hG, hA.analyticOrderAt_eq_zero.mpr hunit, zero_add]
  have hiff : (∀ n < T, iteratedDeriv n (A * G) z = 0) ↔
      ∀ n < T, iteratedDeriv n G z = 0 := by
    rw [← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hA.mul hG),
      ← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hG, horder]
  simpa only [hsum, G, iteratedDeriv_comp_add_const] using hiff

