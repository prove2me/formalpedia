-- Prove2me | solution 1 for WeierstrassEllipticZeta.wp_root_power_dvd_of_sigma_contact
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T02:26:25.13085+00:00
-- url     : https://prove2.me/submissions/0658e6c2-a9e2-41b9-a450-98a48007b7b7

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination

noncomputable section
open Filter
open scoped Topology
open WeierstrassEllipticZeta

private lemma sigma_translate (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (hne : ∀ z : ℂ, z ∉ L.lattice → S.sigma z ≠ 0)
    (hzeta : ∀ ω z : ℂ, ω ∈ L.lattice → z ∉ L.lattice →
      weierstrassZeta L (z + ω) = weierstrassZeta L z + zetaQuasiPeriod L ω)
    (ω : ℂ) (hω : ω ∈ L.lattice) :
    ∃ c : ℂ, c ≠ 0 ∧ (fun z => S.sigma (z + ω)) =
      (fun z => c * Complex.exp (zetaQuasiPeriod L ω * z) * S.sigma z) := by
  let η := zetaQuasiPeriod L ω
  have hshift (z : ℂ) (hz : z ∉ L.lattice) : z + ω ∉ L.lattice := by
    intro h
    exact hz (by simpa using L.lattice.sub_mem h hω)
  have hd (z : ℂ) (hz : z ∉ L.lattice) :
      HasDerivAt (fun w => S.sigma (w + ω) / S.sigma w * Complex.exp (-η * w)) 0 z := by
    have h1 : HasDerivAt (fun w => S.sigma (w + ω))
        ((weierstrassZeta L z + η) * S.sigma (z + ω)) z := by
      simpa [hzeta ω z hω hz, η] using!
        (S.hasDerivAt (z + ω) (hshift z hz)).comp z ((hasDerivAt_id z).add_const ω)
    have h2 := ((hasDerivAt_id z).const_mul (-η)).cexp
    convert! ((h1.div (S.hasDerivAt z hz) (hne z hz)).mul h2) using 1
    simp only [Pi.div_apply, id_eq]
    field_simp
    ring
  obtain ⟨c, hc⟩ := L.isClosed_lattice.isOpen_compl.exists_is_const_of_deriv_eq_zero
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv)
  have heq (z : ℂ) (hz : z ∉ L.lattice) :
      S.sigma (z + ω) = c * Complex.exp (η * z) * S.sigma z := by
    have h := congrArg (fun w : ℂ => w * Complex.exp (η * z) * S.sigma z) (hc z hz)
    simpa [mul_assoc, ← Complex.exp_add, hne z hz] using h
  let u := L.ω₁ / 2
  have hu : u ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have hc0 : c ≠ 0 := by
    intro hc0
    have h := heq u hu
    simp only [hc0, zero_mul] at h
    exact hne (u + ω) (hshift u hu) h
  have hall : (fun z => S.sigma (z + ω)) =
      (fun z => c * Complex.exp (η * z) * S.sigma z) := by
    apply AnalyticOnNhd.eq_of_eventuallyEq
      (show AnalyticOnNhd ℂ (fun z => S.sigma (z + ω)) Set.univ from
        fun z _ => (S.entire.analyticAt (z + ω)).comp (f := fun w : ℂ => w + ω) (x := z)
          (analyticAt_id.add analyticAt_const))
      (show AnalyticOnNhd ℂ (fun z => c * Complex.exp (η * z) * S.sigma z) Set.univ from
        fun z _ => ((analyticAt_const.mul
          (analyticAt_const.mul analyticAt_id).cexp).mul (S.entire.analyticAt z)))
      (z₀ := u)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hu] with z hz
    exact heq z hz
  exact ⟨c, hc0, hall⟩

private lemma sigma_order_le_one (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (hne : ∀ z : ℂ, z ∉ L.lattice → S.sigma z ≠ 0)
    (hzeta : ∀ ω z : ℂ, ω ∈ L.lattice → z ∉ L.lattice →
      weierstrassZeta L (z + ω) = weierstrassZeta L z + zetaQuasiPeriod L ω)
    (z : ℂ) : analyticOrderAt S.sigma z ≤ 1 := by
  by_cases hz : z ∈ L.lattice
  · obtain ⟨c, hc, heq⟩ := sigma_translate L S hne hzeta z hz
    have h0 : analyticOrderAt S.sigma 0 = 1 :=
      (S.entire.analyticAt 0).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
        S.zero (by rw [S.deriv_zero.deriv]; exact one_ne_zero)
    have hshift : analyticOrderAt (fun w => S.sigma (w + z)) 0 =
        analyticOrderAt S.sigma z := by
      simpa only [Function.comp_def, zero_add] using
        (analyticOrderAt_comp_of_deriv_ne_zero
          (show AnalyticAt ℂ (fun w : ℂ => w + z) 0 from
            analyticAt_id.add analyticAt_const)
          (by simpa using one_ne_zero : deriv (fun w : ℂ => w + z) 0 ≠ 0)
          (f := S.sigma))
    rw [← hshift, heq]
    have hunit : AnalyticAt ℂ (fun w : ℂ => c * Complex.exp (zetaQuasiPeriod L z * w)) 0 :=
      analyticAt_const.mul (analyticAt_const.mul analyticAt_id).cexp
    change analyticOrderAt ((fun w : ℂ => c * Complex.exp (zetaQuasiPeriod L z * w)) *
      S.sigma) 0 ≤ 1
    rw [analyticOrderAt_mul hunit (S.entire.analyticAt 0),
      hunit.analyticOrderAt_eq_zero.mpr (by simpa using hc), h0, zero_add]
  · rw [(S.entire.analyticAt z).analyticOrderAt_eq_zero.mpr (hne z hz)]
    exact zero_le

private lemma wp_order_le_two (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (hne : ∀ z : ℂ, z ∉ L.lattice → S.sigma z ≠ 0)
    (hzeta : ∀ ω z : ℂ, ω ∈ L.lattice → z ∉ L.lattice →
      weierstrassZeta L (z + ω) = weierstrassZeta L z + zetaQuasiPeriod L ω)
    (hadd : ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice →
      S.sigma (z + v) * S.sigma (z - v) =
        (L.weierstrassP v - L.weierstrassP z) * S.sigma z ^ 2 * S.sigma v ^ 2)
    (z : ℂ) (hz : z ∉ L.lattice) :
    analyticOrderAt (fun w => L.weierstrassP w - L.weierstrassP z) z ≤ 2 := by
  have hwp := L.analyticOnNhd_weierstrassP z hz
  have hwpsub : AnalyticAt ℂ (fun w => L.weierstrassP z - L.weierstrassP w) z :=
    analyticAt_const.sub hwp
  have hsplus : AnalyticAt ℂ (fun w => S.sigma (w + z)) z :=
    (S.entire.analyticAt (z + z)).comp (f := fun w : ℂ => w + z) (x := z)
      (analyticAt_id.add analyticAt_const)
  have hsminus : AnalyticAt ℂ (fun w => S.sigma (w - z)) z :=
    (S.entire.analyticAt (z - z)).comp (f := fun w : ℂ => w - z) (x := z)
      (analyticAt_id.sub analyticAt_const)
  have hunit : AnalyticAt ℂ (fun w => S.sigma w ^ 2 * S.sigma z ^ 2) z :=
    (S.entire.analyticAt z).pow 2 |>.mul analyticAt_const
  have hunit0 : analyticOrderAt (fun w => S.sigma w ^ 2 * S.sigma z ^ 2) z = 0 :=
    hunit.analyticOrderAt_eq_zero.mpr (mul_ne_zero (pow_ne_zero _ (hne z hz))
      (pow_ne_zero _ (hne z hz)))
  have heq : (fun w => S.sigma (w + z) * S.sigma (w - z)) =ᶠ[𝓝 z]
      (fun w => (L.weierstrassP z - L.weierstrassP w) *
        (S.sigma w ^ 2 * S.sigma z ^ 2)) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    simpa only [mul_assoc] using hadd w z hw hz
  have hplus : analyticOrderAt (fun w => S.sigma (w + z)) z ≤ 1 := by
    have ho := analyticOrderAt_comp_of_deriv_ne_zero
      (show AnalyticAt ℂ (fun w : ℂ => w + z) z from
        analyticAt_id.add analyticAt_const)
      (by simpa using one_ne_zero : deriv (fun w : ℂ => w + z) z ≠ 0)
      (f := S.sigma)
    simpa only [Function.comp_def] using ho ▸ sigma_order_le_one L S hne hzeta (z + z)
  have hminus : analyticOrderAt (fun w => S.sigma (w - z)) z ≤ 1 := by
    have ho := analyticOrderAt_comp_of_deriv_ne_zero
      (show AnalyticAt ℂ (fun w : ℂ => w - z) z from
        analyticAt_id.sub analyticAt_const)
      (by simpa using one_ne_zero : deriv (fun w : ℂ => w - z) z ≠ 0)
      (f := S.sigma)
    simpa only [Function.comp_def] using ho ▸ sigma_order_le_one L S hne hzeta (z - z)
  have ho := analyticOrderAt_congr heq
  rw [show (fun w => S.sigma (w + z) * S.sigma (w - z)) =
      (fun w => S.sigma (w + z)) * (fun w => S.sigma (w - z)) from rfl,
    analyticOrderAt_mul hsplus hsminus] at ho
  rw [show (fun w => (L.weierstrassP z - L.weierstrassP w) *
      (S.sigma w ^ 2 * S.sigma z ^ 2)) =
      (fun w => L.weierstrassP z - L.weierstrassP w) *
        (fun w => S.sigma w ^ 2 * S.sigma z ^ 2) from rfl,
    analyticOrderAt_mul hwpsub hunit, hunit0, add_zero] at ho
  have hneg : analyticOrderAt (fun w => L.weierstrassP z - L.weierstrassP w) z =
      analyticOrderAt (fun w => L.weierstrassP w - L.weierstrassP z) z := by
    rw [show (fun w => L.weierstrassP z - L.weierstrassP w) =
        -(fun w => L.weierstrassP w - L.weierstrassP z) from by
          funext w; simp only [Pi.neg_apply, neg_sub], analyticOrderAt_neg]
  rw [← hneg, ← ho]
  calc
    _ ≤ (1 : ℕ∞) + 1 := add_le_add hplus hminus
    _ = 2 := by norm_num

private lemma polynomial_eval_order (p : Polynomial ℂ) (hp : p ≠ 0) (a : ℂ) :
    analyticOrderAt (fun w => p.eval w) a = (p.rootMultiplicity a : ℕ∞) := by
  obtain ⟨q, hq, hqroot⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp a
  have hqa : q.eval a ≠ 0 := by
    simpa only [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot] using hqroot
  rw [(AnalyticOnNhd.eval_polynomial p a (Set.mem_univ a)).analyticOrderAt_eq_natCast]
  refine ⟨fun w => q.eval w, AnalyticOnNhd.eval_polynomial q a (Set.mem_univ a), hqa, ?_⟩
  filter_upwards [] with w
  simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, smul_eq_mul] using congrArg (Polynomial.eval w) hq

/-- Local contact of a polynomial in the elliptic coordinate forces root multiplicity.
The explicit sigma and quasi-period identities are supplied by the established analytic theory. -/
theorem solution
    (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (hne : ∀ z : ℂ, z ∉ L.lattice → S.sigma z ≠ 0)
    (hzeta : ∀ ω z : ℂ, ω ∈ L.lattice → z ∉ L.lattice →
      weierstrassZeta L (z + ω) = weierstrassZeta L z + zetaQuasiPeriod L ω)
    (hadd : ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice →
      S.sigma (z + v) * S.sigma (z - v) =
        (L.weierstrassP v - L.weierstrassP z) * S.sigma z ^ 2 * S.sigma v ^ 2)
    (p : Polynomial ℂ) (z : ℂ) (hz : z ∉ L.lattice) (U : ℕ)
    (hcontact : ∀ j < 2 * U + 1,
      iteratedDeriv j (fun w => p.eval (L.weierstrassP w)) z = 0) :
    (Polynomial.X - Polynomial.C (L.weierstrassP z)) ^ (U + 1) ∣ p := by
  by_cases hp : p = 0
  · simp [hp]
  have hwp := L.analyticOnNhd_weierstrassP z hz
  have horder := wp_order_le_two L S hne hzeta hadd z hz
  have hfinite : analyticOrderAt (fun w => L.weierstrassP w - L.weierstrassP z) z ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) horder
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hr2 : r ≤ 2 := by
    rw [← hr] at horder
    exact_mod_cast horder
  have hpw : AnalyticAt ℂ (fun w => p.eval w) (L.weierstrassP z) :=
    AnalyticOnNhd.eval_polynomial p (L.weierstrassP z) (Set.mem_univ _)
  have heval : AnalyticAt ℂ (fun w => p.eval (L.weierstrassP w)) z := hpw.comp hwp
  have ho := hpw.analyticOrderAt_comp hwp
  rw [polynomial_eval_order p hp, ← hr] at ho
  have hlarge : ((2 * U + 1 : ℕ) : ℕ∞) ≤
      analyticOrderAt (fun w => p.eval (L.weierstrassP w)) z :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero heval).mpr hcontact
  change ((2 * U + 1 : ℕ) : ℕ∞) ≤
    analyticOrderAt ((fun w => p.eval w) ∘ L.weierstrassP) z at hlarge
  rw [ho, ← ENat.natCast_mul] at hlarge
  have hnat : 2 * U + 1 ≤ p.rootMultiplicity (L.weierstrassP z) * r := by
    exact_mod_cast hlarge
  apply (Polynomial.le_rootMultiplicity_iff hp).mp
  have := Nat.mul_le_mul_left (p.rootMultiplicity (L.weierstrassP z)) hr2
  omega
