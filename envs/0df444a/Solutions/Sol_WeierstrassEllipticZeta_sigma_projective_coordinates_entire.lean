-- Prove2me | solution 1 for WeierstrassEllipticZeta.sigma_projective_coordinates_entire
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T14:20:59.213346+00:00
-- url     : https://prove2.me/submissions/434db240-1086-4d71-aae4-332c65cbe0f3

import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_weierstrassZeta_add_period
import Theorems.Thm_WeierstrassEllipticZeta_sigma_addition_from_differential
import Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_formula
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section
open Filter Set
open scoped Topology

open WeierstrassEllipticZeta

private lemma p2m_sigma_translation_factor (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (hne : ∀ z : ℂ, z ∉ L.lattice → S.sigma z ≠ 0)
    (hzeta : ∀ ω z : ℂ, ω ∈ L.lattice → z ∉ L.lattice →
      weierstrassZeta L (z + ω) = weierstrassZeta L z + zetaQuasiPeriod L ω)
    (ω : ℂ) (hω : ω ∈ L.lattice) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z : ℂ, S.sigma (z + ω) =
      c * Complex.exp (zetaQuasiPeriod L ω * z) * S.sigma z := by
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
  exact ⟨c, hc0, fun z => congrFun hall z⟩

private lemma p2m_sigma_second_deriv (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (hζ : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (z : ℂ) (hz : z ∉ L.lattice) :
    deriv (deriv D.sigma) z =
      (weierstrassZeta L z ^ 2 - L.weierstrassP z) * D.sigma z := by
  have heq : deriv D.sigma =ᶠ[𝓝 z] fun w ↦ weierstrassZeta L w * D.sigma w := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact (D.hasDerivAt w hw).deriv
  have h := ((hζ z hz).mul (D.hasDerivAt z hz)).congr_of_eventuallyEq heq
  rw [h.deriv]
  ring

private lemma p2m_sigma_third_deriv (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (hζ : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (z : ℂ) (hz : z ∉ L.lattice) :
    deriv (deriv (deriv D.sigma)) z =
      (weierstrassZeta L z ^ 3 - 3 * weierstrassZeta L z * L.weierstrassP z -
        L.derivWeierstrassP z) * D.sigma z := by
  have heq : deriv (deriv D.sigma) =ᶠ[𝓝 z]
      fun w ↦ (weierstrassZeta L w ^ 2 - L.weierstrassP w) * D.sigma w := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact p2m_sigma_second_deriv L D hζ w hw
  have hp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds hz)).hasDerivAt
  have h := ((((hζ z hz).pow 2).sub hp).mul
    (D.hasDerivAt z hz)).congr_of_eventuallyEq heq
  rw [h.deriv]
  simp only [Pi.sub_apply, Pi.pow_apply]
  ring

private lemma p2m_sigma_simple_zero_at_period (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (hne : ∀ z : ℂ, z ∉ L.lattice → D.sigma z ≠ 0)
    (ω : ℂ) (hω : ω ∈ L.lattice) :
    D.sigma ω = 0 ∧ deriv D.sigma ω ≠ 0 := by
  obtain ⟨c, hc, htrans⟩ := p2m_sigma_translation_factor L D hne
    (weierstrassZeta_add_period L) ω hω
  refine ⟨?_, ?_⟩
  · simpa [D.zero] using htrans 0
  · have hleft : HasDerivAt (fun w : ℂ => D.sigma (w + ω)) (deriv D.sigma ω) 0 := by
      simpa using! (D.entire (0 + ω)).hasDerivAt.comp 0 ((hasDerivAt_id (0 : ℂ)).add_const ω)
    have hright : HasDerivAt
        (fun w : ℂ => c * Complex.exp (zetaQuasiPeriod L ω * w) * D.sigma w) c 0 := by
      convert! (((hasDerivAt_id (0 : ℂ)).const_mul (zetaQuasiPeriod L ω)).cexp.const_mul c).mul
        D.deriv_zero using 1
      simp [D.zero]
    have hder : deriv D.sigma ω = c :=
      hleft.unique (hright.congr_of_eventuallyEq (Filter.Eventually.of_forall htrans))
    simpa only [hder] using hc

theorem solution (L : PeriodPair)
    (D : EllipticSigmaDifferentialData L) :
    ∃ S : Fin 5 → ℂ → ℂ,
      (∀ j, AnalyticOnNhd ℂ (S j) Set.univ) ∧
      (∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
        S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
          weierstrassZeta L z,
          L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j) ∧
      (∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0) ∧ S 2 0 = -2 := by
  let S : Fin 5 → ℂ → ℂ := ![
    fun z => D.sigma z ^ 3,
    fun z => D.sigma z * (deriv D.sigma z ^ 2 - D.sigma z * deriv (deriv D.sigma) z),
    fun z => -2 * deriv D.sigma z ^ 3 +
      3 * D.sigma z * deriv D.sigma z * deriv (deriv D.sigma) z -
      D.sigma z ^ 2 * deriv (deriv (deriv D.sigma)) z,
    fun z => D.sigma z ^ 2 * deriv D.sigma z,
    fun z => -(deriv D.sigma z ^ 2 * deriv (deriv D.sigma) z) +
      D.sigma z * (2 * deriv (deriv D.sigma) z ^ 2 -
        deriv D.sigma z * deriv (deriv (deriv D.sigma)) z)]
  have hζ := hasDerivAt_weierstrassZeta L
  have hne := (sigma_addition_from_differential L D hζ (zeta_addition_formula L)).1
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · intro j z _
    have h0 := D.entire.analyticAt z
    have h1 := h0.deriv
    have h2 := h1.deriv
    have h3 := h2.deriv
    fin_cases j
    · exact h0.pow 3
    · exact h0.mul ((h1.pow 2).sub (h0.mul h2))
    · exact (((analyticAt_const.mul (h1.pow 3)).add
        (((analyticAt_const.mul h0).mul h1).mul h2))).sub ((h0.pow 2).mul h3)
    · exact (h0.pow 2).mul h1
    · exact (((h1.pow 2).mul h2).neg).add
        (h0.mul ((analyticAt_const.mul (h2.pow 2)).sub (h1.mul h3)))
  · intro z hz j
    have h1 := (D.hasDerivAt z hz).deriv
    have h2 := p2m_sigma_second_deriv L D hζ z hz
    have h3 := p2m_sigma_third_deriv L D hζ z hz
    fin_cases j <;> simp [S, h1, h2, h3] <;> ring
  · intro z
    by_cases hz : D.sigma z = 0
    · have hzL : z ∈ L.lattice := by
        by_contra h
        exact hne z h hz
      have hd := (p2m_sigma_simple_zero_at_period L D hne z hzL).2
      refine ⟨2, ?_⟩
      simpa [S, hz] using mul_ne_zero (by norm_num : (-2 : ℂ) ≠ 0) (pow_ne_zero 3 hd)
    · refine ⟨0, ?_⟩
      simpa [S] using pow_ne_zero 3 hz
  · change -2 * deriv D.sigma 0 ^ 3 +
      3 * D.sigma 0 * deriv D.sigma 0 * deriv (deriv D.sigma) 0 -
      D.sigma 0 ^ 2 * deriv (deriv (deriv D.sigma)) 0 = -2
    norm_num [D.zero, D.deriv_zero.deriv]

