-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_extension_projective_chart_cover
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T17:12:59.288212+00:00
-- url     : https://prove2.me/submissions/112f7518-e4d8-4248-9e64-60478b9da5aa

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionChartLocus
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section
open Filter Set TranscendenceTheory
open scoped Topology
open WeierstrassEllipticZeta

private lemma sigma_second_deriv (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
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

private lemma sigma_third_deriv (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (hζ : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (z : ℂ) (hz : z ∉ L.lattice) :
    deriv (deriv (deriv D.sigma)) z =
      (weierstrassZeta L z ^ 3 - 3 * weierstrassZeta L z * L.weierstrassP z -
        L.derivWeierstrassP z) * D.sigma z := by
  have heq : deriv (deriv D.sigma) =ᶠ[𝓝 z]
      fun w ↦ (weierstrassZeta L w ^ 2 - L.weierstrassP w) * D.sigma w := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact sigma_second_deriv L D hζ w hw
  have hp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds hz)).hasDerivAt
  have h := ((((hζ z hz).pow 2).sub hp).mul
    (D.hasDerivAt z hz)).congr_of_eventuallyEq heq
  rw [h.deriv]
  simp only [Pi.sub_apply, Pi.pow_apply]
  ring

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (P : GraphQuotientExtension L.lattice η → ProjectiveExtensionLocus L.g₂ L.g₃)
    (hP : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (P ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv) :
    (∀ z : ℂ, S 0 z ≠ 0 ∨ S 2 z ≠ 0) ∧
      (∀ (e : GraphQuotientExtension L.lattice η) (v : Fin 5 → ℂ) (hv : v ≠ 0),
        Projectivization.mk ℂ v hv = (P e).val → v 0 ≠ 0 ∨ v 2 ≠ 0) ∧
      ∃ A : GraphQuotientExtension L.lattice η → ProjectiveExtensionChartLocus L.g₂ L.g₃,
        ∀ e, (A e).val = P e := by
  let J : Fin 5 → ℂ → ℂ := ![
    fun z => D.sigma z ^ 3,
    fun z => D.sigma z * (deriv D.sigma z ^ 2 - D.sigma z * deriv (deriv D.sigma) z),
    fun z => -2 * deriv D.sigma z ^ 3 +
      3 * D.sigma z * deriv D.sigma z * deriv (deriv D.sigma) z -
      D.sigma z ^ 2 * deriv (deriv (deriv D.sigma)) z,
    fun z => D.sigma z ^ 2 * deriv D.sigma z,
    fun z => -(deriv D.sigma z ^ 2 * deriv (deriv D.sigma) z) +
      D.sigma z * (2 * deriv (deriv D.sigma) z ^ 2 -
        deriv D.sigma z * deriv (deriv (deriv D.sigma)) z)]
  have hJa (j : Fin 5) : AnalyticOnNhd ℂ (J j) Set.univ := by
    intro z _
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
  have hSJ (j : Fin 5) : S j = J j := by
    apply AnalyticOnNhd.eq_of_eventuallyEq (hS j) (hJa j) (z₀ := L.ω₁ / 2)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
      L.ω₁_div_two_notMem_lattice] with z hz
    rw [hS_value z hz j]
    have h1 := (D.hasDerivAt z hz).deriv
    have h2 := sigma_second_deriv L D (hasDerivAt_weierstrassZeta L) z hz
    have h3 := sigma_third_deriv L D (hasDerivAt_weierstrassZeta L) z hz
    fin_cases j <;> simp [J, h1, h2, h3] <;> ring
  have hcover (z : ℂ) : S 0 z ≠ 0 ∨ S 2 z ≠ 0 := by
    by_cases hz : D.sigma z = 0
    · have hd : deriv D.sigma z ≠ 0 := by
        intro hd
        obtain ⟨j, hj⟩ := hS_ne z
        rw [hSJ j] at hj
        fin_cases j <;> simp [J, hz, hd] at hj
      right
      simpa [hSJ 2, J, hz] using
        mul_ne_zero (by norm_num : (-2 : ℂ) ≠ 0) (pow_ne_zero 3 hd)
    · left
      simpa [hSJ 0, J] using pow_ne_zero 3 hz
  have hrep (e : GraphQuotientExtension L.lattice η) (v : Fin 5 → ℂ) (hv : v ≠ 0)
      (hp : Projectivization.mk ℂ v hv = (P e).val) : v 0 ≠ 0 ∨ v 2 ≠ 0 := by
    obtain ⟨⟨z, u⟩, rfl⟩ := (extensionPeriodGraph L.lattice η).mkQ_surjective e
    obtain ⟨hvu, hpu⟩ := hP z u
    rw [hpu] at hp
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp hp
    rw [← hc]
    rcases hcover z with h0 | h2
    · left
      simpa [Units.smul_def, Pi.smul_apply, smul_eq_mul] using mul_ne_zero c.ne_zero h0
    · right
      simpa [Units.smul_def, Pi.smul_apply, smul_eq_mul] using mul_ne_zero c.ne_zero h2
  refine ⟨hcover, hrep, ?_⟩
  exact ⟨fun e => ⟨P e, hrep e (P e).val.rep (P e).val.rep_nonzero (P e).val.mk_rep⟩,
    fun _ => rfl⟩

