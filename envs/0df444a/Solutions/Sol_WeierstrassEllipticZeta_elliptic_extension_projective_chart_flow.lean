-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_extension_projective_chart_flow
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T19:16:38.503826+00:00
-- url     : https://prove2.me/submissions/e0525c30-08b3-4fca-9937-74113b6d66b6

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_derivWeierstrassP
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

noncomputable section
open Filter
open scoped Topology
open WeierstrassEllipticZeta

private theorem regular_coordinate_derivatives
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (z : ℂ) (hz : z ∉ L.lattice) :
    ∀ j : Fin 5, deriv (S j) z = 3 * weierstrassZeta L z * S j z + D.sigma z ^ 3 *
      ![0, L.derivWeierstrassP z, 6 * L.weierstrassP z ^ 2 - L.g₂ / 2,
        -L.weierstrassP z,
        (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) * weierstrassZeta L z +
          3 * L.weierstrassP z * L.derivWeierstrassP z] j := by
  have hnear : ∀ᶠ w in 𝓝 z, w ∉ L.lattice := L.isClosed_lattice.isOpen_compl.mem_nhds hz
  have hσ := (D.hasDerivAt z hz).pow 3
  have hx : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    simpa using (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  have hy := hasDerivAt_derivWeierstrassP L z hz
  have ht := hasDerivAt_weierstrassZeta L z hz
  have hd (j : Fin 5) (d : ℂ)
      (h : HasDerivAt (fun w => D.sigma w ^ 3 *
        ![1, L.weierstrassP w, L.derivWeierstrassP w, weierstrassZeta L w,
          L.derivWeierstrassP w * weierstrassZeta L w + 2 * L.weierstrassP w ^ 2] j) d z) :
      deriv (S j) z = d :=
    (h.congr_of_eventuallyEq (hnear.mono fun w hw => hS_value w hw j)).deriv
  intro j
  fin_cases j <;> dsimp
  · rw [hd 0 _ (by simpa using! hσ), hS_value z hz 0]
    simp
    ring
  · rw [hd 1 _ (by simpa using! hσ.mul hx), hS_value z hz 1]
    simp
    ring
  · rw [hd 2 _ (by simpa using! hσ.mul hy), hS_value z hz 2]
    simp
    ring
  · rw [hd 3 _ (by simpa using! hσ.mul ht), hS_value z hz 3]
    simp
    ring
  · rw [hd 4 _ (by simpa using! hσ.mul ((hy.mul ht).add ((hx.pow 2).const_mul 2))),
      hS_value z hz 4]
    simp
    ring

private theorem cleared_chart_derivative_identities
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (z : ℂ) :
    ![deriv (S 1) z * S 0 z - S 1 z * deriv (S 0) z,
      deriv (S 2) z * S 0 z - S 2 z * deriv (S 0) z,
      deriv (S 3) z * S 0 z - S 3 z * deriv (S 0) z,
      deriv (S 0) z * S 2 z - S 0 z * deriv (S 2) z,
      deriv (S 1) z * S 2 z - S 1 z * deriv (S 2) z,
      deriv (S 4) z * S 2 z - S 4 z * deriv (S 2) z] =
    ![S 0 z * S 2 z, 6 * S 1 z ^ 2 - L.g₂ / 2 * S 0 z ^ 2, -S 0 z * S 1 z,
      -6 * S 1 z ^ 2 + L.g₂ / 2 * S 0 z ^ 2,
      -(1 / 2 : ℂ) * S 2 z ^ 2 - L.g₂ * S 0 z * S 1 z - 3 * L.g₃ / 2 * S 0 z ^ 2,
      -2 * L.g₂ * S 1 z ^ 2 - 3 * L.g₃ * S 0 z * S 1 z] := by
  let f : ℂ → Fin 6 → ℂ := fun w =>
    ![deriv (S 1) w * S 0 w - S 1 w * deriv (S 0) w,
      deriv (S 2) w * S 0 w - S 2 w * deriv (S 0) w,
      deriv (S 3) w * S 0 w - S 3 w * deriv (S 0) w,
      deriv (S 0) w * S 2 w - S 0 w * deriv (S 2) w,
      deriv (S 1) w * S 2 w - S 1 w * deriv (S 2) w,
      deriv (S 4) w * S 2 w - S 4 w * deriv (S 2) w]
  let g : ℂ → Fin 6 → ℂ := fun w =>
    ![S 0 w * S 2 w, 6 * S 1 w ^ 2 - L.g₂ / 2 * S 0 w ^ 2, -S 0 w * S 1 w,
      -6 * S 1 w ^ 2 + L.g₂ / 2 * S 0 w ^ 2,
      -(1 / 2 : ℂ) * S 2 w ^ 2 - L.g₂ * S 0 w * S 1 w - 3 * L.g₃ / 2 * S 0 w ^ 2,
      -2 * L.g₂ * S 1 w ^ 2 - 3 * L.g₃ * S 0 w * S 1 w]
  have ha (j : Fin 5) (w : ℂ) : AnalyticAt ℂ (S j) w := hS j w (Set.mem_univ w)
  have hf : AnalyticOnNhd ℂ f Set.univ := by
    intro w _
    apply AnalyticAt.pi
    intro i
    fin_cases i <;> dsimp [f] <;> fun_prop
  have hg : AnalyticOnNhd ℂ g Set.univ := by
    intro w _
    apply AnalyticAt.pi
    intro i
    fin_cases i <;> dsimp [g] <;> fun_prop
  have heq : f = g := by
    apply AnalyticOnNhd.eq_of_eventuallyEq hf hg (z₀ := L.ω₁ / 2)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
      L.ω₁_div_two_notMem_lattice] with w hw
    have hder := regular_coordinate_derivatives L D S hS_value w hw
    have hc := L.derivWeierstrassP_sq w hw
    ext i
    fin_cases i <;> simp [f, g, hder, hS_value w hw]
    · ring
    · ring
    · ring
    · ring
    · linear_combination 3 * D.sigma w ^ 6 * hc / 2
    · linear_combination 3 * D.sigma w ^ 6 * L.weierstrassP w * hc
  exact congrFun heq z

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j) :
    (∀ z : ℂ, S 0 z ≠ 0 →
      HasDerivAt (fun w => S 1 w / S 0 w) (S 2 z / S 0 z) z ∧
      HasDerivAt (fun w => S 2 w / S 0 w) (6 * (S 1 z / S 0 z) ^ 2 - L.g₂ / 2) z ∧
      HasDerivAt (fun w => S 3 w / S 0 w) (-S 1 z / S 0 z) z) ∧
    (∀ z : ℂ, S 2 z ≠ 0 →
      HasDerivAt (fun w => S 0 w / S 2 w)
        (-6 * (S 1 z / S 2 z) ^ 2 + L.g₂ / 2 * (S 0 z / S 2 z) ^ 2) z ∧
      HasDerivAt (fun w => S 1 w / S 2 w)
        (-(1 / 2 : ℂ) - L.g₂ * (S 0 z / S 2 z) * (S 1 z / S 2 z) -
          3 * L.g₃ / 2 * (S 0 z / S 2 z) ^ 2) z ∧
      HasDerivAt (fun w => S 4 w / S 2 w)
        (-2 * L.g₂ * (S 1 z / S 2 z) ^ 2 -
          3 * L.g₃ * (S 0 z / S 2 z) * (S 1 z / S 2 z)) z) := by
  have hd (j : Fin 5) (z : ℂ) : HasDerivAt (S j) (deriv (S j) z) z :=
    (hS j z (Set.mem_univ z)).differentiableAt.hasDerivAt
  constructor
  · intro z hz
    have hi := cleared_chart_derivative_identities L D S hS hS_value z
    refine ⟨((hd 1 z).div (hd 0 z) hz).congr_deriv ?_,
      ((hd 2 z).div (hd 0 z) hz).congr_deriv ?_,
      ((hd 3 z).div (hd 0 z) hz).congr_deriv ?_⟩
    · have h := congrFun hi 0
      dsimp at h
      rw [h]
      field_simp
    · have h := congrFun hi 1
      dsimp at h
      rw [h]
      field_simp
    · have h := congrFun hi 2
      dsimp at h
      rw [h]
      field_simp
  · intro z hz
    have hi := cleared_chart_derivative_identities L D S hS hS_value z
    refine ⟨((hd 0 z).div (hd 2 z) hz).congr_deriv ?_,
      ((hd 1 z).div (hd 2 z) hz).congr_deriv ?_,
      ((hd 4 z).div (hd 2 z) hz).congr_deriv ?_⟩
    · have h := congrFun hi 3
      dsimp at h
      rw [h]
      field_simp
    · have h := congrFun hi 4
      dsimp at h
      rw [h]
      field_simp
    · have h := congrFun hi 5
      dsimp at h
      rw [h]
      field_simp

