-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_cleared_entire_data
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T14:33:42.956738+00:00
-- url     : https://prove2.me/submissions/6cfac082-b03f-4c49-81c8-59505b1b5ac6

import Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_period_jet_systems
import Mathlib.Tactic.FinCases
import Theorems.Thm_WeierstrassEllipticZeta_period_translate_polynomial_jets
import Theorems.Thm_TranscendenceTheory_polynomial_clear_denominators_bound
import Theorems.Thm_TranscendenceTheory_bivariate_monic_reduction_bound

noncomputable section
set_option maxHeartbeats 800000
open MvPolynomial
open scoped Polynomial
namespace WeierstrassEllipticZeta

private def flatten : ℤ[X][X] →+* MvPolynomial (Fin 2) ℤ :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom C (X 0)) (X 1)

private lemma flatten_eval (p : ℤ[X][X]) (θ ν : ℂ) :
    eval₂ (Int.castRingHom ℂ) ![θ, ν] (flatten p) =
      p.eval₂ (Polynomial.aeval θ).toRingHom ν := by
  have h : (eval₂Hom (Int.castRingHom ℂ) ![θ, ν]).comp flatten =
      Polynomial.eval₂RingHom (Polynomial.aeval θ).toRingHom ν := by
    apply Polynomial.ringHom_ext
    · intro q
      have hq : (eval₂Hom (Int.castRingHom ℂ) ![θ, ν]).comp
          (Polynomial.eval₂RingHom C (X 0)) = (Polynomial.aeval θ).toRingHom := by
        apply Polynomial.ringHom_ext <;> simp
      simpa [flatten] using congrArg (fun f : ℤ[X] →+* ℂ => f q) hq
    · simp [flatten]
  exact congrArg (fun f : ℤ[X][X] →+* ℂ => f p) h

private theorem period_arithmetic_jet_systems (L : PeriodPair) (ω z θ ν : ℂ)
    (hzeta : ∀ w : ℂ, w ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP w) w)
    (hperiod : ∀ (w : ℂ) (a : ℤ), w ∉ L.lattice →
      L.weierstrassP (w + a * ω) = L.weierstrassP w ∧
      weierstrassZeta L (w + a * ω) = weierstrassZeta L w + a * zetaQuasiPeriod L ω)
    (hregular : ∀ a : ℤ, z + a * ω ∉ L.lattice)
    (g : ℤ[X][X]) (hg : g.Monic) (hg_degree : 0 < g.natDegree)
    (hg_zero : g.eval₂ (Polynomial.aeval θ).toRingHom ν = 0)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (hdata : ∀ i : Fin 7, ∃ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν =
        Polynomial.aeval θ d * periodJetCoordinates L ω z i) :
    PeriodArithmeticJetSystemData L ω z θ ν g d := by
  classical
  choose p hp using hdata
  let s : Fin 7 → MvPolynomial (Fin 2) ℤ := fun i => flatten (p i)
  let q : MvPolynomial (Fin 2) ℤ := flatten (Polynomial.C d)
  let D := 1 + q.totalDegree + Finset.univ.sup fun i => (s i).totalDegree
  let h := 1 + (∑ m ∈ q.support, (q.coeff m).natAbs) +
    Finset.univ.sup fun i => ∑ m ∈ (s i).support, ((s i).coeff m).natAbs
  let Bg := g.support.sup fun j => (g.coeff j).natDegree
  let Hg := 1 + ∑ j ∈ g.support, ∑ k ∈ (g.coeff j).support,
    ((g.coeff j).coeff k).natAbs
  have hDpos : 0 < D := by dsimp [D]; omega
  have hhpos : 0 < h := by dsimp [h]; omega
  have hHg : 1 ≤ Hg := by dsimp [Hg]; omega
  have hsD (i : Fin 7) : (s i).totalDegree ≤ D := by
    have := Finset.le_sup (f := fun i => (s i).totalDegree) (Finset.mem_univ i)
    dsimp [D]; omega
  have hqD : q.totalDegree ≤ D := by dsimp [D]; omega
  have hsh (i : Fin 7) : (∑ m ∈ (s i).support, ((s i).coeff m).natAbs) ≤ h := by
    have := Finset.le_sup (f := fun i => ∑ m ∈ (s i).support,
      ((s i).coeff m).natAbs) (Finset.mem_univ i)
    dsimp [h]; omega
  have hqh : (∑ m ∈ q.support, (q.coeff m).natAbs) ≤ h := by dsimp [h]; omega
  have hBg (i : ℕ) : (g.coeff i).natDegree ≤ Bg := by
    by_cases hi : i ∈ g.support
    · exact Finset.le_sup (f := fun i => (g.coeff i).natDegree) hi
    · simp [Polynomial.notMem_support_iff.mp hi]
  let B := (Bg + 1) * (7 * D)
  let H := h ^ 7 * Hg ^ (7 * D + 1)
  refine ⟨B, H, by dsimp [B]; positivity, by dsimp [H]; positivity, ?_⟩
  intro a M L₀ T
  dsimp only
  let I := Fin (L₀ + 1) × Fin (M + 1) × Fin (M + 1)
  let K : ℕ → ℕ := fun n => L₀ + 2 * M + n
  have hall (n : Fin T) (i : I) : ∃ r : ℤ[X][X],
      r.natDegree < g.natDegree ∧ (∀ j, (r.coeff j).natDegree ≤ B * K n) ∧
      (∑ j ∈ r.support, ∑ k ∈ (r.coeff j).support, ((r.coeff j).coeff k).natAbs) ≤
        n.val.factorial * 24 ^ K n * (1 + a.natAbs) ^ (L₀ + M) * H ^ (K n + 1) ∧
      r.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d ^ (7 * K n) *
        iteratedDeriv n (fun w => w ^ i.1.val * L.weierstrassP w ^ i.2.1.val *
          weierstrassZeta L w ^ i.2.2.val) (z + a * ω) := by
    let P := periodJetDerivation^[n.val] (periodJetPolynomial a i.1 i.2.1 i.2.2)
    have hj := period_translate_polynomial_jets L ω hzeta hperiod a i.1 i.2.1 i.2.2 n
    have hsum : i.1.val + i.2.1.val + i.2.2.val + n.val ≤ K n := by
      have := i.1.isLt; have := i.2.1.isLt; have := i.2.2.isLt
      dsimp [K]; omega
    have hsum' : i.1.val + i.2.2.val ≤ L₀ + M := by
      have := i.1.isLt; have := i.2.2.isLt; omega
    have hP : P.totalDegree ≤ K n := hj.1.trans hsum
    obtain ⟨r, hrD, hrh, hreval⟩ := TranscendenceTheory.polynomial_clear_denominators_bound
      (A := ℂ) P (fun _ => K n) (fun _ => D) (fun _ => h) s (fun _ => q)
      (fun j => (degreeOf_le_totalDegree P j).trans hP) hsD (fun _ => hqD) hsh (fun _ => hqh)
    have hrD' : r.totalDegree ≤ 7 * D * K n := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hrD
    have hrh' : (∑ m ∈ r.support, (r.coeff m).natAbs) ≤
        (n.val.factorial * 24 ^ K n * (1 + a.natAbs) ^ (L₀ + M)) * h ^ (7 * K n) := by
      apply hrh.trans
      have hbase := hj.2.1
      have hb := Nat.mul_le_mul
        (Nat.mul_le_mul_left n.val.factorial
          (Nat.pow_le_pow_right (by norm_num : 1 ≤ (24 : ℕ)) hsum))
        (Nat.pow_le_pow_right (by omega : 1 ≤ 1 + a.natAbs) hsum')
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
        Nat.mul_comm (K n) 7] using Nat.mul_le_mul_right (h ^ (K n * 7)) (hbase.trans hb)
    obtain ⟨r', hy, hx, hlen, heval⟩ :=
      TranscendenceTheory.bivariate_monic_reduction_bound g hg hg_degree Bg hBg r
    refine ⟨r', hy, ?_, ?_, ?_⟩
    · intro j
      simpa [B, mul_assoc] using (hx j).trans (Nat.mul_le_mul_left (Bg + 1) hrD')
    · apply hlen.trans
      change _ ≤ _ * H ^ (K n + 1)
      have he : r.totalDegree + 1 ≤ (7 * D + 1) * (K n + 1) := by nlinarith [hrD']
      calc
        _ ≤ ((n.val.factorial * 24 ^ K n * (1 + a.natAbs) ^ (L₀ + M)) *
            h ^ (7 * K n)) * Hg ^ ((7 * D + 1) * (K n + 1)) :=
          Nat.mul_le_mul hrh' (Nat.pow_le_pow_right hHg he)
        _ ≤ ((n.val.factorial * 24 ^ K n * (1 + a.natAbs) ^ (L₀ + M)) *
            h ^ (7 * (K n + 1))) * Hg ^ ((7 * D + 1) * (K n + 1)) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right (by omega) (by omega)))
        _ = _ := by simp [H, mul_pow, ← pow_mul, mul_assoc]
    · have he := heval ℂ (Polynomial.aeval θ).toRingHom ν hg_zero
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X] at he
      apply he.trans
      have hqeval : eval₂ (Int.castRingHom ℂ) ![θ, ν] q = Polynomial.aeval θ d := by
        simpa [q] using flatten_eval (Polynomial.C d) θ ν
      have hseval (j : Fin 7) : (eval₂Hom (Int.castRingHom ℂ) ![θ, ν]) (s j) =
          (eval₂Hom (Int.castRingHom ℂ) ![θ, ν]) q * periodJetCoordinates L ω z j := by
        change eval₂ _ _ (flatten (p j)) = _
        rw [flatten_eval, hp, show (eval₂Hom (Int.castRingHom ℂ) ![θ, ν]) q = _ from hqeval]
      have hv := hreval (eval₂Hom (Int.castRingHom ℂ) ![θ, ν])
        (periodJetCoordinates L ω z) hseval
      have hz : z ∉ L.lattice := by simpa using hregular 0
      change eval₂ (Int.castRingHom ℂ) ![θ, ν] r =
        (∏ _ : Fin 7, eval₂ (Int.castRingHom ℂ) ![θ, ν] q ^ K n) *
          eval₂ (Int.castRingHom ℂ) (periodJetCoordinates L ω z) P at hv
      dsimp only [P] at hv
      simpa only [hqeval, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← pow_mul, Nat.mul_comm, ← hj.2.2 z hz] using hv
  choose R hRy hRx hRH hReval using hall
  refine ⟨R, fun n i => ⟨hRy n i, hRx n i, hRH n i⟩, hReval, ?_⟩
  intro c
  have hZ : AnalyticAt ℂ (weierstrassZeta L) (z + a * ω) :=
    (show DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ from
      fun w hw => (hzeta w hw).differentiableAt.differentiableWithinAt).analyticOnNhd
      L.isClosed_lattice.isOpen_compl _ (hregular a)
  have hmono (i : I) : AnalyticAt ℂ (fun w =>
      w ^ i.1.val * L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val)
        (z + a * ω) :=
    ((analyticAt_id.pow _).mul ((L.analyticOnNhd_weierstrassP _ (hregular a)).pow _)).mul
      (hZ.pow _)
  have hsum (n : Fin T) : (∑ i, (R n i).eval₂ (Polynomial.aeval θ).toRingHom ν * c i) =
      Polynomial.aeval θ d ^ (7 * K n) * iteratedDeriv n (fun w =>
        ∑ i, c i * w ^ i.1.val * L.weierstrassP w ^ i.2.1.val *
          weierstrassZeta L w ^ i.2.2.val) (z + a * ω) := by
    simp_rw [mul_assoc (c _)]
    rw [iteratedDeriv_fun_sum (f := fun i w => c i *
      (w ^ i.1.val * L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val))
        (fun i _ => (analyticAt_const.mul (hmono i)).contDiffAt)]
    simp only [iteratedDeriv_const_mul_field, Finset.mul_sum, hReval]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [mul_assoc]
    ring
  constructor
  · intro he n hn
    exact (mul_eq_zero.mp ((hsum ⟨n, hn⟩).symm.trans (he ⟨n, hn⟩))).resolve_left
      (pow_ne_zero _ hd)
  · intro he n
    rw [hsum, he n n.isLt, mul_zero]

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_zeta_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (h_wp_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
        -4 * (L.weierstrassP z + L.weierstrassP v) *
          (L.weierstrassP v - L.weierstrassP z) ^ 2 +
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2)
    (θ : ℂ) (hθ : Transcendental ℚ θ)
    (ν : ℂ)
    (g : ℤ[X][X]) (hg_monic : g.Monic) (hg_degree : 0 < g.natDegree)
    (hg_kernel : ∀ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = 0 ↔ g ∣ p)
    (h_jet_systems : ReducedArithmeticJetSystemData L θ ν g)
    (h_interpolation : AuxiliaryGridInterpolationData ω u₁ u₂)
    (h_regularization : EllipticRegularizationData L ω u₁ u₂)
    (h_cleared_entire : ClearedAdditionEntireData L ω u₁ u₂)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_data : ∀ i : Fin 18, ∃ p : ℤ[X][X],
      p.natDegree < g.natDegree ∧
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂] i)) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∃ S : TranscendenceTheory.ComplexAuxiliarySystem
          θ ν a ((3 + ‖θ‖ + ‖ν‖) * a) c N,
          S.yDegree < g.natDegree := by
  have hperiod (z : ℂ) (a : ℤ) (hz : z ∉ L.lattice) :=
    And.intro (h_grid.period_values z a hz).1 (h_grid.period_values z a hz).2.2
  have hregular (a : ℤ) : u₁ / 2 + a * ω ∉ L.lattice := by
    simpa [integerGridPoint, add_comm] using h_grid.shifted_regular ![0, 0, a]
  have hg_zero := (hg_kernel g).2 (dvd_refl g)
  have hdata : ∀ i : Fin 7, ∃ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν =
        Polynomial.aeval θ d * periodJetCoordinates L ω (u₁ / 2) i := by
    intro i
    fin_cases i
    · obtain ⟨p, _, hp⟩ := h_data 4
      exact ⟨p, by simpa [periodJetCoordinates] using hp⟩
    · obtain ⟨p, _, hp⟩ := h_data 2
      exact ⟨p, by simpa [periodJetCoordinates] using hp⟩
    · obtain ⟨p, _, hp⟩ := h_data 3
      exact ⟨p, by simpa [periodJetCoordinates] using hp⟩
    · obtain ⟨p, _, hp⟩ := h_data 6
      exact ⟨p, by simpa [periodJetCoordinates] using hp⟩
    · obtain ⟨p, _, hp⟩ := h_data 7
      exact ⟨p, by simpa [periodJetCoordinates] using hp⟩
    · obtain ⟨p, _, hp⟩ := h_data 8
      exact ⟨p, by simpa [periodJetCoordinates] using hp⟩
    · obtain ⟨p, _, hp⟩ := h_data 9
      exact ⟨p, by simpa [periodJetCoordinates] using hp⟩
  have h_period_jets := period_arithmetic_jet_systems L ω (u₁ / 2) θ ν
    h_zeta_deriv hperiod hregular g hg_monic hg_degree hg_zero d hd hdata
  exact exists_complex_auxiliary_systems_from_period_jet_systems L ω u₁ u₂ h_grid
    h_zeta_deriv h_zeta_addition h_wp_addition θ hθ ν g hg_monic hg_degree hg_kernel
    h_jet_systems h_interpolation h_regularization h_cleared_entire d hd h_period_jets h_data
