-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_reduced_arithmetic_jets
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T12:48:42.456717+00:00
-- url     : https://prove2.me/submissions/2a73cfea-3b84-413e-a9e1-447df7eab0d6

import Theorems.Thm_WeierstrassEllipticZeta_cleared_addition_jet_vanishing_iff
import Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_reduced_jet_systems
import Definitions.Def_WeierstrassEllipticZeta_ReducedJetSystems

noncomputable section

open scoped Polynomial

namespace WeierstrassEllipticZeta

private theorem reduced_jet_systems_of_reduced_jets
    (L : PeriodPair)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (hadd : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (θ ν : ℂ) (g : ℤ[X][X]) (h_reduced : ReducedArithmeticJetData L θ ν g) :
    ReducedArithmeticJetSystemData L θ ν g := by
  classical
  obtain ⟨B, H, hB, hH, h_reduced⟩ := h_reduced
  refine ⟨B, H, hB, hH, ?_⟩
  intro M L₀ T
  dsimp only
  intro s q d h hs hq hsH hqH
  let I := Fin (L₀ + 1) × Fin (M + 1) × Fin (M + 1)
  let k : ℕ → Fin 8 → ℕ := fun n =>
    ![L₀, 5 * M, 5 * M, 5 * M,
      L₀ + 5 * M + n, L₀ + 5 * M + n, L₀ + 5 * M + n, L₀ + 5 * M + n]
  have hall (n : Fin T) (i : I) := h_reduced M L₀ i.1 i.2.1 i.2.2 n
    (Nat.le_of_lt_succ i.1.isLt) (Nat.le_of_lt_succ i.2.1.isLt)
    (Nat.le_of_lt_succ i.2.2.isLt) s q d h hs hq hsH hqH
  choose R hRy hRx hRH hReval using hall
  refine ⟨R, fun n i => ⟨hRy n i, hRx n i, hRH n i⟩, ?_⟩
  intro v z hv hz hp hcoord
  have heval := fun n i => hReval n i v z hv hz hp hcoord
  refine ⟨heval, ?_⟩
  intro hm hnonzero c
  have hcancel := (cleared_addition_jet_vanishing_iff L hzeta hadd z v hz hv hp hm
    M T (fun i : I => i.1.val) (fun i : I => i.2.1.val)
      (fun i : I => i.2.2.val) c).2
  let Q : Fin T → ℂ := fun n =>
    ∏ a, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (q a) ^ k n a
  have hQ (n : Fin T) : Q n ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => pow_ne_zero _ (hnonzero a)
  have hsum (n : Fin T) :
      (∑ i, (R n i).eval₂ (Polynomial.aeval θ).toRingHom ν * c i) =
        Q n * ∑ i : I, c i * iteratedDeriv n
          (clearedAdditionMonomial L v M i.1 i.2.1 i.2.2) z := by
    simp only [heval, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change (Q n * _) * c i = Q n * (c i * _)
    ring
  constructor
  · intro hequations
    apply hcancel.mp
    intro n hn
    exact (mul_eq_zero.mp ((hsum ⟨n, hn⟩).symm.trans
      (hequations ⟨n, hn⟩))).resolve_left (hQ ⟨n, hn⟩)
  · intro hvanish n
    rw [hsum, hcancel.mpr hvanish n n.isLt, mul_zero]

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
    (h_reduced : ReducedArithmeticJetData L θ ν g)
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
  have h_jet_systems := reduced_jet_systems_of_reduced_jets L h_zeta_deriv h_zeta_addition
    θ ν g h_reduced
  exact exists_complex_auxiliary_systems_from_reduced_jet_systems L ω u₁ u₂ h_grid
    h_zeta_deriv h_zeta_addition h_wp_addition θ hθ ν g hg_monic hg_degree hg_kernel
    h_jet_systems d hd h_data
