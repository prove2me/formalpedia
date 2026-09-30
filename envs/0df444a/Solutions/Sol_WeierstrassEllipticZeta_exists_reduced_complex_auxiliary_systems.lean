-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_reduced_complex_auxiliary_systems
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T10:14:35.6558+00:00
-- url     : https://prove2.me/submissions/4cd33167-9c39-4316-93d2-681062f660c8

import Theorems.Thm_TranscendenceTheory_integer_grid_geometry
import Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_on_regular_grids
import Theorems.Thm_WeierstrassEllipticZeta_weierstrassZeta_add_period
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.GCongr

noncomputable section

namespace WeierstrassEllipticZeta

private theorem integer_zeta_shift (L : PeriodPair) (ω : ℂ) (hω : ω ∈ L.lattice)
    (n : ℤ) (z : ℂ) (hz : z ∉ L.lattice) :
    weierstrassZeta L (z + n * ω) =
      weierstrassZeta L z + n * zetaQuasiPeriod L ω := by
  have hreg (k : ℤ) : z + k * ω ∉ L.lattice := by
    intro hm
    apply hz
    simpa [zsmul_eq_mul] using L.lattice.sub_mem hm (L.lattice.smul_mem k hω)
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have hs := weierstrassZeta_add_period L ω (z + n * ω) hω (hreg n)
    have heq : z + (((n : ℤ) + 1 : ℤ) : ℂ) * ω = z + n * ω + ω := by
      push_cast
      ring
    rw [heq, hs]
    push_cast at ih ⊢
    rw [ih]
    ring
  | pred n ih =>
    let k : ℤ := -(n : ℤ)
    have hs := weierstrassZeta_add_period L ω
      (z + ((k - 1 : ℤ) : ℂ) * ω) hω (hreg (k - 1))
    have heq : z + ((k - 1 : ℤ) : ℂ) * ω + ω = z + k * ω := by
      push_cast
      ring
    change weierstrassZeta L (z + k * ω) =
      weierstrassZeta L z + k * zetaQuasiPeriod L ω at ih
    rw [heq, ih] at hs
    change weierstrassZeta L (z + (k - 1 : ℤ) * ω) =
      weierstrassZeta L z + (k - 1 : ℤ) * zetaQuasiPeriod L ω
    push_cast
    push_cast at hs
    linear_combination -hs

private theorem regular_auxiliary_grid_data
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (hω : ω ∈ L.lattice)
    (h_independent : LinearIndependent ℚ ![u₁, u₂, ω])
    (h_intersection : Submodule.span ℤ {u₁, u₂} ⊓ L.lattice = ⊥) :
    RegularAuxiliaryGridData L ω u₁ u₂ := by
  classical
  obtain ⟨hinj, hlat, hreg, hcong⟩ :=
    TranscendenceTheory.integer_grid_geometry L.lattice ω u₁ u₂
      hω h_independent h_intersection
  have hfinite (A : Fin 3 → ℕ) : Function.Injective
      (fun m : (i : Fin 3) → Fin (A i) ↦
        integerGridPoint u₁ u₂ ω (fun i ↦ (m i : ℕ))) := by
    intro m n hmn
    have heq := hinj hmn
    funext i
    apply Fin.ext
    exact_mod_cast congrFun heq i
  have hcard (A : Fin 3 → ℕ) : (auxiliaryGrid u₁ u₂ ω A).card = ∏ i, A i := by
    rw [auxiliaryGrid, Finset.card_image_of_injective _ (hfinite A)]
    simp [Fintype.card_pi]
  refine ⟨hinj, hlat, hcong, hreg, hcard, ?_, ?_, ?_, ?_⟩
  · intro A
    rw [shiftedAuxiliaryGrid,
      Finset.card_image_of_injective _ (add_left_injective (u₁ / 2)), hcard]
  · intro A z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hw
    exact hreg _
  · intro A z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hw
    have hm (i : Fin 3) : ((m i : ℕ) : ℝ) ≤ A i := by
      exact_mod_cast (m i).isLt.le
    calc
      ‖integerGridPoint u₁ u₂ ω (fun i ↦ (m i : ℕ)) + u₁ / 2‖ ≤
          ‖integerGridPoint u₁ u₂ ω (fun i ↦ (m i : ℕ))‖ + ‖u₁ / 2‖ :=
        norm_add_le _ _
      _ ≤ (‖(((m 0 : ℕ) : ℂ) * u₁)‖ + ‖(((m 1 : ℕ) : ℂ) * u₂)‖ +
          ‖(((m 2 : ℕ) : ℂ) * ω)‖) + ‖u₁ / 2‖ := by
        dsimp [integerGridPoint]
        push_cast
        gcongr
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ((m 0 : ℕ) : ℝ) * ‖u₁‖ + ((m 1 : ℕ) : ℝ) * ‖u₂‖ +
          ((m 2 : ℕ) : ℝ) * ‖ω‖ + ‖u₁‖ / 2 := by
        simp
      _ ≤ _ := by gcongr <;> exact (m _).isLt.le
  · intro z n hz
    have hn : (n : ℂ) * ω ∈ L.lattice := by
      simpa [zsmul_eq_mul] using L.lattice.smul_mem n hω
    exact ⟨L.weierstrassP_add_coe z ⟨_, hn⟩,
      L.derivWeierstrassP_add_coe z ⟨_, hn⟩, integer_zeta_shift L ω hω n z hz⟩

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta
open scoped Polynomial

theorem solution
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (hω_ne : ω ≠ 0) (hω_period : ω ∈ L.lattice)
    (h_linearIndependent : LinearIndependent ℚ ![u₁, u₂, ω])
    (h_intersection : Submodule.span ℤ {u₁, u₂} ⊓ L.lattice = ⊥)
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
  have h_grid := regular_auxiliary_grid_data L ω u₁ u₂ hω_period
    h_linearIndependent h_intersection
  exact exists_complex_auxiliary_systems_on_regular_grids L ω u₁ u₂ h_grid
    h_zeta_deriv h_zeta_addition h_wp_addition θ hθ ν g hg_monic hg_degree
    hg_kernel d hd h_data
