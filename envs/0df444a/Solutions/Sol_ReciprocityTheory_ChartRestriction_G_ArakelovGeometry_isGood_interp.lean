-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isGood_interp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:29.158048+00:00
-- url     : https://prove2.me/submissions/5e1c6284-d0ba-4d84-925b-7c4fb1bccee8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AInterpSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_interp_rho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_fderiv2_lin_comb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Topology
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {x : Ix κ → Ω} {m₀ m₁ : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg₀ : IsGood D x m₀ μ) (hg₁ : IsGood D x m₁ μ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsGood D x (interp m₀ m₁ t) μ := by
  obtain ⟨ht0, ht1⟩ := ht
  have hS : IsOpen {z : Ix κ → ℂ | z ≠ 0} := isOpen_ne
  have hsm0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₀.ρ {z | z ≠ 0} := hg₀.semipos.1
  have hsm1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁.ρ {z | z ≠ 0} := hg₁.semipos.1
  have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    first
      | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
      | exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
      | (norm_cast; exact le_top)
      | decide
  have hl0 : ContDiffOn ℝ 2 (fun z => Real.log (m₀.ρ z)) {z | z ≠ 0} :=
    (hsm0.of_le h2).log fun z hz => (m₀.pos z hz).ne'
  have hl1 : ContDiffOn ℝ 2 (fun z => Real.log (m₁.ρ z)) {z | z ≠ 0} :=
    (hsm1.of_le h2).log fun z hz => (m₁.pos z hz).ne'
  refine ⟨hg₀.arith, hg₀.indep, hg₀.smooth, ?_, ?_, hg₀.conjMu, hg₀.vol⟩
  · unfold IsSemipositiveOn
    refine ⟨?_, ?_⟩
    · show ContDiffOn ℝ _ (fun z => m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) _
      exact (hsm0.rpow_const_of_ne fun z hz => (m₀.pos z hz).ne').mul
        (hsm1.rpow_const_of_ne fun z hz => (m₁.pos z hz).ne')
    · intro z hz hz0 w hw
      have h0 := hg₀.semipos.2 z hz hz0 w hw
      have h1 := hg₁.semipos.2 z hz hz0 w hw
      unfold leviForm at h0 h1 ⊢
      rw [fderiv2_lin_comb (h := fun z => Real.log ((interp m₀ m₁ t).ρ z)) hS (1 - t) t hl0 hl1
        (fun y hy => by
          try dsimp only
          rw [interp_rho, Real.log_mul (Real.rpow_pos_of_pos (m₀.pos y hy) _).ne'
            (Real.rpow_pos_of_pos (m₁.pos y hy) _).ne', Real.log_rpow (m₀.pos y hy),
            Real.log_rpow (m₁.pos y hy)]) hz0]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) h0, mul_nonneg ht0 h1]
  · intro z
    rw [interp_rho, interp_rho, hg₀.conjM z, hg₁.conjM z]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
