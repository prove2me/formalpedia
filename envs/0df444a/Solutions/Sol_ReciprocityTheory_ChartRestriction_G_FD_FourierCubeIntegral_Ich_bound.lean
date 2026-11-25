-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCubeIntegral.Ich_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:53:56.181462+00:00
-- url     : https://prove2.me/submissions/6582123b-a7c1-4fab-958c-966a398a86e4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeVolume
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCubeIntegral
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
  MeasureTheory Set Filter
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {u : Fin 2 → Fin r → E} {g : ℕ} {ω : Fin (4 * Fintype.card X.Ψ) → X.Ψ → Fin 2 → Fin 2 → ℂ}
  {G : Frame X.Ψ r → ℂ}
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCubeIntegral
theorem _root_.solution (hω : X.IsLZBasis g ω)
    (hunit : ∀ b, IsHermFam b → X.IsUnitaryC (X.zmat u b)) (la : Wt X.Ψ r)
    (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) {M : ℝ}
    (hM : ∀ b, IsHermFam b → X.pnorm la G (X.Zb u b x) ≤ M) :
    ‖Ich X u ω G χ x‖ * fac X la x ≤ M := by
  have hωh : ∀ j, IsHermFam (ω j) := by
    intro j τ i k
    obtain ⟨β, hβ, -, hb⟩ := hω.1 j
    rw [hb]
    simp only [Data.embH]
    rw [← hβ i k, cc, NumberField.IsCMField.complexEmbedding_complexConj]
  have hBv : ∀ t : Fin (4 * Fintype.card X.Ψ) → ℝ, IsHermFam (Bv ω t) := by
    intro t τ i k
    simp only [Bv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal]
    exact Finset.sum_congr rfl fun j _ => by rw [hωh j τ i k]
  have hfac : ∀ b, IsHermFam b → fac X la (X.Zb u b x) = fac X la x := by
    intro b hb
    have hd : ∀ τ i, dmin X.Gm (X.Zb u b x) τ i = dmin X.Gm x τ i := by
      intro τ i
      unfold dmin
      congr 1
      ext a c
      have hcol : ∀ a, col (mat (X.Zb u b x) τ) a =
          Matrix.mulVec (X.zmat u b τ) (col (mat x τ) a) := by
        intro a
        ext k
        show (X.zmat u b τ * mat x τ) k a = ∑ j, X.zmat u b τ k j * col (mat x τ) a j
        rw [Matrix.mul_apply]
        rfl
      simp only [gram, Matrix.of_apply]
      rw [hcol, hcol, hunit b hb τ]
    simp only [fac, hd]
  have hnn : ∀ y, 0 ≤ fac X la y := fun y =>
    Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hpn : ∀ y, X.pnorm la G y = ‖G y‖ * fac X la y := fun y => rfl
  have hech : ∀ t, ‖ech ω χ t‖ = 1 := fun t => by
    unfold ech
    rw [Complex.norm_exp]
    simp
  have hcube1 : ∀ n, volume (cube n) = 1 := fun n => by
    rw [show cube n = Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) 1) from rfl, volume_pi,
      Measure.pi_pi]
    simp
  rcases (hnn x).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    have h1 := hM _ (hBv 0)
    rw [hpn] at h1
    exact le_trans (mul_nonneg (norm_nonneg _) (hnn _)) h1
  · have hb : ∀ t ∈ cube (4 * Fintype.card X.Ψ),
        ‖G (X.Zb u (Bv ω t) x) * ech ω χ t‖ ≤ M / fac X la x := by
      intro t _
      rw [norm_mul, hech, mul_one, le_div_iff₀ hpos, ← hfac _ (hBv t), ← hpn]
      exact hM _ (hBv t)
    have hI : ‖Ich X u ω G χ x‖ ≤ M / fac X la x * (volume (cube (4 * Fintype.card X.Ψ))).toReal :=
      norm_setIntegral_le_of_norm_le_const (by rw [hcube1]; simp) hb
    rw [hcube1, ENNReal.toReal_one, mul_one] at hI
    calc _ ≤ M / fac X la x * fac X la x := mul_le_mul_of_nonneg_right hI (hnn x)
      _ = M := div_mul_cancel₀ M hpos.ne'
end ReciprocityTheory.ChartRestriction.G.FD.FourierCubeIntegral
