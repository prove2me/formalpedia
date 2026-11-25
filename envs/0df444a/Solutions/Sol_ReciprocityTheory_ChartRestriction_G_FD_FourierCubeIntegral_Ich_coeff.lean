-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCubeIntegral.Ich_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:09:08.211496+00:00
-- url     : https://prove2.me/submissions/9c017526-5b8c-4b4a-83c3-cc8d8943fc6c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeVolume
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeVolume_pair_Bv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeVolume_ubox_ae
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_mF_tproj


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
theorem _root_.solution {χ : X.Ψ → Fin 2 → Fin 2 → ℂ} {m : Fin (4 * Fintype.card X.Ψ) → ℤ}
    (hm : ∀ j, 2 * X.pairR χ (ω j) = m j) {x : Frame X.Ψ r}
    (D : C(UnitAddTorus (Fin (4 * Fintype.card X.Ψ)), ℂ))
    (hD : ∀ t, D (I2.DimB.tproj t) = G (X.Zb u (Bv ω t) x)) :
    Ich X u ω G χ x = UnitAddTorus.mFourierCoeff D m := by
  have hp : ∀ j, pr χ (ω j) = (m j : ℝ) / 2 := fun j => by
    have := hm j
    change 2 * pr χ (ω j) = _ at this
    linarith
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ m 0]
  unfold Ich
  rw [← setIntegral_congr_set (ubox_ae _)]
  have e : ∀ t : Fin (4 * Fintype.card X.Ψ) → ℝ, G (X.Zb u (Bv ω t) x) * ech ω χ t =
      UnitAddTorus.mFourier (-m) (fun i => (t i : UnitAddCircle)) •
        D (fun i => (t i : UnitAddCircle)) := by
    intro t
    rw [show (fun i => (t i : UnitAddCircle)) = I2.DimB.tproj t from rfl, hD, I2.DimB.mF_tproj,
      smul_eq_mul, mul_comm]
    congr 1
    simp only [ech, pair_Bv, hp]
    congr 1
    push_cast
    simp only [Pi.neg_apply, Int.cast_neg]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [e]
  rfl
end ReciprocityTheory.ChartRestriction.G.FD.FourierCubeIntegral
