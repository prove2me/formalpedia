-- Prove2me | solution 1 for P2M_GlobalTheory_AnVal_AnFr___add_7e58f427dd4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:12:22.830147+00:00
-- url     : https://prove2.me/submissions/89f95fa3-332d-4f43-8754-e8f833d11e35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AppellHumbertFrameSemicharacter
import Theorems.Thm_GlobalTheory_AnVal_semichar_herm_zero_left
import Theorems.Thm_GlobalTheory_AnVal_semichar_herm_add_left
import Theorems.Thm_GlobalTheory_AnVal_semichar_herm_add_right
import Theorems.Thm_GlobalTheory_AnVal_semichar_herm_swap
import Theorems.Thm_GlobalTheory_AnVal_AnFr_exists_chart_lat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
namespace GlobalTheory.AnVal
namespace AnFr
theorem _root_.solution {a b : Fin g → ℂ} (ha : a ∈ Φ.lat) (hb : b ∈ Φ.lat) :
    Φ.χ (a + b) = Φ.χ a * Φ.χ b * Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ)) := by
  obtain ⟨j, hj⟩ := Φ.exists_chart_lat
  have hab := Φ.lat.add_mem ha hb
  have h1 := Φ.fr_per a ha j 0 (hj 0 Φ.lat.zero_mem)
  have h2 := Φ.fr_per b hb j a (hj a ha)
  have h3 := Φ.fr_per (a + b) hab j 0 (hj 0 Φ.lat.zero_mem)
  have hne : Φ.fr j (a + b) ≠ 0 := Φ.fr_ne j _ (hj _ hab)
  rw [zero_add, h2] at h1
  rw [zero_add] at h3
  simp only [semichar_herm_zero_left, mul_zero, zero_add] at h1 h3
  have key : Φ.χ (a + b) * Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm (a + b) (a + b)) =
      Φ.χ a * Φ.χ b * (Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm a a) *
        Complex.exp (↑Real.pi * hermForm Φ.Hm a b + ↑Real.pi / 2 * hermForm Φ.Hm b b)) := by
    have := h3.symm.trans h1
    apply mul_right_cancel₀ hne
    linear_combination this
  have hexp : Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm a a) *
      Complex.exp (↑Real.pi * hermForm Φ.Hm a b + ↑Real.pi / 2 * hermForm Φ.Hm b b) =
      Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm (a + b) (a + b)) *
        Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [semichar_herm_add_left, semichar_herm_add_right, semichar_herm_add_right, semichar_herm_swap Φ.herm a b]
    have hsc : hermForm Φ.Hm a b - star (hermForm Φ.Hm a b) =
        2 * ((hermForm Φ.Hm a b).im : ℂ) * Complex.I := by
      rw [show star (hermForm Φ.Hm a b) = (starRingEnd ℂ) (hermForm Φ.Hm a b) from rfl, Complex.sub_conj]
      push_cast; ring
    linear_combination (↑Real.pi / 2 : ℂ) * hsc
  rw [hexp] at key
  have hE : Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm (a + b) (a + b)) ≠ 0 := Complex.exp_ne_zero _
  apply mul_right_cancel₀ hE
  linear_combination key
end AnFr
end GlobalTheory.AnVal
