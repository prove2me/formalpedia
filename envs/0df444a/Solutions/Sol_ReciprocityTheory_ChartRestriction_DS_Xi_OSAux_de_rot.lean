-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.de_rot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:18:50.87114+00:00
-- url     : https://prove2.me/submissions/c040d047-16df-4c64-b24a-19197f5ac2c7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoMulStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux
private theorem norm_rho (t : ℝ) : ‖rho t‖ = 1 := by
  have h2 : ‖(1 + (t : ℂ) * Complex.I)‖ ^ 2 = 1 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    ring
  have hd : ‖((1 + t ^ 2 : ℝ) : ℂ)‖ = 1 + t ^ 2 := by
    exact Complex.norm_of_nonneg (by positivity)
  unfold rho
  rw [norm_div, norm_pow, h2, hd, div_self (by positivity)]
private theorem rho_mul_star (t : ℝ) : rho t * star (rho t) = 1 := by
  have h := norm_rho t
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
  simp
end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution {p m : ℕ} (t : ℝ) (x : Xp p m) (l : Fin (p + 1)) : de (rot t x) l = de x l := by
  have hn : ∀ z : ℂ, ‖rho t * z‖ = ‖z‖ := fun z => by rw [norm_mul, norm_rho, one_mul]
  have hc : ∀ a b : ℂ, rho t * a * star (rho t * b) = a * star b := by
    intro a b
    rw [star_mul']
    linear_combination (a * star b) * rho_mul_star t
  simp only [ReciprocityTheory.ChartRestriction.DS.Xi.de, ReciprocityTheory.ChartRestriction.DS.Xi.Lsq, ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq, ReciprocityTheory.ChartRestriction.DS.Xi.bco, rot, hn, hc]
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
