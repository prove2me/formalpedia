-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.rot_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:21:02.373612+00:00
-- url     : https://prove2.me/submissions/209c8102-46dd-4070-8bea-104c5e2d3291

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
private theorem rho_mp (t : ℝ) : MeasurePreserving (fun z : ℂ => rho t * z) volume volume := by
  have h1 := rho_mul_star t
  have h1' : star (rho t) * rho t = 1 := by rw [mul_comm]; exact h1
  have hn := norm_rho t
  let e : ℂ ≃ₗᵢ[ℝ] ℂ :=
    { toFun := fun z => rho t * z
      invFun := fun z => star (rho t) * z
      map_add' := fun x y => mul_add _ x y
      map_smul' := fun r x => by
        exact mul_smul_comm r (rho t) x
      left_inv := fun z => by
        show star (rho t) * (rho t * z) = z
        rw [← mul_assoc, h1', one_mul]
      right_inv := fun z => by
        show rho t * (star (rho t) * z) = z
        rw [← mul_assoc, h1, one_mul]
      norm_map' := fun z => by
        show ‖rho t * z‖ = ‖z‖
        rw [norm_mul, hn, one_mul] }
  exact e.measurePreserving
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
theorem _root_.solution {p m : ℕ} (t : ℝ) : MeasurePreserving (rot (p := p) (m := m) t) volume volume := by
  have h0 := rho_mp t
  have hp : ∀ n : ℕ, MeasurePreserving (fun (v : Fin n → ℂ) (j : Fin n) => rho t * v j) volume volume := by
    intro n
    exact measurePreserving_pi (fun _ => volume) (fun _ => volume) (fun _ => h0)
  have h := (hp p).prod ((hp p).prod ((hp m).prod (MeasurePreserving.id (volume : Measure ℝ))))
  exact h
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
