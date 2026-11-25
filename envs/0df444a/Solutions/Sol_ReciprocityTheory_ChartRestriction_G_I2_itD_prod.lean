-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.itD_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:23:56.177177+00:00
-- url     : https://prove2.me/submissions/1d3ce43a-70bc-4242-bf03-c2fcb719aec3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_itD_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_itD_differentiable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_itD_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_fderiv_prod_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_colL_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {n : ℕ} {g : Fin n → W → ℂ} (hg : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (g k))
    (L : List (Fin n × W)) (x : Fin n → W) :
    itD (fun v : Fin n → W => ∏ k, g k (v k)) (L.map fun p => Pi.single p.1 p.2) x =
      ∏ k, itD (g k) (colL L k) (x k) := by
  have hP : ContDiff ℂ (⊤ : ℕ∞) (fun v : Fin n → W => ∏ k, g k (v k)) := by
    first
      | exact contDiff_prod fun k _ => (hg k).comp (contDiff_apply ℂ W k)
      | fun_prop
  induction L generalizing x with
  | nil => simp [itD_nil, colL]
  | cons a L ih =>
    simp only [List.map_cons]
    rw [itD_cons hP]
    have hfun : (fun y => itD (fun v : Fin n → W => ∏ k, g k (v k))
        (L.map fun p => Pi.single p.1 p.2) y) = fun y => ∏ k, itD (g k) (colL L k) (y k) :=
      funext fun y => ih y
    rw [hfun, fderiv_prod_single (h := fun k y => itD (g k) (colL L k) y)
      (fun k => itD_differentiable (hg k) _)]
    rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ a.1)]
    congr 1
    · refine Finset.prod_congr rfl fun k hk => ?_
      rw [colL_cons, if_neg (Ne.symm (Finset.ne_of_mem_erase hk))]
    · rw [colL_cons, if_pos rfl, itD_cons (hg _)]
end ReciprocityTheory.ChartRestriction.G.I2
