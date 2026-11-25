-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.aeval_eq_pow_mul_deh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:46:00.233544+00:00
-- url     : https://prove2.me/submissions/35420291-503e-4c42-a4f2-cad59f5ea94d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_aeval_smul_of_isHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution {ι S : Type*} [Fintype ι] [Field S] (v : ι → S) (i₀ : ι)
    (hv : v i₀ ≠ 0) {n : ℕ} {f : MvPolynomial ι ℤ} (hf : f.IsHomogeneous n) :
    aeval v f = v i₀ ^ n * deh v i₀ f := by
  have h : v = fun i => v i₀ * (v i / v i₀) := by
    funext i; rw [mul_div_cancel₀ _ hv]
  conv_lhs => rw [h]
  rw [aeval_smul_of_isHomogeneous hf]
  rfl
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
