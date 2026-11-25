-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_deh_eval__rename_376a9ee8007e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:57:47.861296+00:00
-- url     : https://prove2.me/submissions/2f796c60-8bdc-437c-a9fa-147566b0b31d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_deh_apply


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
variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution {S : Type*} [Field S] (v : ι → S) (e : Fin (D + 1) → ι)
    (Θ : MvPolynomial ι ℤ) (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)) :
    deh v (e 0) (H.eval₂ (rename e : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial ι ℤ).toRingHom Θ) =
      H.eval₂ (deh (v ∘ e) 0) (deh v (e 0) Θ) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [deh_apply]
  · intro i
    simp [deh_apply]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
