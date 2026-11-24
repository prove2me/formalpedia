-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inh_finrank_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:45.318686+00:00
-- url     : https://prove2.me/submissions/fc5e65f2-f278-4eab-a591-fb6f0dd1326e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {σ : Type*} {F : Type*} [Field F]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution (I : Ideal (MvPolynomial σ F)) (c : σ → F)
    (hI : I ≤ RingHom.ker (eval c)) (hX : ∀ s, X s - C (c s) ∈ I) :
    Module.finrank F (MvPolynomial σ F ⧸ I) = 1 := by
  have hne : I ≠ ⊤ := by
    intro h
    have := hI (h ▸ Submodule.mem_top : (1 : MvPolynomial σ F) ∈ I)
    simp at this
  have := Ideal.Quotient.nontrivial_iff.mpr hne
  have hmk : (Ideal.Quotient.mk I) = (algebraMap F (MvPolynomial σ F ⧸ I)).comp (eval c) := by
    apply MvPolynomial.ringHom_ext
    · intro r; rw [RingHom.comp_apply, eval_C]; rfl
    · intro s
      rw [RingHom.comp_apply, eval_X,
        show algebraMap F _ (c s) = Ideal.Quotient.mk I (C (c s)) from rfl]
      exact Ideal.Quotient.eq.mpr (hX s)
  rw [finrank_eq_one_iff_of_nonzero' (1 : MvPolynomial σ F ⧸ I) one_ne_zero]
  intro w
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine ⟨eval c f, ?_⟩
  rw [Algebra.smul_def, mul_one, hmk, RingHom.comp_apply]
end ReciprocityTheory.ChartRestriction.G.AI.I1
