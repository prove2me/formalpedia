-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.qeRing_gammaChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:40:49.18546+00:00
-- url     : https://prove2.me/submissions/0a58d0ea-e606-4f89-be7c-18d40acf02fc

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LogResStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hQE : FinalTheorems.FinTypeQE) (p : (k : K) → ι k) : FinalTheorems.QERing Γ(projX P hP, (chartOpen hP p).1) := by
  letI : Algebra ℂ Γ(projX P hP, (chartOpen hP p).1) :=
    ((gammaChart hP p).symm.toRingHom.comp (algebraMap ℂ (chartRing P p))).toAlgebra
  let e : chartRing P p ≃ₐ[ℂ] Γ(projX P hP, (chartOpen hP p).1) :=
    { (gammaChart hP p).symm with commutes' := fun c => rfl }
  haveI : Algebra.FiniteType ℂ Γ(projX P hP, (chartOpen hP p).1) :=
    Algebra.FiniteType.equiv inferInstance e
  exact hQE Γ(projX P hP, (chartOpen hP p).1)
end ReciprocityTheory.AnForm.R
