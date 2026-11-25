-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.fFinRes_projX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:50:47.954348+00:00
-- url     : https://prove2.me/submissions/6b14321d-8fba-4c74-aa90-c499f520e289

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LogResStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypStalk
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Theorems.Thm_ReciprocityTheory_AnForm_R_chartOpen_cover


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
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    FinalTheorems.FFinRes (projX P hP) := by
  intro x p _ hchar
  obtain ⟨q, hq⟩ := chartOpen_cover hP x
  let f : ℂ →+* (projX P hP).residueField x :=
    ((projX P hP).residue x).hom.comp (((projX P hP).presheaf.germ (chartOpen hP q).1 x hq).hom.comp
      ((gammaChart hP q).symm.toRingHom.comp (algebraMap ℂ (chartRing P q))))
  exfalso
  have h1 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have h2 : f (p : ℂ) = 0 := by
    rw [map_natCast]
    exact CharP.cast_eq_zero _ p
  exact h1 (f.injective (by rw [h2, map_zero]))
end ReciprocityTheory.AnForm.R
