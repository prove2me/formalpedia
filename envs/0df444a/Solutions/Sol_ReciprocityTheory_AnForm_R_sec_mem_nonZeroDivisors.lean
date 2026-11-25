-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.sec_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:05:54.520989+00:00
-- url     : https://prove2.me/submissions/33839e09-ac83-40f4-8183-13f510aa6822

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjBCompl
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Theorems.Thm_ReciprocityTheory_AnForm_R_mem_nonZeroDivisors_of_bijective

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
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {W : Scheme.{0}} (V : W.Opens) {A : CommRingCat.{0}}
    (e : V.toScheme ≅ Spec A) {a : A} (ha : a ∈ nonZeroDivisors A) :
    V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso A).inv a)) ∈ nonZeroDivisors Γ(W, V) := by
  have : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
  have hb : Function.Bijective ((V.topIso.hom.hom).comp ((e.hom.appTop).hom.comp
      (Scheme.ΓSpecIso A).inv.hom)) :=
    (ConcreteCategory.bijective_of_isIso V.topIso.hom).comp
      ((ConcreteCategory.bijective_of_isIso e.hom.appTop).comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv))
  exact mem_nonZeroDivisors_of_bijective _ hb ha
end ReciprocityTheory.AnForm.R
