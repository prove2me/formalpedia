-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.constRes_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:17:40.28578+00:00
-- url     : https://prove2.me/submissions/0e87b44e-bbdc-4678-9179-47e0ae04fbf0

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Theorems.Thm_ReciprocityTheory_AnForm_R_fromSpecResidueField_appTop_iso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
variable {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of ℂ))
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (x : S) (hx : IsClosed ({x} : Set S)) [LocallyOfFiniteType s] :
    constRes s x = (residueFieldIsoBase s x hx).inv.hom := by
  have hφ := Scheme.ΓSpecIso_naturality (Spec.preimage (S.fromSpecResidueField x ≫ s))
  rw [Spec.map_preimage] at hφ
  have hpre : Spec.preimage (S.fromSpecResidueField x ≫ s) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (S.fromSpecResidueField x ≫ s).appTop ≫
        (Scheme.ΓSpecIso (S.residueField x)).hom := by
    rw [hφ, Iso.inv_hom_id_assoc]
  have hA : s.appLE ⊤ ⊤ le_top = s.appTop := (s.app_eq_appLE (U := ⊤)).symm
  have hc : constRes s x = ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ s.appLE ⊤ ⊤ le_top ≫
      S.evaluation ⊤ x trivial).hom := rfl
  rw [hc, hA, ← fromSpecResidueField_appTop_iso x]
  show _ = (Spec.preimage (S.fromSpecResidueField x ≫ s)).hom
  rw [hpre, Scheme.Hom.comp_appTop, Category.assoc]
end ReciprocityTheory.AnForm.R
