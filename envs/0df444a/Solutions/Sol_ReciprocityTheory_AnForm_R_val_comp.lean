-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.val_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:57.498056+00:00
-- url     : https://prove2.me/submissions/949d376c-a736-4288-ac97-6fefd2be2695

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Theorems.Thm_ReciprocityTheory_AnForm_R_valHom_unique
import Theorems.Thm_ReciprocityTheory_AnForm_R_valHom_spec
import Theorems.Thm_ReciprocityTheory_AnForm_R_valHom_eq
import Theorems.Thm_ReciprocityTheory_AnForm_R_isClosed_image_of_closed
import Theorems.Thm_ReciprocityTheory_AnForm_R_residueFieldMap_constRes

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
theorem _root_.solution {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (g : S ⟶ T) (hg : g ≫ t = s)
    [LocallyOfFiniteType s] [LocallyOfFiniteType t] {U : T.Opens} {V : S.Opens} (hVU : V ≤ g ⁻¹ᵁ U)
    (f : Γ(T, U)) (x : S) (hx : x ∈ V) (hc : IsClosed ({x} : Set S)) :
    IsClosed ({g.base x} : Set T) ∧ val s (g.appLE U V hVU f) x hx = val t f (g.base x) (hVU hx) := by
  have hcl := isClosed_image_of_closed s t g hg x hc
  refine ⟨hcl, ?_⟩
  have hmor : g.appLE U V hVU ≫ S.evaluation V x hx =
      T.evaluation U (g.base x) (hVU hx) ≫ g.residueFieldMap x := by
    rw [Scheme.evaluation_naturality g x (V := U) (hVU hx :), Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp only [Scheme.evaluation, TopCat.Presheaf.germ_res_assoc]
  have hres : (residueFieldIsoBase s x hc).hom.hom.comp (g.residueFieldMap x).hom =
      (residueFieldIsoBase t (g.base x) hcl).hom.hom := by
    apply valHom_unique t (g.base x) hcl
    rw [RingHom.comp_assoc, residueFieldMap_constRes s t g hg x, valHom_spec s x hc]
  unfold val
  rw [valHom_eq s x hc, valHom_eq t (g.base x) hcl, ← hres]
  show _ = ((residueFieldIsoBase s x hc).hom.hom.comp (g.residueFieldMap x).hom)
    ((T.evaluation U (g.base x) (hVU hx)).hom f)
  rw [RingHom.comp_apply, ← RingHom.comp_apply (g.residueFieldMap x).hom, ← CommRingCat.hom_comp,
    ← hmor]
  rfl
end ReciprocityTheory.AnForm.R
