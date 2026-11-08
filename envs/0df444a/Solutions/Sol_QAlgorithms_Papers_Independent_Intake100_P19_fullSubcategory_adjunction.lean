-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P19.fullSubcategory_adjunction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:46:48.606742+00:00
-- url     : https://prove2.me/submissions/e01f2099-411a-4b58-92be-af99ee6d9b96

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P19

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uB vB uC vC

open QAlgorithms.Papers.Independent.Intake100.P19 in
theorem solution
    {B : Type uB} [Category.{vB} B] {C : Type uC} [Category.{vC} C]
    (F : B ⥤ C) (G : C ⥤ B) (adj : F ⊣ G)
    (P : ObjectProperty B) (Q : ObjectProperty C)
    (hF : ∀ b, P b → Q (F.obj b)) (hG : ∀ c, Q c → P (G.obj c)) :
    Nonempty (restrictedFunctor F P Q hF ⊣ restrictedFunctor G Q P hG) :=
  ⟨adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι (Iso.refl _) (Iso.refl _)⟩

end
