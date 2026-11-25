-- Prove2me | solution 1 for PretorsionImageClosed.Statement.traceRejectCondition_of_quotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:57:10.757806+00:00
-- url     : https://prove2.me/submissions/a8f4c963-1a00-4b8f-bbc2-9fb785b26890

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Theorems.Thm_P2M_PretorsionImageClosed___comp_cokernelKernelSubobjectArrowIso_inv_7623172b6aa2
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_trace_iso
public import Theorems.Thm_PretorsionImageClosed_imageSubobject_comp_iso_hom


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C] {T F : Subcategory C} {X : C}
namespace PretorsionImageClosed.Statement
theorem _root_.solution (hT : T.IsQuotientClosed) {Q : C} (π : X ⟶ Q) [Epi π]
    (hker : kernelSubobject π = F.reject X) (h1 : F.reject X ≤ T.trace X)
    (h2 : F.reject (T.trace X : C) = Subobject.mk (Subobject.ofLE _ _ h1))
    (h3 : T.trace Q = imageSubobject ((T.trace X).arrow ≫ π)) : TraceRejectCondition T F X := by
  refine ⟨h1, h2, ?_⟩
  have key : ∀ r : Subobject X, kernelSubobject π = r →
      T.trace (cokernel r.arrow) = imageSubobject ((T.trace X).arrow ≫ cokernel.π r.arrow) := by
    rintro _ rfl
    rw [trace_iso hT (cokernelKernelSubobjectArrowIso π).symm, h3,
      ← imageSubobject_comp_iso_hom _ (cokernelKernelSubobjectArrowIso π).symm]
    congr 1
    rw [Category.assoc, Iso.symm_hom, π_comp_cokernelKernelSubobjectArrowIso_inv]
  exact key _ hker
end PretorsionImageClosed.Statement
