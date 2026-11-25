-- Prove2me | solution 1 for PretorsionImageClosed.Statement.TraceRejectCondition.of_reject_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:54:18.745033+00:00
-- url     : https://prove2.me/submissions/4dcd4928-c72e-4eaa-8d22-976f644c5da8

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
namespace PretorsionImageClosed.Statement
namespace TraceRejectCondition
theorem _root_.solution {T F G : Subcategory C} {X : C}
    (h : TraceRejectCondition T F X) (h1 : G.reject X = F.reject X)
    (h2 : G.reject (T.trace X : C) = F.reject (T.trace X : C)) : TraceRejectCondition T G X := by
  obtain ⟨a, b, c⟩ := h
  have a' : G.reject X ≤ T.trace X := h1 ▸ a
  refine ⟨a', ?_, ?_⟩
  · have key : ∀ (r : Subobject X) (_ : r = F.reject X) (hle : r ≤ T.trace X),
        Subobject.mk (Subobject.ofLE r _ hle) = Subobject.mk (Subobject.ofLE (F.reject X) _ a) := by
      rintro _ rfl _
      rfl
    rw [h2, b, key _ h1 a']
  · have key : ∀ (r : Subobject X), r = F.reject X →
        T.trace (cokernel r.arrow) = imageSubobject ((T.trace X).arrow ≫ cokernel.π r.arrow) := by
      rintro _ rfl
      exact c
    exact key _ h1
end TraceRejectCondition
end PretorsionImageClosed.Statement
