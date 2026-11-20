-- Prove2me | solution 1 for QEC.Coding.BDL26BaseGeometricDomain.z_in_closed_Xstar_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:05:50.515207+00:00
-- url     : https://prove2.me/submissions/f5e6106c-bb16-4192-9636-ef179e39f1bc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare

set_option autoImplicit false
open QEC.Coding.BDL26FiniteTannerSquare

namespace QEC.Coding.BDL26BaseGeometricDomain
theorem _root_.solution (P : TannerSquarePresentation) (x : P.X) (z : P.Z) :
    xStarVertexMember P x (.z z)=true ↔
      ∃ q : P.Q, P.xq x q=true ∧ P.qz q z=true := by
  constructor
  · intro h
    obtain ⟨f,hf,hz⟩ := of_decide_eq_true h
    have hx : P.faceX f=x := of_decide_eq_true hf
    subst z
    refine ⟨P.faceQ f 0,?_,P.data.faceQ_qz f 0⟩
    exact (congrArg (fun a => P.xq a (P.faceQ f 0)) hx).symm.trans
      (P.data.faceQ_xq f 0)
  · rintro ⟨q,hx,hz⟩
    let shared : SharedQ P.data x z := ⟨q,by simpa using And.intro hx hz⟩
    let fc := (P.faceCornerEquiv x z).symm shared
    change decide (∃ f : P.Face, xStarFaceMember P x f=true ∧ z=P.faceZ f)=true
    apply decide_eq_true
    exact ⟨fc.1.val,decide_eq_true fc.1.property.1,fc.1.property.2.symm⟩
end QEC.Coding.BDL26BaseGeometricDomain
