-- Prove2me | solution 1 for QEC.Coding.BDL26BaseGeometricDomain.closed_Xstar_vertex_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:09:18.324602+00:00
-- url     : https://prove2.me/submissions/1b645c1d-6369-450d-9b35-b148c1ae4d1c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint
import Theorems.Thm_QEC_Coding_BDL26BaseGeometricDomain_q_in_closed_Xstar_iff
import Theorems.Thm_QEC_Coding_BDL26BaseGeometricDomain_z_in_closed_Xstar_iff

set_option autoImplicit false
noncomputable section
noncomputable section
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BaseGeometricDomain
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open scoped Classical
namespace QEC.Coding.BDL26BaseGeometricDomain
theorem _root_.solution (P : TannerSquarePresentation) (x : P.X)
    (v : Vertex P) (hv : xStarVertexMember P x v=true) :
    v=.x x ∨ (tannerSkeleton P).adjacent (.x x) v ∨
      ∃ w : Vertex P, (tannerSkeleton P).adjacent (.x x) w ∧
        (tannerSkeleton P).adjacent w v := by
  cases v with
  | x y =>
    have hy : y=x := of_decide_eq_true hv
    subst y
    exact Or.inl rfl
  | q q =>
    obtain ⟨z,hx,_hz⟩ := (q_in_closed_Xstar_iff P x q).mp hv
    exact Or.inr (Or.inl hx)
  | z z =>
    obtain ⟨q,hx,hz⟩ := (z_in_closed_Xstar_iff P x z).mp hv
    exact Or.inr (Or.inr ⟨.q q,hx,hz⟩)
end QEC.Coding.BDL26BaseGeometricDomain
