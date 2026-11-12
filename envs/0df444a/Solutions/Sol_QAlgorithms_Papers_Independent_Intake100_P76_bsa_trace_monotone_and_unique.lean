-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P76.bsa_trace_monotone_and_unique
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T18:45:21.082594+00:00
-- url     : https://prove2.me/submissions/dc65a626-1d3b-48cb-be84-b64e4b3ae682

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P76

open scoped Matrix ComplexOrder ComplexConjugate

open QAlgorithms QAlgorithms.Entanglement

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

open QAlgorithms.Papers.Independent.Intake100.P76 in
theorem solution [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (V W : Set (EuclideanSpace ℂ (A × B)))
    (hV : ∀ v ∈ V, IsUnitProduct v ∧ v ∈ LinearMap.range (Matrix.toEuclideanLin rho))
    (hW : ∀ v ∈ W, IsUnitProduct v ∧ v ∈ LinearMap.range (Matrix.toEuclideanLin rho)) :
    (∀ S T, V ⊆ W → IsBSAOver rho V S → IsBSAOver rho W T →
      S.trace.re ≤ T.trace.re) ∧
    (∀ S T, IsBSAOver rho V S → IsBSAOver rho V T → S.trace.re = T.trace.re) := by
  refine ⟨fun S T hVW hS hT => ?_, fun S T hS hT => ?_⟩
  · obtain ⟨⟨m, w, v, hw, hv, hSeq⟩, hpsd, _⟩ := hS
    exact hT.2.2 S ⟨m, w, v, hw, fun k => hVW (hv k), hSeq⟩ hpsd
  · exact le_antisymm (hT.2.2 S hS.1 hS.2.1) (hS.2.2 T hT.1 hT.2.1)
