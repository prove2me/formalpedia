-- Prove2me | solution 1 for PvsNP.coP_eq_P
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T06:24:07.300682+00:00
-- url     : https://prove2.me/submissions/25a6628f-9604-4343-8505-993a1d2812b3

import Definitions.Def_PvsNP_complexity_classes

open Computability Turing PvsNP

namespace PvsNPcoPaux

/-- Boolean negation, viewed as an equivalence `Bool ≃ Bool`. -/
def boolNotEquiv : Bool ≃ Bool where
  toFun := not
  invFun := not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

/-- If a decision problem is decidable in polynomial time, so is its pointwise negation:
the *same* machine decides it, after relabelling the output alphabet by Boolean negation. -/
theorem isPolyTime_not {L : DecisionProblem} (h : IsPolyTime L) :
    IsPolyTime (fun x => !(L x)) := by
  obtain ⟨h⟩ := h
  refine ⟨?_⟩
  refine { tm := h.tm, inputAlphabet := h.inputAlphabet,
           outputAlphabet := h.outputAlphabet.trans boolNotEquiv,
           time := h.time, outputsFun := ?_ }
  intro a
  have key : List.map (h.outputAlphabet.trans boolNotEquiv).invFun
        (BitstringEncoding.toEncoding.encode (!(L a)))
      = List.map h.outputAlphabet.invFun (BitstringEncoding.toEncoding.encode (L a)) := by
    show [(h.outputAlphabet.trans boolNotEquiv).symm (!(L a))] = [h.outputAlphabet.symm (L a)]
    simp [boolNotEquiv]
  rw [key]
  exact h.outputsFun a

/-- The pointwise complement of a decision problem is its pointwise Boolean negation. -/
theorem compl_eq (L : DecisionProblem) : Lᶜ = fun x => !(L x) := by
  funext x
  simp only [Pi.compl_apply, Bool.compl_eq_bnot]

end PvsNPcoPaux

open PvsNPcoPaux in
theorem solution : { L : DecisionProblem | Lᶜ ∈ P } = P := by
  ext L
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    have h' := isPolyTime_not (L := Lᶜ) h
    have : (fun x => !((Lᶜ) x)) = L := by
      funext x
      simp only [Pi.compl_apply, Bool.compl_eq_bnot, Bool.not_not]
    rwa [this] at h'
  · intro h
    have h' := isPolyTime_not h
    rwa [← compl_eq L] at h'
