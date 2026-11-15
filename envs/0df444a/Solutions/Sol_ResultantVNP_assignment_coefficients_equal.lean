-- Prove2me | solution 1 for ResultantVNP.assignment_coefficients_equal
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T13:12:06.517188+00:00
-- url     : https://prove2.me/submissions/e4a271ad-1a91-4f00-8bf9-2d6189a9e487

import Theorems.Thm_ResultantVNP_charCoeff_perm_invariant
import Definitions.Def_ResultantVNP_gridSum

namespace AssignmentCoefficients
open ResultantVNP

theorem choice_injective {m : ℕ} {ι : Type} (cls : ι → ZMod m × ZMod m)
    (ν : ∀ p,{a // cls a = p}) : Function.Injective (fun p => (ν p).val) := by
  intro p q h
  have hh := congrArg cls h
  simpa only [(ν p).property,(ν q).property] using hh

theorem monomial_transport {m n : ℕ} [NeZero m]
    (cls cls' : Fin n → ZMod m × ZMod m)
    (ν : ∀ p,{a // cls a = p}) (η : ∀ p,{a // cls' a = p})
    (π : Equiv.Perm (Fin n)) (hπ : ∀ p,π (ν p).val = (η p).val) :
    (assignMonomial cls ν).mapDomain (Sym.map π) = assignMonomial cls' η := by
  classical
  unfold assignMonomial
  rw [Finsupp.mapDomain_finset_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finsupp.mapDomain_single]
  congr 1
  simp only [assignTriple,Sym.map_cons,hπ,
    show Sym.map π (Sym.nil : Sym (Fin n) 0) = Sym.nil from Subsingleton.elim _ _]

theorem coefficient_eq (𝓡 : ResultantSystem) (m n : ℕ) [NeZero m]
    (cls cls' : Fin n → ZMod m × ZMod m)
    (ν : ∀ p,{a // cls a = p}) (η : ∀ p,{a // cls' a = p}) :
    (charCoeff 𝓡 n (m^2)).coeff (assignMonomial cls ν) =
      (charCoeff 𝓡 n (m^2)).coeff (assignMonomial cls' η) := by
  obtain ⟨π,hπ⟩ := Equiv.Perm.exists_extending_pair
    (fun p => (ν p).val) (fun p => (η p).val)
    (choice_injective cls ν) (choice_injective cls' η)
  have h := MvPolynomial.coeff_rename_mapDomain (Sym.map π)
    (Sym.map_injective π.injective 3) (charCoeff 𝓡 n (m^2)) (assignMonomial cls ν)
  rw [ResultantVNP.charCoeff_perm_invariant,monomial_transport cls cls' ν η π hπ] at h
  exact h.symm

theorem exists_common (𝓡 : ResultantSystem) (m n : ℕ) [NeZero m] :
    ∃ κ : ℤ, ∀ cls : Fin n → ZMod m × ZMod m,
      ∀ ν : (∀ p,{a // cls a = p}),
        (charCoeff 𝓡 n (m^2)).coeff (assignMonomial cls ν) = κ := by
  classical
  by_cases h : ∃ cls : Fin n → ZMod m × ZMod m, Nonempty (∀ p,{a // cls a = p})
  · obtain ⟨cls,⟨ν⟩⟩ := h
    refine ⟨(charCoeff 𝓡 n (m^2)).coeff (assignMonomial cls ν),?_⟩
    intro cls' η
    exact coefficient_eq 𝓡 m n cls' cls η ν
  · refine ⟨1,?_⟩
    intro cls ν
    exact (h ⟨cls,⟨ν⟩⟩).elim

end AssignmentCoefficients

theorem solution (𝓡 : ResultantVNP.ResultantSystem) (m n : ℕ) [NeZero m]
    (cls cls' : Fin n → ZMod m × ZMod m)
    (ν : ∀ p,{a // cls a = p}) (η : ∀ p,{a // cls' a = p}) :
    (ResultantVNP.charCoeff 𝓡 n (m^2)).coeff (ResultantVNP.assignMonomial cls ν) =
      (ResultantVNP.charCoeff 𝓡 n (m^2)).coeff (ResultantVNP.assignMonomial cls' η) :=
  AssignmentCoefficients.coefficient_eq 𝓡 m n cls cls' ν η

#print axioms solution
#print axioms AssignmentCoefficients.exists_common
