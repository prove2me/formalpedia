-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.multiplicity_map_eq_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:32:12.194603+00:00
-- url     : https://prove2.me/submissions/1785eb73-d494-4c95-89c8-7dac8034018f

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Localization.NormTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Localization

set_option autoImplicit false
open Module
open scoped nonZeroDivisors
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (S Sm : Type*) [CommRing S] [CommRing Sm]
    [IsDomain S] [IsDomain Sm]
    [Algebra S Sm] [IsDedekindDomain S] [IsDedekindDomain Sm]
    (M : Submonoid S) [IsLocalization M Sm]
    (Q I : Ideal S) [Q.IsMaximal]
    (hQ : Disjoint (M : Set S) (Q : Set S)) :
    multiplicity (Ideal.map (algebraMap S Sm) Q)
        (Ideal.map (algebraMap S Sm) I) =
      multiplicity Q I := by
  apply multiplicity_eq_of_emultiplicity_eq
  rw [emultiplicity_eq_emultiplicity_iff]
  intro n
  cases n with
  | zero => simp
  | succ n =>
      have hQprimary : (Q ^ (n + 1)).IsPrimary := by
        apply Ideal.isPrimary_of_isMaximal_radical
        rw [Ideal.radical_pow Q (Nat.succ_ne_zero n),
          (inferInstance : Q.IsPrime).radical]
        exact inferInstance
      have hQdisjoint :
          Disjoint (M : Set S) ((Q ^ (n + 1) : Ideal S) : Set S) :=
        hQ.mono_right (Ideal.pow_le_self (I := Q) (Nat.succ_ne_zero n))
      rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, ← Ideal.map_pow]
      constructor
      · intro h
        calc
          I ≤ (Ideal.map (algebraMap S Sm) I).under S := Ideal.le_comap_map
          _ ≤ (Ideal.map (algebraMap S Sm) (Q ^ (n + 1))).under S :=
            Ideal.comap_mono h
          _ = Q ^ (n + 1) :=
            IsLocalization.under_map_of_isPrimary_disjoint M Sm hQprimary hQdisjoint
      · exact Ideal.map_mono
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
