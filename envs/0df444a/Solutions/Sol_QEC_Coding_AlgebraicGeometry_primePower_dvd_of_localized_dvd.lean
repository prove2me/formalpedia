-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primePower_dvd_of_localized_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:32:58.632105+00:00
-- url     : https://prove2.me/submissions/b6309b81-7ac5-457c-a836-80d4cd7d69b2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.Prime.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFiberDescent

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {R : Type*} [CommRing R] [IsDomain R]
    (P : Ideal R) [P.IsPrime] (a : R) (hP : P = Ideal.span {a}) (ha : Prime a)
    (n : ℕ) (r : R)
    (h : (algebraMap R (Localization.AtPrime P) a)^n ∣
      algebraMap R (Localization.AtPrime P) r) : a^n ∣ r := by
  let G := Localization.AtPrime P
  obtain ⟨b,hb⟩ := h
  obtain ⟨⟨x,s⟩,hs⟩ := IsLocalization.surj P.primeCompl b
  have hsr : (s : R)*r = a^n*x := by
    apply FaithfulSMul.algebraMap_injective R G
    calc
      algebraMap R G ((s : R)*r) =
          (algebraMap R G a)^n * (b * algebraMap R G s) := by
        rw [map_mul,hb]
        ac_rfl
      _ = algebraMap R G (a^n*x) := by rw [hs,map_mul,map_pow]
  have hsnot : ¬ a ∣ (s : R) := by
    intro hd
    apply s.property
    exact (le_of_eq hP.symm) (Ideal.mem_span_singleton.mpr hd)
  exact ha.pow_dvd_of_dvd_mul_left n hsnot ⟨x,hsr⟩
end QEC.Coding.AlgebraicGeometry
