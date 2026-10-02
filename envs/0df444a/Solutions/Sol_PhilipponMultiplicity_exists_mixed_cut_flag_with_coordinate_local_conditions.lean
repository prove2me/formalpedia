-- Prove2me | solution 1 for PhilipponMultiplicity.exists_mixed_cut_flag_with_coordinate_local_conditions
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T20:07:06.639979+00:00
-- url     : https://prove2.me/submissions/6e15f90f-e37f-4425-b871-574b7c8c7287
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_mixed_cut_flag_with_point_local_conditions
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Localization.Ideal
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators Topology

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.ClosedPointSupport
variable {R : Type*} [CommRing R]

/-- Membership on a principal open implies membership at each prime on it. -/
theorem mem_atPrime_of_mem_away (I : Ideal R) (s x : R)
    (q : Ideal R) [q.IsPrime] (hs : s ∉ q)
    (hx : algebraMap R (Localization.Away s) x ∈
      I.map (algebraMap R (Localization.Away s))) :
    algebraMap R (Localization.AtPrime q) x ∈
      I.map (algebraMap R (Localization.AtPrime q)) := by
  obtain ⟨t,ht,htx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers s) (Localization.Away s) I x).mp hx
  obtain ⟨n,rfl⟩ := (Submonoid.mem_powers_iff t s).mp ht
  have hsn : s ^ n ∉ q := fun h => hs ((inferInstance : q.IsPrime).mem_of_pow_mem n h)
  have hu := IsLocalization.map_units (Localization.AtPrime q)
    (⟨s ^ n,hsn⟩ : q.primeCompl)
  have hm := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime q)) htx
  rw [map_mul] at hm
  exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hm

/-- Over a Jacobson ring, membership on a principal open is detected by
the maximal ideals of the original ring that lie on that open. -/
theorem mem_away_of_mem_at_maximal [IsJacobsonRing R]
    (I : Ideal R) (s x : R)
    (hx : ∀ (q : Ideal R) (_ : q.IsMaximal), s ∉ q →
      algebraMap R (Localization.AtPrime q) x ∈
        I.map (algebraMap R (Localization.AtPrime q))) :
    algebraMap R (Localization.Away s) x ∈
      I.map (algebraMap R (Localization.Away s)) := by
  classical
  let f := algebraMap R (Localization.Away s)
  let J := I.map f
  by_contra hn
  have hproper : J.colon {f x} ≠ ⊤ := by
    intro he
    have h1 : (1 : Localization.Away s) ∈ J.colon {f x} := by rw [he]; trivial
    rw [Submodule.mem_colon_singleton,one_smul] at h1
    exact hn h1
  obtain ⟨m,hm,hcolon⟩ := Ideal.exists_le_maximal (J.colon {f x}) hproper
  obtain ⟨hq,hs⟩ :=
    (IsLocalization.isMaximal_iff_isMaximal_disjoint (Localization.Away s) s m).mp hm
  have hlocal := hx (m.under R) hq hs
  obtain ⟨t,ht,htx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (m.under R).primeCompl (Localization.AtPrime (m.under R)) I x).mp hlocal
  apply ht
  apply hcolon
  rw [Submodule.mem_colon_singleton,smul_eq_mul,← map_mul]
  exact Ideal.mem_map_of_mem f htx

/-- Injectivity modulo an ideal can be checked at the closed points of a
principal open of a Jacobson spectrum. -/
theorem injective_away_of_injective_at_maximal [IsJacobsonRing R]
    (I : Ideal R) (s P : R)
    (hinj : ∀ (q : Ideal R) (_ : q.IsMaximal), s ∉ q →
      ∀ Q : Localization.AtPrime q,
        algebraMap R (Localization.AtPrime q) P * Q ∈
          I.map (algebraMap R (Localization.AtPrime q)) →
        Q ∈ I.map (algebraMap R (Localization.AtPrime q))) :
    ∀ Q : Localization.Away s,
      algebraMap R (Localization.Away s) P * Q ∈
        I.map (algebraMap R (Localization.Away s)) →
      Q ∈ I.map (algebraMap R (Localization.Away s)) := by
  intro Q hQ
  obtain ⟨⟨r,t⟩,hrt⟩ := IsLocalization.surj (Submonoid.powers s) Q
  have hPr : algebraMap R (Localization.Away s) (P*r) ∈
      I.map (algebraMap R (Localization.Away s)) := by
    rw [map_mul,← hrt]
    simpa only [mul_assoc] using
      (I.map (algebraMap R (Localization.Away s))).mul_mem_right
        (algebraMap R (Localization.Away s) t) hQ
  have hr := mem_away_of_mem_at_maximal I s r (fun q hq hs => by
    apply hinj q hq hs
    rw [← map_mul]
    exact mem_atPrime_of_mem_away I s (P*r) q hs hPr)
  rw [← hrt,mul_comm] at hr
  exact (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units (Localization.Away s) t)).mp hr

/-- Radicality on a principal open can be checked at its closed points. -/
theorem isRadical_away_of_isRadical_at_maximal [IsJacobsonRing R]
    (I : Ideal R) (s : R)
    (hred : ∀ (q : Ideal R) (_ : q.IsMaximal), s ∉ q →
      (I.map (algebraMap R (Localization.AtPrime q))).IsRadical) :
    (I.map (algebraMap R (Localization.Away s))).IsRadical := by
  apply Ideal.radical_eq_iff.mp
  apply le_antisymm ?_ Ideal.le_radical
  rw [← IsLocalization.map_radical (Submonoid.powers s) (Localization.Away s)]
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  apply mem_away_of_mem_at_maximal I s x
  intro q hq hs
  rw [← (hred q hq hs).radical]
  exact (I.map_radical_le _) (Ideal.mem_map_of_mem _ hx)

end PhilipponMultiplicity.ClosedPointSupport

end
end


section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] [IsAlgClosed K] (M : MultiProjectiveSpace K)

/-- A closed point on a coordinate open is a vector with every block nonzero. -/
theorem exists_vector_of_coordinate_maximal
    (j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (q : Ideal M.CoordinateRing) (hq : q.IsMaximal)
    (hs : (∏ i, (MvPolynomial.X (⟨i,j i⟩ : M.Variable) : M.CoordinateRing)) ∉ q) :
    ∃ v : M.Variable → K, q = MvPolynomial.vanishingIdeal K {v} ∧
      ∀ i : M.FactorIndex, (fun k : Fin (M.ambientDimension i + 1) => v ⟨i,k⟩) ≠ 0 := by
  classical
  obtain ⟨v,hv⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hq
  refine ⟨v,hv,?_⟩
  have hprod : (∏ i, v ⟨i,j i⟩) ≠ 0 := by
    simpa [hv,MvPolynomial.vanishingIdeal,map_prod] using hs
  intro i hz
  have hi := Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
  exact hi (congrFun hz (j i))

/-- Point-local injectivity at the geometric cut points gives injectivity
on every coordinate open of the multicone. -/
theorem coordinate_injective_of_point_local (I : Ideal M.CoordinateRing)
    (P : M.CoordinateRing)
    (hinj : ∀ v : M.Variable → K,
      (∀ i : M.FactorIndex, (fun k : Fin (M.ambientDimension i + 1) => v ⟨i,k⟩) ≠ 0) →
      (∀ Q ∈ I, MvPolynomial.eval v Q = 0) →
      let f := algebraMap M.CoordinateRing
        (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))
      ∀ Q, f P * Q ∈ I.map f → Q ∈ I.map f)
    (j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) :
    let f := algebraMap M.CoordinateRing
      (Localization.Away (∏ i, (MvPolynomial.X (⟨i,j i⟩ : M.Variable) : M.CoordinateRing)))
    ∀ Q, f P * Q ∈ I.map f → Q ∈ I.map f := by
  classical
  apply ClosedPointSupport.injective_away_of_injective_at_maximal
  intro q hq hs
  obtain ⟨v,rfl,hv⟩ := M.exists_vector_of_coordinate_maximal j q hq hs
  by_cases hI : I ≤ MvPolynomial.vanishingIdeal K {v}
  · apply hinj v hv
    intro Q hQ
    simpa [MvPolynomial.vanishingIdeal] using hI hQ
  · rw [IsLocalization.AtPrime.map_eq_top_of_not_le
      (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})) hI]
    exact fun _ _ => Submodule.mem_top

/-- Point-local reducedness at the geometric cut points gives reducedness
on every coordinate open, including opens with empty intersection. -/
theorem coordinate_isRadical_of_point_local (I : Ideal M.CoordinateRing)
    (hred : ∀ v : M.Variable → K,
      (∀ i : M.FactorIndex, (fun k : Fin (M.ambientDimension i + 1) => v ⟨i,k⟩) ≠ 0) →
      (∀ Q ∈ I, MvPolynomial.eval v Q = 0) →
      (I.map (algebraMap M.CoordinateRing
        (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})))).IsRadical)
    (j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) :
    (I.map (algebraMap M.CoordinateRing
      (Localization.Away (∏ i, (MvPolynomial.X (⟨i,j i⟩ : M.Variable) : M.CoordinateRing))))).IsRadical := by
  classical
  apply ClosedPointSupport.isRadical_away_of_isRadical_at_maximal
  intro q hq hs
  obtain ⟨v,rfl,hv⟩ := M.exists_vector_of_coordinate_maximal j q hq hs
  by_cases hI : I ≤ MvPolynomial.vanishingIdeal K {v}
  · apply hred v hv
    intro Q hQ
    simpa [MvPolynomial.vanishingIdeal] using hI hQ
  · rw [IsLocalization.AtPrime.map_eq_top_of_not_le
      (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})) hI]
    exact Ideal.radical_eq_iff.mp (by simp)

end PhilipponMultiplicity.MultiProjectiveSpace

end
end


section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem IsPhilipponBaseField.isAlgClosed {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : IsAlgClosed K := by
  have transfer (L : Type) [Field L] [IsAlgClosed L] (e : K ≃+* L) : IsAlgClosed K := by
    apply IsAlgClosed.of_exists_root K
    intro P _ hP
    obtain ⟨x,hx⟩ := IsAlgClosed.exists_eval₂_eq_zero e.toRingHom P
      (ne_of_gt (Polynomial.degree_pos_of_irreducible hP))
    refine ⟨e.symm x,?_⟩
    apply e.injective
    rw [map_zero]
    change e.toRingHom (P.eval (e.symm x)) = 0
    rw [← Polynomial.eval₂_at_apply]
    change P.eval₂ e.toRingHom (e (e.symm x)) = 0
    simpa only [RingEquiv.apply_symm_apply] using hx
  rcases hK with ⟨e,_⟩ | ⟨p,hp,h⟩
  · exact transfer ℂ e
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e,_⟩ := h
    exact transfer (PadicComplex p) e


end PhilipponMultiplicity
end
end


section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

/-- Closed-point conditions imply the coordinate-open conditions, with
the section, actual cut ideals, and cutting forms all unchanged. -/
theorem coordinate_cut_flag_of_point_local_conditions
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hchoice : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
        ∃ (l : List M.FactorIndex) (P : ℕ → M.CoordinateRing)
          (J : ℕ → Ideal M.CoordinateRing),
          (∀ i, l.count i = α i) ∧ J 0 = M.vanishingIdeal W ∧
          (∀ k (hk : k < l.length),
            M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧
            J (k+1) = J k ⊔ Ideal.span {P k} ∧
            ∀ v : M.Variable → K,
              (∀ i : M.FactorIndex,
                (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
              (∀ Q ∈ J k, MvPolynomial.eval v Q = 0) →
              let f := algebraMap M.CoordinateRing
                (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))
              ∀ Q, f (P k) * Q ∈ (J k).map f → Q ∈ (J k).map f) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ v : M.Variable → K,
            (∀ i : M.FactorIndex,
              (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
            (∀ Q ∈ J l.length, MvPolynomial.eval v Q = 0) →
            ((J l.length).map (algebraMap M.CoordinateRing
              (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})))).IsRadical)) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
        ∃ (l : List M.FactorIndex) (P : ℕ → M.CoordinateRing)
          (J : ℕ → Ideal M.CoordinateRing),
          (∀ i, l.count i = α i) ∧ J 0 = M.vanishingIdeal W ∧
          (∀ k (hk : k < l.length),
            M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧
            J (k+1) = J k ⊔ Ideal.span {P k} ∧
            ∀ j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
              let f := algebraMap M.CoordinateRing
                (Localization.Away (∏ i,
                  (MvPolynomial.X (⟨i,j i⟩ : M.Variable) : M.CoordinateRing)))
              ∀ Q, f (P k) * Q ∈ (J k).map f → Q ∈ (J k).map f) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
            ((J l.length).map (algebraMap M.CoordinateRing
              (Localization.Away (∏ i,
                (MvPolynomial.X (⟨i,j i⟩ : M.Variable) : M.CoordinateRing))))).IsRadical) := by
  let := hK.isAlgClosed
  intro M W hW hirr α hα hdim B hB hBW hnonempty
  obtain ⟨L,hL,hfinite,hdisjoint,l,P,J,hcount,hfirst,hstep,hgeometry,hreduced⟩ :=
    hchoice M W hW hirr α hα hdim B hB hBW hnonempty
  refine ⟨L,hL,hfinite,hdisjoint,l,P,J,hcount,hfirst,?_,hgeometry,?_⟩
  · intro k hk
    refine ⟨(hstep k hk).1,(hstep k hk).2.1,?_⟩
    exact M.coordinate_injective_of_point_local (J k) (P k) (hstep k hk).2.2
  · exact M.coordinate_isRadical_of_point_local (J l.length) hreduced

end PhilipponMultiplicity
end
end

open PhilipponMultiplicity PhilipponMultiplicity.SectionThree PhilipponMultiplicity.SectionThreeSupport

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
        ∃ (l : List M.FactorIndex) (P : ℕ → M.CoordinateRing)
          (J : ℕ → Ideal M.CoordinateRing),
          (∀ i, l.count i = α i) ∧ J 0 = M.vanishingIdeal W ∧
          (∀ k (hk : k < l.length),
            M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧
            J (k+1) = J k ⊔ Ideal.span {P k} ∧
            ∀ j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
              let f := algebraMap M.CoordinateRing
                (Localization.Away (∏ i,
                  (MvPolynomial.X (⟨i,j i⟩ : M.Variable) : M.CoordinateRing)))
              ∀ Q, f (P k) * Q ∈ (J k).map f → Q ∈ (J k).map f) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
            ((J l.length).map (algebraMap M.CoordinateRing
              (Localization.Away (∏ i,
                (MvPolynomial.X (⟨i,j i⟩ : M.Variable) : M.CoordinateRing))))).IsRadical) := by
  exact coordinate_cut_flag_of_point_local_conditions K hK
    (exists_mixed_cut_flag_with_point_local_conditions K hK)
