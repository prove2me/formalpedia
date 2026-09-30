-- Prove2me | solution 1 for PhilipponMultiplicity.Hilbert.cohenMacaulayAt_sup_span_of_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-26T07:07:19.768591+00:00
-- url     : https://prove2.me/submissions/1a9680cc-34fa-4cc9-8ce8-c2846bb5f0e1

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Theorems.Thm_Module_depth_quotSMulTop_succ_eq
import Theorems.Thm_Module_depth_quotient_eq_depth
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Pointwise
noncomputable section

namespace PhilipponMultiplicity.RegularCutSupport
open IsLocalRing RingTheory

variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem depth_eq_of_linearEquiv {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    Module.depth R M = Module.depth R N := by
  rw [Module.depth, Module.depth]
  congr 1
  ext k
  constructor
  · rintro ⟨s, hs, hs', rfl⟩
    exact ⟨s, (e.isWeaklyRegular_congr s).mp hs, hs', rfl⟩
  · rintro ⟨s, hs, hs', rfl⟩
    exact ⟨s, (e.isWeaklyRegular_congr s).mpr hs, hs', rfl⟩

/-- Finite lower bounds on depth are attained by actual regular sequences. -/
theorem exists_weaklyRegular_of_le_depth (n : ℕ) (hn : (n : ℕ∞) ≤ Module.depth R R) :
    ∃ s : List R, Sequence.IsWeaklyRegular R s ∧
      (∀ r ∈ s, r ∈ maximalIdeal R) ∧ s.length = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact ⟨[], Sequence.IsWeaklyRegular.nil R R, by simp, rfl⟩
  have hlt : ((n - 1 : ℕ) : ℕ∞) < Module.depth R R :=
    lt_of_lt_of_le (Nat.cast_lt.mpr (by omega)) hn
  rw [Module.depth, lt_sSup_iff] at hlt
  obtain ⟨b, ⟨s, hs, hs', rfl⟩, hb⟩ := hlt
  have hlen : n ≤ s.length := by
    have := Nat.cast_lt.mp hb
    omega
  refine ⟨s.take n, ?_, ?_, ?_⟩
  · exact ((Sequence.isWeaklyRegular_append_iff R (s.take n) (s.drop n)).mp
      (by rwa [List.take_append_drop])).1
  · exact fun r hr => hs' r (List.take_subset n s hr)
  · rw [List.length_take]; omega

/-- The depth and dimension drops give a full regular sequence in a regular
hypersurface section of a Cohen--Macaulay local ring. -/
theorem fullRegularSequence_quotient [IsNoetherianRing R]
    (rs : List R) (hrs : ∀ r ∈ rs, ¬ IsUnit r)
    (hreg : Sequence.IsRegular R rs)
    (hdim : (rs.length : WithBot ℕ∞) = ringKrullDim R)
    (x : R) (hx : ¬ IsUnit x) (hxreg : IsSMulRegular R x) :
    ∃ s : List (R ⧸ Ideal.span {x}),
      (∀ r ∈ s, ¬ IsUnit r) ∧ Sequence.IsRegular (R ⧸ Ideal.span {x}) s ∧
      (s.length : WithBot ℕ∞) = ringKrullDim (R ⧸ Ideal.span {x}) := by
  let C := R ⧸ Ideal.span {x}
  have : Nontrivial C := Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top hx)
  letI : IsLocalRing C := IsLocalRing.of_surjective' (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective
  have hxm : x ∈ maximalIdeal R := (mem_maximalIdeal x).mpr hx
  have hdR : (rs.length : ℕ∞) ≤ Module.depth R R :=
    le_sSup ⟨rs, hreg.1, fun r hr => (mem_maximalIdeal r).mpr (hrs r hr), rfl⟩
  have hspan : x • (⊤ : Ideal R) = Ideal.span {x} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  have hdepth : Module.depth C C + 1 = Module.depth R R := by
    rw [Module.depth_quotient_eq_depth (Ideal.span {x}) C]
    rw [← depth_eq_of_linearEquiv (Submodule.quotEquivOfEq _ _ hspan)]
    exact Module.depth_quotSMulTop_succ_eq R hxm hxreg
  have hdimdrop := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hxreg hxm
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim C = (n : WithBot ℕ∞) := by
    cases h : ringKrullDim C with
    | bot => exact (ringKrullDim_ne_bot h).elim
    | coe d =>
      cases d with
      | top => exact (ringKrullDim_ne_top h).elim
      | coe n => exact ⟨n, by norm_cast⟩
  have hlen : n + 1 = rs.length := by
    change ringKrullDim C + 1 = ringKrullDim R at hdimdrop
    rw [hn, ← hdim, ← Nat.cast_add_one] at hdimdrop
    exact_mod_cast hdimdrop
  have hdC : (n : ℕ∞) ≤ Module.depth C C := by
    apply (ENat.add_le_add_iff_right ENat.one_ne_top).mp
    rw [hdepth, ← Nat.cast_add_one, hlen]
    exact hdR
  obtain ⟨s, hs, hsm, hsn⟩ := exists_weaklyRegular_of_le_depth n hdC
  refine ⟨s, fun r hr => (mem_maximalIdeal r).mp (hsm r hr), ?_, ?_⟩
  · exact (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hsm).mpr hs
  · rw [hsn, hn]

omit [IsLocalRing R] in
/-- Full regular sequences transport along actual ring equivalences. -/
theorem fullRegularSequence_map {S : Type*} [CommRing S] (e : R ≃+* S)
    (rs : List R) (hrs : ∀ r ∈ rs, ¬ IsUnit r)
    (hreg : Sequence.IsRegular R rs)
    (hdim : (rs.length : WithBot ℕ∞) = ringKrullDim R) :
    ∃ s : List S, (∀ r ∈ s, ¬ IsUnit r) ∧ Sequence.IsRegular S s ∧
      (s.length : WithBot ℕ∞) = ringKrullDim S := by
  refine ⟨rs.map e, ?_, ?_, ?_⟩
  · intro r hr hu
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    exact hrs a ha (by simpa using hu.map e.symm.toRingHom)
  · apply (e.toAddEquiv.isRegular_congr (List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr fun r _ x => ?_))).mp hreg
    exact e.map_mul r x
  · rw [List.length_map, hdim, ringKrullDim_eq_of_ringEquiv e]

end PhilipponMultiplicity.RegularCutSupport
namespace PhilipponMultiplicity.Hilbert
open RegularCutSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- The local Cohen--Macaulay condition persists after adding an equation
which is regular in the actual localized quotient. -/
theorem cohenMacaulayAt_sup_span_of_isRegular
    (I : Ideal M.CoordinateRing) (m : MaximalSpectrum M.CoordinateRing)
    (P : M.CoordinateRing)
    (hCM : IsCohenMacaulayAt K M.factorCount M.ambientDimension I m)
    (hreg : IsRegular (Ideal.Quotient.mk
      (I.map (algebraMap M.CoordinateRing (Localization.AtPrime m.asIdeal)))
      (algebraMap M.CoordinateRing (Localization.AtPrime m.asIdeal) P))) :
    IsCohenMacaulayAt K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P}) m := by
  let R := M.CoordinateRing
  let A := Localization.AtPrime m.asIdeal
  let f : R →+* A := algebraMap R A
  let J := I.map f
  let B := A ⧸ J
  letI : CommRing B := inferInstanceAs (CommRing (A ⧸ J))
  let x : B := Ideal.Quotient.mk J (f P)
  let C := B ⧸ Ideal.span {x}
  let D := A ⧸ (I ⊔ Ideal.span {P}).map f
  have hmap : (Ideal.span {f P}).map (Ideal.Quotient.mk J) = Ideal.span {x} := by
    simp only [Ideal.map_span, Set.image_singleton]
    rfl
  have hcut : J ⊔ Ideal.span {f P} = (I ⊔ Ideal.span {P}).map f := by
    simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton, J]
    rfl
  let e : C ≃+* D := (Ideal.quotEquivOfEq hmap.symm).trans
    ((DoubleQuot.quotQuotEquivQuotSup J (Ideal.span {f P})).trans (Ideal.quotEquivOfEq hcut))
  change Subsingleton D ∨ ∃ rs : List D,
    (∀ r ∈ rs, ¬ IsUnit r) ∧ RingTheory.Sequence.IsRegular D rs ∧
    (rs.length : WithBot ℕ∞) = ringKrullDim D
  change Subsingleton B ∨ ∃ rs : List B,
    (∀ r ∈ rs, ¬ IsUnit r) ∧ RingTheory.Sequence.IsRegular B rs ∧
    (rs.length : WithBot ℕ∞) = ringKrullDim B at hCM
  rcases subsingleton_or_nontrivial B with hzero | hnonzero
  · have : Subsingleton C := Function.Surjective.subsingleton
      (Ideal.Quotient.mk_surjective (I := Ideal.span {x}))
    exact Or.inl (e.surjective.subsingleton)
  letI : IsLocalRing B := IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective
  rcases hCM with hzero | ⟨rs, hrs, hseq, hdim⟩
  · exact (not_subsingleton B hzero).elim
  by_cases hx : IsUnit x
  · have htop : Ideal.span {x} = ⊤ := Ideal.span_singleton_eq_top.mpr hx
    have : Subsingleton C := Ideal.Quotient.subsingleton_iff.mpr htop
    exact Or.inl (e.surjective.subsingleton)
  have hxreg : IsSMulRegular B x := hreg.1
  obtain ⟨ss, hss, hsreg, hsdim⟩ := fullRegularSequence_quotient rs hrs hseq hdim x hx hxreg
  have hresult := fullRegularSequence_map (R := C) (S := D) e ss hss hsreg hsdim
  exact Or.inr hresult

end PhilipponMultiplicity.Hilbert

open PhilipponMultiplicity
open PhilipponMultiplicity.SectionThreeSupport
theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (m : MaximalSpectrum M.CoordinateRing)
    (P : M.CoordinateRing)
    (hCM : Hilbert.IsCohenMacaulayAt K M.factorCount M.ambientDimension I m)
    (hreg : IsRegular (Ideal.Quotient.mk
      (I.map (algebraMap M.CoordinateRing (Localization.AtPrime m.asIdeal)))
      (algebraMap M.CoordinateRing (Localization.AtPrime m.asIdeal) P))) :
    Hilbert.IsCohenMacaulayAt K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P}) m := by
  exact PhilipponMultiplicity.Hilbert.cohenMacaulayAt_sup_span_of_isRegular M I m P hCM hreg
