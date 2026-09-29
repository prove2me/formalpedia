-- Prove2me | solution 1 for WeierstrassProjModel.schemeNsmul_locallyQuasiFinite_of_isPointsEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c74cc03c-9e08-5853-afd8-a891ae12bdbb

import Definitions.Def_WeierstrassCurve_ProjModel
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassProjModel_exists_genericPoint_projModelCR_of_field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_schemeNsmul_locallyQuasiFinite_of_isPointsEval

set_option autoImplicit false
set_option Elab.async false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "schemeHomOverComp RelativeGroupLaw RelativeGroupLaw.nsmul_zero RelativeGroupLaw.nsmul_succ RelativeGroupLaw.nsmul_unit projModelHomogeneousIdealCR ProjModelRingCR projModelGradingCR projModelCR projModelStrCR IsPointsEval projModelStrCR_isProper exists_genericPoint_projModelCR_of_field"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra

section Extract

variable {K : Type u} [Field K] (V : WeierstrassCurve.Projective K)

private noncomputable def ha3q_η : Proj (projModelGradingCR V) :=
  Classical.choose (exists_genericPoint_projModelCR_of_field V)

private theorem ha3q_η_bot : (ha3q_η V).asHomogeneousIdeal = ⊥ :=
  (Classical.choose_spec (exists_genericPoint_projModelCR_of_field V)).1

private theorem ha3q_η_toIdeal_bot : (ha3q_η V).asHomogeneousIdeal.toIdeal = ⊥ := by
  rw [ha3q_η_bot V, HomogeneousIdeal.toIdeal_bot]

private theorem ha3q_η_closure :
    closure ({ha3q_η V} : Set (Proj (projModelGradingCR V))) = Set.univ :=
  (Classical.choose_spec (exists_genericPoint_projModelCR_of_field V)).2

private scoped instance ha3q_isDomain : IsDomain (ProjModelRingCR V) := by
  haveI : (⊥ : Ideal (ProjModelRingCR V)).IsPrime := by
    have h := (ha3q_η V).isPrime
    rwa [ha3q_η_bot V, HomogeneousIdeal.toIdeal_bot] at h
  exact IsDomain.of_bot_isPrime (ProjModelRingCR V)

end Extract

private scoped instance ha3q_isProper_projModelStrCR {R : Type*} [CommRing R]
    (V : WeierstrassCurve.Projective R) :
    IsProper (projModelStrCR V) := projModelStrCR_isProper V

section DegreeZero

open MvPolynomial

private theorem ha3q_mem_homogeneousSubmodule_zero_iff_exists_C {σ R : Type*} [CommSemiring R]
    {p : MvPolynomial σ R} :
    p ∈ homogeneousSubmodule σ R 0 ↔ ∃ r : R, C r = p := by
  constructor
  · intro hp
    rw [homogeneousSubmodule_zero] at hp
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hp
    exact ⟨r, by rwa [← algebraMap_eq]⟩
  · rintro ⟨r, rfl⟩
    exact (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ _)

variable {K : Type u} [Field K] (V : WeierstrassCurve.Projective K)

private theorem ha3q_degreeZero_algebraMap_surjective :
    Function.Surjective (algebraMap K ((projModelGradingCR V) 0)) := by
  rintro ⟨b, hb⟩
  obtain ⟨p, hp, rfl⟩ :=
    (mem_quotGradingSubmodule_iff (homogeneousSubmodule (Fin 3) K)
      (projModelHomogeneousIdealCR V).toIdeal).mp hb
  obtain ⟨r, rfl⟩ := ha3q_mem_homogeneousSubmodule_zero_iff_exists_C.mp hp
  exact ⟨r, Subtype.ext rfl⟩

end DegreeZero

namespace RelativeGroupLaw
p2m_export "WeierstrassProjModel.RelativeGroupLaw" "nsmul nsmul_zero nsmul_succ nsmul_unit one_natural nsmul_natural idPoint schemeNsmul schemeNsmul_over one_mul inv one"
p2m_open "WeierstrassProjModel.RelativeGroupLaw"

open NeronModelInfra

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

private theorem schemeHomOverComp_idPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t f) :
    schemeHomOverComp x.1 x.2 (idPoint (f := f)) = x :=
  Subtype.ext (Category.comp_id x.1)

private theorem nsmul_coe_eq_comp_schemeNsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have h : schemeHomOverComp x.1 x.2 (G.nsmul f n idPoint)
      = G.nsmul t n (schemeHomOverComp x.1 x.2 idPoint) :=
    G.nsmul_natural f t x.1 x.2 n idPoint
  rw [schemeHomOverComp_idPoint] at h
  exact (congrArg Subtype.val h).symm

private theorem one_coe_eq_comp_one (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).1 = t ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h : schemeHomOverComp t (Category.comp_id t) (G.one (𝟙 _)) = G.one t :=
    G.one_natural (𝟙 _) t t (Category.comp_id t)
  exact (congrArg Subtype.val h).symm

private scoped instance isProper_schemeNsmul (G : RelativeGroupLaw R f) [IsProper f] (n : ℕ) :
    IsProper (G.schemeNsmul n) := by
  have : IsProper (G.schemeNsmul n ≫ f) := by
    rw [G.schemeNsmul_over n]; infer_instance
  exact IsProper.of_comp (G.schemeNsmul n) f

end RelativeGroupLaw
p2m_reactivate "P2MW.S_WeierstrassProjModel_schemeNsmul_locallyQuasiFinite_of_isPointsEval.WeierstrassProjModel.RelativeGroupLaw"

section FieldProj

variable {K : Type u} [Field K] (V : WeierstrassCurve.Projective K)

private theorem a3b_ringKrullDim_projModelRingCR_lt_three :
    ringKrullDim (ProjModelRingCR V) < (3 : ℕ) := by
  have hF : V.polynomial ∈ nonZeroDivisors (MvPolynomial (Fin 3) K) :=
    mem_nonZeroDivisors_of_ne_zero (polynomial_ne_zero V)
  have h3 : ringKrullDim (MvPolynomial (Fin 3) K) = (3 : ℕ) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field K,
      zero_add, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hle : ringKrullDim (ProjModelRingCR V) + 1 ≤ (3 : ℕ) := by
    rw [← h3]
    show ringKrullDim (MvPolynomial (Fin 3) K ⧸ Ideal.span {V.polynomial}) + 1 ≤ _
    exact ringKrullDim_quotient_succ_le_of_nonZeroDivisor hF
  exact ENat.WithBot.add_one_le_natCast_iff.mp hle

private theorem a3b_exists_algebraMap_of_mem_zero {a : ProjModelRingCR V}
    (ha : a ∈ projModelGradingCR V 0) : ∃ c : K, algebraMap K (ProjModelRingCR V) c = a := by
  obtain ⟨c, hc⟩ := ha3q_degreeZero_algebraMap_surjective V ⟨a, ha⟩
  exact ⟨c, by simpa using congrArg Subtype.val hc⟩

private theorem a3b_le_irrelevant_of_ne_top (𝔮 : HomogeneousIdeal (projModelGradingCR V))
    (h𝔮 : 𝔮.toIdeal ≠ ⊤) :
    𝔮.toIdeal ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR V)).toIdeal := by
  intro x hx
  rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
  have hx0 : (DirectSum.decompose (projModelGradingCR V) x 0 : ProjModelRingCR V) ∈ 𝔮.toIdeal :=
    𝔮.isHomogeneous 0 hx
  obtain ⟨c, hc⟩ := a3b_exists_algebraMap_of_mem_zero V
    (DirectSum.decompose (projModelGradingCR V) x 0).2
  by_contra hne
  apply h𝔮
  rw [← hc] at hx0 hne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by simp)
  exact Ideal.eq_top_of_isUnit_mem _ hx0 ((IsUnit.mk0 c hc0).map _)

private theorem a3b_irrelevant_ne_top :
    (HomogeneousIdeal.irrelevant (projModelGradingCR V)).toIdeal ≠ ⊤ := by
  intro h
  have h1 : (1 : ProjModelRingCR V) ∈ (HomogeneousIdeal.irrelevant (projModelGradingCR V)).toIdeal :=
    h ▸ Submodule.mem_top
  rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
    DirectSum.decompose_of_mem_same _ (SetLike.GradedOne.one_mem)] at h1
  exact one_ne_zero h1

private theorem a3b_eq_of_le_of_ne_bot (x y : Proj (projModelGradingCR V))
    (hxy : x.asHomogeneousIdeal.toIdeal ≤ y.asHomogeneousIdeal.toIdeal)
    (hx : x.asHomogeneousIdeal.toIdeal ≠ ⊥) : x = y := by
  by_contra hne
  have hne' : x.asHomogeneousIdeal.toIdeal ≠ y.asHomogeneousIdeal.toIdeal := fun h =>
    hne (ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective h))
  have hlt : x.asHomogeneousIdeal.toIdeal < y.asHomogeneousIdeal.toIdeal := lt_of_le_of_ne hxy hne'

  obtain ⟨𝔪, h𝔪, hirr𝔪⟩ := Ideal.exists_le_maximal _ (a3b_irrelevant_ne_top V)
  have hy𝔪 : y.asHomogeneousIdeal.toIdeal < 𝔪 := by
    refine lt_of_le_of_ne ((a3b_le_irrelevant_of_ne_top V _ y.isPrime.ne_top).trans hirr𝔪) ?_
    intro hEq
    have hle : (HomogeneousIdeal.irrelevant (projModelGradingCR V)).toIdeal
        ≤ y.asHomogeneousIdeal.toIdeal := by
      rw [hEq]; exact hirr𝔪
    exact y.not_irrelevant_le (toIdeal_le_toIdeal_iff.mp hle)
  haveI : IsDomain (ProjModelRingCR V) := inferInstance

  let p0 : PrimeSpectrum (ProjModelRingCR V) := ⟨⊥, Ideal.isPrime_bot⟩
  let p1 : PrimeSpectrum (ProjModelRingCR V) := ⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩
  let p2 : PrimeSpectrum (ProjModelRingCR V) := ⟨y.asHomogeneousIdeal.toIdeal, y.isPrime⟩
  let p3 : PrimeSpectrum (ProjModelRingCR V) := ⟨𝔪, h𝔪.isPrime⟩
  have h01 : p0 < p1 := bot_lt_iff_ne_bot.mpr (by
    intro h; exact hx (congrArg PrimeSpectrum.asIdeal h))
  have h12 : p1 < p2 := hlt
  have h23 : p2 < p3 := hy𝔪
  let s : LTSeries (PrimeSpectrum (ProjModelRingCR V)) :=
    (((RelSeries.singleton _ p0).snoc p1 (by simpa using h01)).snoc p2 (by simpa using h12)).snoc p3
      (by simpa using h23)
  have hs : s.length = 3 := rfl
  have hlt3 := (Order.krullDim_lt_coe_iff.mp (a3b_ringKrullDim_projModelRingCR_lt_three V)) s
  omega

private theorem a3b_eq_genericPoint_of_toIdeal_eq_bot (x : Proj (projModelGradingCR V))
    (h : x.asHomogeneousIdeal.toIdeal = ⊥) : x = ha3q_η V := by
  refine ProjectiveSpectrum.ext ?_
  rw [ha3q_η_bot V]
  exact HomogeneousIdeal.toIdeal_injective (h.trans HomogeneousIdeal.toIdeal_bot.symm)

private theorem a3b_isClosed_singleton_of_ne_genericPoint (x : Proj (projModelGradingCR V))
    (hx : x ≠ ha3q_η V) :
    IsClosed ({x} : Set (Proj (projModelGradingCR V))) := by
  have hx' : x.asHomogeneousIdeal.toIdeal ≠ ⊥ := fun h =>
    hx (a3b_eq_genericPoint_of_toIdeal_eq_bot V x h)
  rw [← closure_subset_iff_isClosed]
  intro y hy
  have hle : x.asHomogeneousIdeal ≤ y.asHomogeneousIdeal :=
    (ProjectiveSpectrum.as_ideal_le_as_ideal (projModelGradingCR V) x y).mpr
      ((ProjectiveSpectrum.le_iff_mem_closure (𝒜 := projModelGradingCR V) x y).mpr hy)
  exact (a3b_eq_of_le_of_ne_bot V x y hle hx').symm ▸ Set.mem_singleton x

private theorem a3b_finite_of_isClosed_of_genericPoint_not_mem
    (T : Set (Proj (projModelGradingCR V))) (hT : IsClosed T)
    (hη : ha3q_η V ∉ T) : T.Finite := by
  classical
  set 𝔞 : HomogeneousIdeal (projModelGradingCR V) := ProjectiveSpectrum.vanishingIdeal T with h𝔞
  have hT𝔞 : T = ProjectiveSpectrum.zeroLocus (projModelGradingCR V) (𝔞 : Set (ProjModelRingCR V)) := by
    rw [h𝔞, ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hT.closure_eq.symm
  have h𝔞ne : 𝔞.toIdeal ≠ ⊥ := by
    intro h0
    apply hη
    rw [hT𝔞]
    show ((𝔞 : Set (ProjModelRingCR V)) ⊆ _)
    intro a ha
    have : a ∈ 𝔞.toIdeal := ha
    rw [h0] at this
    rw [(Submodule.mem_bot _).mp this]
    exact zero_mem _
  haveI : IsNoetherianRing (ProjModelRingCR V) := inferInstance
  have hfin : (𝔞.toIdeal.minimalPrimes).Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _

  have hmem : ∀ x ∈ T, x.asHomogeneousIdeal.toIdeal ∈ 𝔞.toIdeal.minimalPrimes := by
    intro x hxT
    have h𝔞x : 𝔞.toIdeal ≤ x.asHomogeneousIdeal.toIdeal := by
      intro a ha
      have hxT' : x ∈ ProjectiveSpectrum.zeroLocus (projModelGradingCR V)
          (𝔞 : Set (ProjModelRingCR V)) := hT𝔞 ▸ hxT
      exact hxT' ha
    refine ⟨⟨x.isPrime, h𝔞x⟩, ?_⟩
    rintro q ⟨hq, h𝔞q⟩ hqx

    let x' : Proj (projModelGradingCR V) :=
      { asHomogeneousIdeal := q.homogeneousCore (projModelGradingCR V)
        isPrime := hq.homogeneousCore
        not_irrelevant_le := fun hle =>
          x.not_irrelevant_le (hle.trans ((Ideal.toIdeal_homogeneousCore_le _ q).trans hqx)) }
    have hx'x : x'.asHomogeneousIdeal.toIdeal ≤ x.asHomogeneousIdeal.toIdeal :=
      (Ideal.toIdeal_homogeneousCore_le _ q).trans hqx
    have h𝔞x' : 𝔞.toIdeal ≤ x'.asHomogeneousIdeal.toIdeal :=
      𝔞.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ h𝔞q)
    have hx'ne : x'.asHomogeneousIdeal.toIdeal ≠ ⊥ := fun h0 =>
      h𝔞ne (le_bot_iff.mp (h0 ▸ h𝔞x'))
    have hEq := a3b_eq_of_le_of_ne_bot V x' x hx'x hx'ne
    calc x.asHomogeneousIdeal.toIdeal = x'.asHomogeneousIdeal.toIdeal := by rw [hEq]
      _ ≤ q := Ideal.toIdeal_homogeneousCore_le _ q
  have hinj : Set.InjOn (fun x : Proj (projModelGradingCR V) => x.asHomogeneousIdeal.toIdeal) T := by
    intro x _ y _ hxy
    exact ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective hxy)
  exact Set.Finite.of_finite_image (hfin.subset (Set.image_subset_iff.mpr hmem)) hinj

end FieldProj
p2m_reactivate "P2MW.S_WeierstrassProjModel_schemeNsmul_locallyQuasiFinite_of_isPointsEval.WeierstrassProjModel.RelativeGroupLaw"

section FibreTransport

open CategoryTheory.Limits

variable {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)

private theorem a3b_nonempty_fiber_iso
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
      Nonempty (pullback (projModelStrCR V) (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        ≅ projModelCR (V.baseChange K)))
    (y : Spec (CommRingCat.of R)) :
    Nonempty ((projModelStrCR V).fiber y ≅ projModelCR (V.baseChange y.asIdeal.ResidueField)) := by
  obtain ⟨Φ⟩ := hbc y.asIdeal.ResidueField
  let ι := Spec.map (Scheme.Spec.residueFieldIso (.of R) y).inv
  let σ := Spec.map (CommRingCat.ofHom (algebraMap R y.asIdeal.ResidueField))
  have hσ : ι ≫ σ = (Spec (CommRingCat.of R)).fromSpecResidueField y :=
    Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) y
  let Φ₁ : (projModelStrCR V).fiber y ≅ pullback (projModelStrCR V) σ :=
    pullback.congrHom rfl hσ.symm ≪≫
      asIso (pullback.map (projModelStrCR V) (ι ≫ σ) (projModelStrCR V) σ (𝟙 _) ι (𝟙 _)
        (by simp) (by simp))
  exact ⟨Φ₁ ≪≫ Φ⟩

private theorem a3b_fibre_package
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
      Nonempty (pullback (projModelStrCR V) (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        ≅ projModelCR (V.baseChange K)))
    (y : Spec (CommRingCat.of R)) :
    ∃ η : ↥(projModelCR V), η ∈ (projModelStrCR V) ⁻¹' {y} ∧
      (projModelStrCR V) ⁻¹' {y} ⊆ closure {η} ∧
      (∀ C : Set ↥(projModelCR V), IsClosed C → η ∉ C →
        (C ∩ (projModelStrCR V) ⁻¹' {y}).Finite) ∧
      (∀ z ∈ (projModelStrCR V) ⁻¹' {y}, z ≠ η →
        ∀ z' ∈ (projModelStrCR V) ⁻¹' {y}, z' ∈ closure {z} → z' = z) := by
  classical
  obtain ⟨Ψ⟩ := a3b_nonempty_fiber_iso V hbc y
  set K := y.asIdeal.ResidueField

  let h : ↥(projModelCR (V.baseChange K)) ≃ₜ ↥((projModelStrCR V) ⁻¹' {y}) :=
    (Scheme.homeoOfIso Ψ.symm).trans ((projModelStrCR V).fiberHomeo y)
  let ηK : ↥(projModelCR (V.baseChange K)) := ha3q_η (V.baseChange K)
  refine ⟨(h ηK).1, (h ηK).2, ?_, ?_, ?_⟩
  ·
    intro z hz
    have hx : h.symm ⟨z, hz⟩ ∈ closure ({ηK} : Set _) := by
      rw [ha3q_η_closure]; trivial
    have h1 : h (h.symm ⟨z, hz⟩) ∈ closure ({h ηK} : Set _) := by
      rw [← Set.image_singleton, ← h.image_closure]
      exact Set.mem_image_of_mem _ hx
    rw [h.apply_symm_apply] at h1
    have h2 : (⟨z, hz⟩ : ↥((projModelStrCR V) ⁻¹' {y})).1 ∈ closure ({(h ηK).1} : Set _) :=
      closure_subtype.mp h1 |> fun h' => by simpa [Set.image_singleton] using h'
    exact h2
  ·
    intro C hC hηC
    let T' : Set ↥(projModelCR (V.baseChange K)) := (fun x => (h x).1) ⁻¹' C
    have hT' : IsClosed T' := hC.preimage (continuous_subtype_val.comp h.continuous)
    have hηT' : ηK ∉ T' := hηC
    have hfin : T'.Finite :=
      a3b_finite_of_isClosed_of_genericPoint_not_mem (V.baseChange K) T' hT' hηT'
    refine (hfin.image (fun x => (h x).1)).subset ?_
    rintro z ⟨hzC, hzy⟩
    refine ⟨h.symm ⟨z, hzy⟩, ?_, ?_⟩
    · show (h (h.symm ⟨z, hzy⟩)).1 ∈ C
      rw [h.apply_symm_apply]; exact hzC
    · show (h (h.symm ⟨z, hzy⟩)).1 = z
      rw [h.apply_symm_apply]
  ·
    intro z hz hzη z' hz' hcl
    let x := h.symm ⟨z, hz⟩
    let x' := h.symm ⟨z', hz'⟩
    have hxη : x ≠ ηK := by
      intro hEq
      apply hzη
      have : h x = h ηK := by rw [hEq]
      rw [h.apply_symm_apply] at this
      exact congrArg Subtype.val this
    have hcl' : (⟨z', hz'⟩ : ↥((projModelStrCR V) ⁻¹' {y})) ∈
        closure ({⟨z, hz⟩} : Set ↥((projModelStrCR V) ⁻¹' {y})) := by
      rw [closure_subtype]
      simpa [Set.image_singleton] using hcl
    have hx'cl : x' ∈ closure ({x} : Set _) := by
      have himg : h.symm ⟨z', hz'⟩ ∈ h.symm '' closure ({⟨z, hz⟩} : Set ↥((projModelStrCR V) ⁻¹' {y})) :=
        Set.mem_image_of_mem h.symm hcl'
      rw [h.symm.image_closure, Set.image_singleton] at himg
      exact himg
    have hx'x : x' = x := by
      have hc := (a3b_isClosed_singleton_of_ne_genericPoint (V.baseChange K) x hxη).closure_eq
      rw [hc] at hx'cl
      exact hx'cl
    have : (h x').1 = (h x).1 := by rw [hx'x]
    simpa [x, x', h.apply_symm_apply] using this

end FibreTransport
p2m_reactivate "P2MW.S_WeierstrassProjModel_schemeNsmul_locallyQuasiFinite_of_isPointsEval.WeierstrassProjModel.RelativeGroupLaw"

section SectionUnique

open IsLocalRing

private lemma a3a_residueFieldMap_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (x : X) :
    f.residueFieldMap x =
      (Y.residueFieldCongr (by rw [h] : f.base x = g.base x)).hom ≫ g.residueFieldMap x := by
  subst h; simp

private theorem a3a_eq_comp_of_base_apply_eq {X : Scheme.{u}} {R : Type u} [CommRing R]
    (f : X ⟶ Spec (.of R)) (e : Spec (.of R) ⟶ X) (he : e ≫ f = 𝟙 _)
    {F : Type u} [Field F] (t : Spec (.of F) ⟶ Spec (.of R))
    (Q : Spec (.of F) ⟶ X) (hQ : Q ≫ f = t)
    (hpt : Q.base (closedPoint F) = e.base (t.base (closedPoint F))) :
    Q = t ≫ e := by

  have hfe : f.base (e.base (t.base (closedPoint F))) = t.base (closedPoint F) := by
    have h := congrArg (fun (g : Spec (.of R) ⟶ Spec (.of R)) => g.base (t.base (closedPoint F))) he
    simpa using h

  have hQd := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField F X Q
  have htd := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField F (Spec (.of R)) t
  set qφ₀ := X.descResidueField (Scheme.stalkClosedPointTo Q) with hqφ₀
  set tφ := (Spec (.of R)).descResidueField (Scheme.stalkClosedPointTo t) with htφ

  set qφ' := (X.residueFieldCongr hpt).inv ≫ qφ₀ with hqφ'
  have hQd' : Spec.map qφ' ≫ X.fromSpecResidueField (e.base (t.base (closedPoint F))) = Q := by
    rw [hqφ', Spec.map_comp, Category.assoc, ← Iso.symm_hom, Scheme.residueFieldCongr_symm,
      Scheme.residueFieldCongr_fromSpecResidueField]
    exact hQd

  have hQf : Spec.map (f.residueFieldMap (e.base (t.base (closedPoint F))) ≫ qφ') ≫
      (Spec (.of R)).fromSpecResidueField (f.base (e.base (t.base (closedPoint F)))) = Q ≫ f := by
    rw [Spec.map_comp, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Category.assoc, hQd']
  have htf : Spec.map (((Spec (.of R)).residueFieldCongr hfe).hom ≫ tφ) ≫
      (Spec (.of R)).fromSpecResidueField (f.base (e.base (t.base (closedPoint F)))) = t := by
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
    exact htd
  have K1 : f.residueFieldMap (e.base (t.base (closedPoint F))) ≫ qφ' =
      ((Spec (.of R)).residueFieldCongr hfe).hom ≫ tφ :=
    Spec.map_injective ((cancel_mono _).mp (hQf.trans (hQ.trans htf.symm)))

  have K2 : f.residueFieldMap (e.base (t.base (closedPoint F))) ≫
        e.residueFieldMap (t.base (closedPoint F)) =
      ((Spec (.of R)).residueFieldCongr hfe).hom := by
    have h0 := a3a_residueFieldMap_congr he (t.base (closedPoint F))
    rw [Scheme.residueFieldMap_comp] at h0
    simpa using h0

  set A := f.residueFieldMap (e.base (t.base (closedPoint F))) with hA
  set B := e.residueFieldMap (t.base (closedPoint F)) with hB
  set D := ((Spec (.of R)).residueFieldCongr hfe).inv ≫ A with hD
  have hDB : D ≫ B = 𝟙 _ := by
    rw [hD, Category.assoc, K2, Iso.inv_hom_id]
  have hBD : B ≫ D = 𝟙 _ := by
    have hinj : Function.Injective B.hom := RingHom.injective _
    ext z
    apply hinj
    have h := congrArg (fun (g : (Spec (.of R)).residueField (t.base (closedPoint F)) ⟶
        (Spec (.of R)).residueField (t.base (closedPoint F))) => g.hom (B.hom z)) hDB
    simpa using h

  have hkey : qφ' = B ≫ tφ := by
    have htφ' : tφ = (((Spec (.of R)).residueFieldCongr hfe).inv ≫ A) ≫ qφ' := by
      rw [Category.assoc, K1, Iso.inv_hom_id_assoc]
    rw [htφ', ← hD, ← Category.assoc, hBD, Category.id_comp]
  have hte : Spec.map (B ≫ tφ) ≫
      X.fromSpecResidueField (e.base (t.base (closedPoint F))) = t ≫ e := by
    rw [Spec.map_comp, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Category.assoc, htd]
  rw [← hQd', hkey, hte]

end SectionUnique
p2m_reactivate "P2MW.S_WeierstrassProjModel_schemeNsmul_locallyQuasiFinite_of_isPointsEval.WeierstrassProjModel.RelativeGroupLaw"

section LQF

p2m_open "CategoryTheory.Limits WeierstrassProjModel P2MW.S_WeierstrassProjModel_schemeNsmul_locallyQuasiFinite_of_isPointsEval.WeierstrassProjModel NeronModelInfra IsLocalRing"

variable {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)

private theorem a3b_one_comp_schemeNsmul (G : RelativeGroupLaw R (projModelStrCR V)) (m : ℕ) :
    (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ G.schemeNsmul m =
      (G.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  rw [← RelativeGroupLaw.nsmul_coe_eq_comp_schemeNsmul, RelativeGroupLaw.nsmul_unit]

private theorem a3b_isClosed_range_one (G : RelativeGroupLaw R (projModelStrCR V)) :
    IsClosed (Set.range (G.one (𝟙 (Spec (CommRingCat.of R)))).1) := by
  have h1 : IsClosedImmersion ((G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ projModelStrCR V) := by
    rw [(G.one (𝟙 (Spec (CommRingCat.of R)))).2]; infer_instance
  have : IsClosedImmersion (G.one (𝟙 (Spec (CommRingCat.of R)))).1 :=
    IsClosedImmersion.of_comp _ (projModelStrCR V)
  exact (G.one (𝟙 (Spec (CommRingCat.of R)))).1.isClosedEmbedding.isClosed_range

variable (G : RelativeGroupLaw R (projModelStrCR V))
  (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
      (V.baseChange F).toAffine.Point)

private theorem a3b_ev_one (hev : IsPointsEval V G ev)
    (F : Type u) [Field F] [DecidableEq F] [Algebra R F] :
    ev F (G.one (Spec.map (CommRingCat.ofHom (algebraMap R F)))) = 0 := by
  have h := hev.1 F (G.one _) (G.one _)
  rw [G.one_mul] at h
  simpa using h

private theorem a3b_ev_nsmul (hev : IsPointsEval V G ev)
    (F : Type u) [Field F] [DecidableEq F] [Algebra R F] (k : ℕ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V)) :
    ev F (G.nsmul (Spec.map (CommRingCat.ofHom (algebraMap R F))) k x) = k • ev F x := by
  induction k with
  | zero => rw [RelativeGroupLaw.nsmul_zero, a3b_ev_one V G ev hev F, zero_nsmul]
  | succ k ih => rw [RelativeGroupLaw.nsmul_succ, hev.1, ih, succ_nsmul]

private theorem a3b_not_constant_on_fibre (hev : IsPointsEval V G ev)
    (hℓ : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F] [IsAlgClosed F] (ℓ : ℕ),
      ℓ.Prime → (ℓ : F) ≠ 0 → ∃ P : (V.baseChange F).toAffine.Point, P ≠ 0 ∧ ℓ • P = 0)
    (y : Spec (CommRingCat.of R)) {m : ℕ} (hm : 0 < m)
    (hconst : ∀ z : ↥(projModelCR V), projModelStrCR V z = y →
      G.schemeNsmul m z = (G.one (𝟙 (Spec (CommRingCat.of R)))).1 y) : False := by
  classical
  let K := y.asIdeal.ResidueField
  let F := AlgebraicClosure K

  obtain ⟨ℓ, hℓle, hℓp⟩ := Nat.exists_infinite_primes (max m (ringChar F) + 1)
  have hmℓ : m < ℓ := by omega
  have hcharℓ : ringChar F < ℓ := by omega
  have hℓF : (ℓ : F) ≠ 0 := by
    intro h0
    rcases (Nat.dvd_prime hℓp).mp ((ringChar.spec F ℓ).mp h0) with h1 | h2
    · exact CharP.ringChar_ne_one h1
    · omega
  obtain ⟨P, hP0, hℓP⟩ := hℓ F ℓ hℓp hℓF
  let t : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R F))
  let x : SchemeHomOver t (projModelStrCR V) := (ev F).symm P
  have hx : ev F x = P := (ev F).apply_symm_apply P

  have hσ : (Spec.map (CommRingCat.ofHom (algebraMap R K))) (closedPoint K) = y := by
    have h3 := congrArg (fun g : Spec ((Spec (CommRingCat.of R)).residueField y) ⟶ _ =>
      g (closedPoint _)) (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) y)
    dsimp only at h3
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at h3
    rwa [Subsingleton.elim ((Spec.map (Scheme.Spec.residueFieldIso (.of R) y).inv) (closedPoint _))
      (closedPoint K)] at h3
  have ht : t (closedPoint F) = y := by
    have h1 : t = Spec.map (CommRingCat.ofHom (algebraMap K F)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq R K F]
    rw [h1, Scheme.Hom.comp_apply,
      Subsingleton.elim ((Spec.map (CommRingCat.ofHom (algebraMap K F))) (closedPoint F))
        (closedPoint K), hσ]

  have hxy : projModelStrCR V (x.1 (closedPoint F)) = y := by
    rw [← Scheme.Hom.comp_apply, x.2]; exact ht

  have hQ : (G.nsmul t m x).1 = (G.one t).1 := by
    rw [RelativeGroupLaw.nsmul_coe_eq_comp_schemeNsmul, RelativeGroupLaw.one_coe_eq_comp_one]
    refine a3a_eq_comp_of_base_apply_eq (projModelStrCR V)
      (G.one (𝟙 (Spec (CommRingCat.of R)))).1 (G.one (𝟙 (Spec (CommRingCat.of R)))).2 t _ ?_ ?_
    · rw [Category.assoc, G.schemeNsmul_over, x.2]
    · show (x.1 ≫ G.schemeNsmul m) (closedPoint F) = _
      rw [Scheme.Hom.comp_apply, hconst _ hxy, ht]
  have hnsmul : G.nsmul t m x = G.one t := Subtype.ext hQ

  have hmP : m • P = 0 := by
    rw [← hx, ← a3b_ev_nsmul V G ev hev F m x, hnsmul, a3b_ev_one V G ev hev F]
  have hcop : Nat.Coprime m ℓ :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hℓp).mpr
      (Nat.not_dvd_of_pos_of_lt hm hmℓ)))
  have h1 : addOrderOf P ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hmP) (addOrderOf_dvd_of_nsmul_eq_zero hℓP)
  exact hP0 (AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))

private theorem a3b_finite_preimage_schemeNsmul
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
      Nonempty (pullback (projModelStrCR V) (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        ≅ projModelCR (V.baseChange K)))
    (hev : IsPointsEval V G ev)
    (hℓ : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F] [IsAlgClosed F] (ℓ : ℕ),
      ℓ.Prime → (ℓ : F) ≠ 0 → ∃ P : (V.baseChange F).toAffine.Point, P ≠ 0 ∧ ℓ • P = 0)
    {m : ℕ} (hm : 0 < m) (z : ↥(projModelCR V)) :
    ((G.schemeNsmul m) ⁻¹' {z}).Finite := by
  classical
  let y := projModelStrCR V z
  obtain ⟨η, hηy, hcl, hfin, hrel⟩ := a3b_fibre_package V hbc y

  have hover : ∀ w, projModelStrCR V (G.schemeNsmul m w) = projModelStrCR V w := fun w => by
    rw [← Scheme.Hom.comp_apply, G.schemeNsmul_over]
  let e := (G.one (𝟙 (Spec (CommRingCat.of R)))).1
  have he : ∀ s, projModelStrCR V (e s) = s := fun s => by
    rw [← Scheme.Hom.comp_apply, (G.one (𝟙 (Spec (CommRingCat.of R)))).2]; rfl
  have hNe : ∀ s, G.schemeNsmul m (e s) = e s := fun s => by
    rw [← Scheme.Hom.comp_apply, a3b_one_comp_schemeNsmul]
  have hNcl : IsClosedMap (G.schemeNsmul m) := (G.schemeNsmul m).isClosedMap
  have hNcont : Continuous (G.schemeNsmul m) := (G.schemeNsmul m).continuous
  have hoy : e y ∈ (projModelStrCR V) ⁻¹' {y} := he y
  have hzy : z ∈ (projModelStrCR V) ⁻¹' {y} := Set.mem_singleton _

  have hH2 : η = e y → ∀ v ∈ (projModelStrCR V) ⁻¹' {y}, v = e y := by
    intro hηo v hv
    have hvcl : v ∈ closure {e y} := hηo ▸ hcl hv
    have hvr : v ∈ Set.range e :=
      ((a3b_isClosed_range_one V G).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨y, rfl⟩))
        hvcl
    obtain ⟨s, rfl⟩ := hvr
    have hs : s = y := (he s).symm.trans hv
    rw [hs]

  have hH1 : ∀ w ∈ (projModelStrCR V) ⁻¹' {y}, w ≠ η → G.schemeNsmul m w = η → η = e y := by
    intro w hw hwη hNw
    have hclosed : IsClosed (G.schemeNsmul m '' closure {w}) := hNcl _ isClosed_closure
    have hηin : η ∈ G.schemeNsmul m '' closure {w} := ⟨w, subset_closure rfl, hNw⟩
    have hsub : closure {η} ⊆ G.schemeNsmul m '' closure {w} :=
      hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηin)
    obtain ⟨w', hw'cl, hw'o⟩ := hsub (hcl hoy)
    have hw'y : w' ∈ (projModelStrCR V) ⁻¹' {y} := by
      rw [Set.mem_preimage, ← hover w', hw'o]; exact hoy
    have hw'w : w' = w := hrel w hw hwη w' hw'y hw'cl
    calc η = G.schemeNsmul m w := hNw.symm
      _ = G.schemeNsmul m w' := by rw [hw'w]
      _ = e y := hw'o

  have hTy : (G.schemeNsmul m) ⁻¹' {z} ⊆ (projModelStrCR V) ⁻¹' {y} := by
    intro w hw
    rw [Set.mem_preimage, ← hover w, Set.mem_singleton_iff.mp hw]; exact hzy
  by_cases hA : G.schemeNsmul m η = z
  ·
    have himg : ∀ w ∈ (projModelStrCR V) ⁻¹' {y}, G.schemeNsmul m w ∈ closure {z} := by
      intro w hw
      have h2 := image_closure_subset_closure_image hNcont
        (⟨w, hcl hw, rfl⟩ : G.schemeNsmul m w ∈ G.schemeNsmul m '' closure {η})
      rwa [Set.image_singleton, hA] at h2
    by_cases hzη : z = η
    ·
      refine (Set.finite_singleton η).subset ?_
      intro w hw
      by_contra hwη
      have hNw : G.schemeNsmul m w = η := (Set.mem_singleton_iff.mp hw).trans hzη
      have hηo := hH1 w (hTy hw) hwη hNw
      exact hwη ((hH2 hηo w (hTy hw)).trans hηo.symm)
    ·
      exfalso
      have hconstz : ∀ w ∈ (projModelStrCR V) ⁻¹' {y}, G.schemeNsmul m w = z := fun w hw =>
        hrel z hzy hzη _ (by rw [Set.mem_preimage, hover]; exact hw) (himg w hw)
      have hzo : z = e y := (hconstz (e y) hoy).symm.trans (hNe y)
      exact a3b_not_constant_on_fibre V G ev hev hℓ y hm (fun w hw => by
        rw [hconstz w hw, hzo])
  · by_cases hzη : z = η
    ·
      refine Set.finite_empty.subset ?_
      intro w hw
      exfalso
      have hNw : G.schemeNsmul m w = η := (Set.mem_singleton_iff.mp hw).trans hzη
      have hwη : w ≠ η := fun h => hA (by rw [← h, hNw, hzη])
      have hηo := hH1 w (hTy hw) hwη hNw
      exact hwη ((hH2 hηo w (hTy hw)).trans hηo.symm)
    ·
      let C : Set ↥(projModelCR V) := (G.schemeNsmul m) ⁻¹' closure {z}
      have hC : IsClosed C := isClosed_closure.preimage hNcont
      have hηC : η ∉ C := fun hηC => hA
        (hrel z hzy hzη _ (by rw [Set.mem_preimage, hover]; exact hηy) hηC)
      refine (hfin C hC hηC).subset ?_
      intro w hw
      exact ⟨subset_closure hw, hTy hw⟩

private theorem a3b_nsmulLocallyQuasiFinite
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
      Nonempty (pullback (projModelStrCR V) (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        ≅ projModelCR (V.baseChange K)))
    (hev : IsPointsEval V G ev)
    (hℓ : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F] [IsAlgClosed F] (ℓ : ℕ),
      ℓ.Prime → (ℓ : F) ≠ 0 → ∃ P : (V.baseChange F).toAffine.Point, P ≠ 0 ∧ ℓ • P = 0) :
    ∀ n : ℕ, 0 < n → LocallyQuasiFinite (G.schemeNsmul n) := by
  intro m hm
  exact LocallyQuasiFinite.of_finite_preimage_singleton (G.schemeNsmul m)
    (fun z => a3b_finite_preimage_schemeNsmul V G ev hbc hev hℓ hm z)

end LQF
p2m_reactivate "P2MW.S_WeierstrassProjModel_schemeNsmul_locallyQuasiFinite_of_isPointsEval.WeierstrassProjModel.RelativeGroupLaw"

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_schemeNsmul_locallyQuasiFinite_of_isPointsEval.WeierstrassProjModel.RelativeGroupLaw P2MW.S_WeierstrassProjModel_schemeNsmul_locallyQuasiFinite_of_isPointsEval.WeierstrassProjModel"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_schemeNsmul_locallyQuasiFinite_of_isPointsEval.WeierstrassProjModel.RelativeGroupLaw P2MW.S_WeierstrassProjModel_schemeNsmul_locallyQuasiFinite_of_isPointsEval.WeierstrassProjModel"

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra _root_.WeierstrassProjModel _root_.P2MW.S_WeierstrassProjModel_schemeNsmul_locallyQuasiFinite_of_isPointsEval.WeierstrassProjModel in
theorem solution
    {R : Type u} [CommRing R]
    (V : WeierstrassCurve.Projective R)
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
      Nonempty (pullback (projModelStrCR V)
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        ≅ projModelCR (V.baseChange K)))
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev)
    (hℓ : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F] [IsAlgClosed F] (ℓ : ℕ),
      ℓ.Prime → (ℓ : F) ≠ 0 →
      ∃ P : (V.baseChange F).toAffine.Point, P ≠ 0 ∧ ℓ • P = 0) :
    ∀ n : ℕ, 0 < n → LocallyQuasiFinite (G.schemeNsmul n) :=
  WeierstrassProjModel.a3b_nsmulLocallyQuasiFinite V G ev hbc hev hℓ

end S_WeierstrassProjModel_schemeNsmul_locallyQuasiFinite_of_isPointsEval
end P2MW
export P2MW.S_WeierstrassProjModel_schemeNsmul_locallyQuasiFinite_of_isPointsEval (solution)
