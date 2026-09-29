-- Prove2me | solution 1 for PDivisibleGroup.exists_square_presentation_level_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0cf94dda-885c-5045-af20-f61e36d2c305

import Mathlib
import Theorems.Thm_HopfAlgebra_exists_ker_map_localization_eq_span_of_surjective_mvPolynomial_of_isMaximal
import Theorems.Thm_Ideal_exists_map_localization_eq_span_of_flat_of_residueField_mvPolynomial
import Theorems.Thm_Ideal_exists_forall_map_localization_eq_span_of_finite_maximal
import Theorems.Thm_Ideal_exists_isIdempotentElem_map_mk_eq_span_of_forall_map_localization_eq
import Theorems.Thm_MvPolynomial_exists_quotient_span_quotient_span_singleton_algEquiv_of_isIdempotentElem
import Theorems.Thm_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_square_presentation_level_of_ringOfIntegers
set_option maxHeartbeats 4000000
p2m_attr_erase "instance" "HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.IsHopfTower.refl HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option Elab.async false

open scoped TensorProduct

universe u

namespace Ideal p2m_export "Ideal" "map_le_iff_le_comap map_map Quotient.eq_zero_iff_mem quotientKerAlgEquivOfSurjective Quotient.mkₐ map_span span map_eq_top_or_isMaximal_of_surjective IsMaximal Quotient.mk mul_mem_left map mk_ker quotientEquivAlgOfEq ext Quotient.algebraQuotientMapQuotient isMaximal_comap_of_isIntegral_of_isMaximal mem_map_of_mem span_le ResidueField comap_map_of_surjective mem_comap comap_top comap mem_map_iff_of_surjective Quotient.mk_surjective exists_map_localization_eq_span_of_flat_of_residueField_mvPolynomial exists_forall_map_localization_eq_span_of_finite_maximal exists_isIdempotentElem_map_mk_eq_span_of_forall_map_localization_eq" end Ideal
p2m_open_scoped "Ideal" in
theorem Ideal.map_maximalIdeal_le_of_finite_quotient_ASM {R : Type*} [CommRing R] [IsLocalRing R]
    {P : Type*} [CommRing P] [Algebra R P] (J : Ideal P) [Module.Finite R (P ⧸ J)]
    (𝔫 : Ideal P) [h𝔫 : 𝔫.IsMaximal] (h : J ≤ 𝔫) :
    (IsLocalRing.maximalIdeal R).map (algebraMap R P) ≤ 𝔫 := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  have hcomap : (𝔫.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = 𝔫 := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.2 h
  have hmax : (𝔫.map (Ideal.Quotient.mk J)).IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj h𝔫 with htop | hm
    · exfalso
      apply h𝔫.ne_top
      rw [← hcomap, htop, Ideal.comap_top]
    · exact hm
  have h2 := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (𝔫.map (Ideal.Quotient.mk J))
  have h3 : (𝔫.map (Ideal.Quotient.mk J)).comap (algebraMap R (P ⧸ J)) = 𝔫.comap (algebraMap R P) := by
    ext r
    rw [Ideal.mem_comap, Ideal.mem_comap,
      show algebraMap R (P ⧸ J) r = Ideal.Quotient.mk J (algebraMap R P r) from rfl,
      ← Ideal.mem_comap (f := Ideal.Quotient.mk J), hcomap]
  rw [h3] at h2
  rw [Ideal.map_le_iff_le_comap, ← IsLocalRing.eq_maximalIdeal h2]

set_option maxHeartbeats 8000000 in
theorem dlc_core
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (A : Type) [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A] :
    ∃ (m : ℕ) (f : Fin m → MvPolynomial (Fin m) R),
      Nonempty ((MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) ≃ₐ[R] A) := by
  classical

  obtain ⟨N, φ, hφ⟩ : ∃ (N : ℕ) (φ : MvPolynomial (Fin N) R →ₐ[R] A), Function.Surjective φ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.1 inferInstance
  set P := MvPolynomial (Fin N) R with hPdef
  set J : Ideal P := RingHom.ker φ with hJdef
  let eJ : (P ⧸ J) ≃ₐ[R] A := Ideal.quotientKerAlgEquivOfSurjective hφ

  haveI : Module.Finite R (P ⧸ J) := Module.Finite.equiv eJ.symm.toLinearEquiv
  haveI : Module.Flat R (P ⧸ J) := Module.Flat.of_linearEquiv eJ.toLinearEquiv

  let κ := IsLocalRing.ResidueField R
  let π : P →+* MvPolynomial (Fin N) κ := MvPolynomial.map (IsLocalRing.residue R)
  let B := κ ⊗[R] A
  let τ : κ ⊗[R] P ≃ₐ[κ] MvPolynomial (Fin N) κ := MvPolynomial.algebraTensorAlgEquiv R κ
  let φκ : MvPolynomial (Fin N) κ →ₐ[κ] B := (Algebra.TensorProduct.map (AlgHom.id κ κ) φ).comp τ.symm.toAlgHom
  have hτ : ∀ f : P, τ ((1 : κ) ⊗ₜ[R] f) = π f := by
    intro f
    change MvPolynomial.algebraTensorAlgEquiv R κ ((1 : κ) ⊗ₜ[R] f) = MvPolynomial.map (IsLocalRing.residue R) f
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
    rfl
  have hφκs : Function.Surjective φκ := by
    refine (Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hφ).comp τ.symm.surjective
  haveI : Module.Finite κ B := inferInstance
  have hkerκ : RingHom.ker φκ = J.map π := by

    apply le_antisymm
    · intro g hg
      obtain ⟨t, rfl⟩ := τ.surjective g
      have h0 : Algebra.TensorProduct.map (AlgHom.id κ κ) φ t = 0 := by
        have := hg; rwa [RingHom.mem_ker, show φκ (τ t) = Algebra.TensorProduct.map (AlgHom.id κ κ) φ (τ.symm (τ t)) from rfl,
          τ.symm_apply_apply] at this

      let ιJ : J.restrictScalars R →ₗ[R] P := (J.restrictScalars R).subtype
      have hex : Function.Exact (ιJ.lTensor κ) ((φ : P →ₐ[R] A).toLinearMap.lTensor κ) := by
        refine lTensor_exact κ (fun y => ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, ?_⟩) hφ
        rintro ⟨z, rfl⟩; exact z.2
      have h0' : ((φ : P →ₐ[R] A).toLinearMap.lTensor κ) t = 0 := by
        rw [← h0]; rfl
      obtain ⟨s, hs⟩ := (hex t).1 h0'
      rw [← hs]
      clear hs h0 h0' hg
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul c j =>
        rw [LinearMap.lTensor_tmul]
        change τ (c ⊗ₜ[R] (j : P)) ∈ J.map π
        have : c ⊗ₜ[R] (j : P) = c • ((1 : κ) ⊗ₜ[R] (j : P)) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this, map_smul, hτ, Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem π j.2)
      | add x y hx hy => rw [map_add, map_add]; exact Ideal.add_mem _ hx hy
    · rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, RingHom.mem_ker, ← hτ]
      change Algebra.TensorProduct.map (AlgHom.id κ κ) φ (τ.symm (τ ((1 : κ) ⊗ₜ[R] f))) = 0
      rw [τ.symm_apply_apply, Algebra.TensorProduct.map_tmul, show φ f = 0 from hf, TensorProduct.tmul_zero]
  have hfib : ∀ (𝔫 : Ideal (MvPolynomial (Fin N) (IsLocalRing.ResidueField R))) [𝔫.IsMaximal],
      Ideal.map (MvPolynomial.map (IsLocalRing.residue R)) (RingHom.ker φ) ≤ 𝔫 →
      ∃ g : Fin N → MvPolynomial (Fin N) (IsLocalRing.ResidueField R),
        (∀ i, g i ∈ Ideal.map (MvPolynomial.map (IsLocalRing.residue R)) (RingHom.ker φ)) ∧
        Ideal.map (algebraMap _ (Localization.AtPrime 𝔫)) (Ideal.map (MvPolynomial.map (IsLocalRing.residue R)) (RingHom.ker φ)) =
          Ideal.span (Set.range fun i => algebraMap _ (Localization.AtPrime 𝔫) (g i)) := by
    intro 𝔫 _ h𝔫
    have h𝔫' : RingHom.ker φκ ≤ 𝔫 := hkerκ ▸ h𝔫
    obtain ⟨g, hg, hloc⟩ := HopfAlgebra.exists_ker_map_localization_eq_span_of_surjective_mvPolynomial_of_isMaximal κ B N φκ hφκs 𝔫 h𝔫'
    refine ⟨g, fun i => hkerκ ▸ hg i, ?_⟩
    rw [← hkerκ]; exact hloc

  have hloc : ∀ (𝔫 : Ideal (MvPolynomial (Fin N) R)) [𝔫.IsMaximal], RingHom.ker φ ≤ 𝔫 →
      ∃ g : Fin N → MvPolynomial (Fin N) R, (∀ i, g i ∈ RingHom.ker φ) ∧
        Ideal.map (algebraMap (MvPolynomial (Fin N) R) (Localization.AtPrime 𝔫)) (RingHom.ker φ) =
          Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin N) R) (Localization.AtPrime 𝔫) (g i)) :=
    fun 𝔫 _ h𝔫 => Ideal.exists_map_localization_eq_span_of_flat_of_residueField_mvPolynomial R N (RingHom.ker φ) hfib 𝔫 h𝔫

  have hfin : {𝔫 : Ideal (MvPolynomial (Fin N) R) | 𝔫.IsMaximal ∧ RingHom.ker φ ≤ 𝔫}.Finite := by
    let 𝔪P : Ideal P := (IsLocalRing.maximalIdeal R).map (algebraMap R P)
    let 𝔪A : Ideal A := (IsLocalRing.maximalIdeal R).map (algebraMap R A)

    letI : Algebra κ (A ⧸ 𝔪A) := Ideal.Quotient.algebraQuotientMapQuotient
    haveI : IsScalarTower R κ (A ⧸ 𝔪A) := IsScalarTower.of_algebraMap_eq (fun r => rfl)
    haveI : Module.Finite κ (A ⧸ 𝔪A) := by
      have : Module.Finite R (A ⧸ 𝔪A) := inferInstance
      exact Module.Finite.of_restrictScalars_finite R κ (A ⧸ 𝔪A)
    haveI : IsArtinianRing (A ⧸ 𝔪A) := IsArtinianRing.of_finite κ (A ⧸ 𝔪A)
    let ψ : P →+* A ⧸ 𝔪A := (Ideal.Quotient.mk 𝔪A).comp (φ : P →+* A)
    have hψs : Function.Surjective ψ := Ideal.Quotient.mk_surjective.comp hφ
    have hkerψ : ∀ 𝔫 : Ideal P, 𝔫.IsMaximal → RingHom.ker φ ≤ 𝔫 → RingHom.ker ψ ≤ 𝔫 := by
      intro 𝔫 h𝔫 hJ𝔫 x hx
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hx

      have h𝔪 : 𝔪A = 𝔪P.map (φ : P →+* A) := by
        change (IsLocalRing.maximalIdeal R).map (algebraMap R A) = ((IsLocalRing.maximalIdeal R).map (algebraMap R P)).map (φ : P →+* A)
        rw [Ideal.map_map]; congr 1; ext r; exact (φ.commutes r).symm
      rw [h𝔪, Ideal.mem_map_iff_of_surjective (φ : P →+* A) hφ] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      have hmP : 𝔪P ≤ 𝔫 := Ideal.map_maximalIdeal_le_of_finite_quotient_ASM (RingHom.ker φ) 𝔫 hJ𝔫
      have : x - y ∈ RingHom.ker φ := by rw [RingHom.mem_ker, map_sub, sub_eq_zero]; exact hxy.symm
      simpa using Ideal.add_mem _ (hJ𝔫 this) (hmP hy)
    refine Set.Finite.of_finite_image (f := fun 𝔫 => 𝔫.map ψ) ?_ ?_
    · refine (IsArtinianRing.setOf_isMaximal_finite (A ⧸ 𝔪A)).subset ?_
      rintro _ ⟨𝔫, ⟨h𝔫, hJ𝔫⟩, rfl⟩
      haveI := h𝔫
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective ψ hψs h𝔫 with htop | hm
      · exfalso; apply h𝔫.ne_top
        have hc := Ideal.comap_map_of_surjective ψ hψs 𝔫
        rw [htop, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, sup_eq_left.2 (hkerψ 𝔫 h𝔫 hJ𝔫)] at hc
        exact hc.symm
      · exact hm
    · intro 𝔫₁ h₁ 𝔫₂ h₂ heq
      have e1 := Ideal.comap_map_of_surjective ψ hψs 𝔫₁
      have e2 := Ideal.comap_map_of_surjective ψ hψs 𝔫₂
      rw [← RingHom.ker_eq_comap_bot, sup_eq_left.2 (hkerψ 𝔫₁ h₁.1 h₁.2)] at e1
      rw [← RingHom.ker_eq_comap_bot, sup_eq_left.2 (hkerψ 𝔫₂ h₂.1 h₂.2)] at e2
      rw [← e1, ← e2]; exact congrArg _ heq

  obtain ⟨f, hfJ, hfloc⟩ := Ideal.exists_forall_map_localization_eq_span_of_finite_maximal (MvPolynomial (Fin N) R) (RingHom.ker φ) hfin N hloc

  have hIJ : Ideal.span (Set.range f) ≤ RingHom.ker φ := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hfJ i)
  have hloc' : ∀ (𝔫 : Ideal (MvPolynomial (Fin N) R)) [𝔫.IsMaximal], RingHom.ker φ ≤ 𝔫 →
      Ideal.map (algebraMap _ (Localization.AtPrime 𝔫)) (RingHom.ker φ) =
        Ideal.map (algebraMap _ (Localization.AtPrime 𝔫)) (Ideal.span (Set.range f)) := by
    intro 𝔫 _ h𝔫
    rw [hfloc 𝔫 h𝔫, Ideal.map_span, ← Set.range_comp]
    rfl
  obtain ⟨e', he', hJe'⟩ := Ideal.exists_isIdempotentElem_map_mk_eq_span_of_forall_map_localization_eq (MvPolynomial (Fin N) R) (Ideal.span (Set.range f)) (RingHom.ker φ) hIJ hloc'

  obtain ⟨f', ⟨ε⟩⟩ := MvPolynomial.exists_quotient_span_quotient_span_singleton_algEquiv_of_isIdempotentElem R N f e' he'

  have hJe'' : Ideal.span {e'} = (RingHom.ker φ).map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) := by
    rw [← hJe']; rfl
  exact ⟨N + 1, f', ⟨(ε.trans (Ideal.quotientEquivAlgOfEq R hJe'')).trans
    ((DoubleQuot.quotQuotEquivQuotOfLEₐ R hIJ).trans eJ)⟩⟩

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) (v : ℕ) :
    ∃ (m : ℕ) (f : Fin m → MvPolynomial (Fin m) (PadicAlgCl.ringOfIntegers p K)),
      Nonempty ((MvPolynomial (Fin m) (PadicAlgCl.ringOfIntegers p K) ⧸ Ideal.span (Set.range f)) ≃ₐ[PadicAlgCl.ringOfIntegers p K]
        G.level v) := by

  obtain ⟨_, hDVR, _⟩ := PadicAlgCl.ringOfIntegers.finite_and_isDiscreteValuationRing_and_isAdicComplete p K
  haveI := hDVR
  exact dlc_core (PadicAlgCl.ringOfIntegers p K) (G.level v)

end S_PDivisibleGroup_exists_square_presentation_level_of_ringOfIntegers
end P2MW
export P2MW.S_PDivisibleGroup_exists_square_presentation_level_of_ringOfIntegers (solution)
