-- Prove2me | solution 1 for PDivisibleGroup.exists_hasDimension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e896f374-8a1d-51a1-9354-03c2fb58843d

import Mathlib
import Definitions.Def_PDivisibleGroup_BaseChange
import Theorems.Thm_PDivisibleGroup_ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot
import Theorems.Thm_PDivisibleGroup_cotangentBaseChange_bijective
import Theorems.Thm_PDivisibleGroup_free_cotangent_of_isArtinianRing_of_pow_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_hasDimension
p2m_attr_erase "instance" "PDivisibleGroup.Points.instAddCommGroup PDivisibleGroup.Points.instInhabited PDivisibleGroup.Point.instCommGroup PDivisibleGroup.pointsDirectedSystem PDivisibleGroup.Points.instDistribMulAction PDivisibleGroup.Point.instCommMonoid TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra"
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "PDivisibleGroup.CartierDuality.mk.injEq PDivisibleGroup.CartierDuality.toDualEquiv_apply PDivisibleGroup.CartierDuality.mk.sizeOf_spec PDivisibleGroup.Points.smul_pointsMkAdd PDivisibleGroup.pointsMkAdd_pointInclLE PDivisibleGroup.Point.toAlgHom_ofAlgHom PDivisibleGroup.pointsMkAdd_pointIncl PDivisibleGroup.pointsMk_pointInclLE PDivisibleGroup.pointIncl_apply PDivisibleGroup.pointInclLE_self PDivisibleGroup.toAlgHom_pointMap PDivisibleGroup.Point.toConv_ofConv PDivisibleGroup.Hopf.antipodeAlgHom_apply PDivisibleGroup.Hopf.convCompMonoidHom_apply PDivisibleGroup.pointsMap_pointsMkAdd PDivisibleGroup.Point.ofAlgHom_toAlgHom PDivisibleGroup.pointsMk_pointIncl PDivisibleGroup.Point.ofConv_toConv TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false

open scoped TensorProduct

namespace PDivExistsDim

section PiQuot

variable {S : Type*} [CommRing S]

theorem smul_top_pi_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ι → Type*)
    [∀ k, AddCommGroup (M k)] [∀ k, Module S (M k)] (J : Ideal S) :
    (J • ⊤ : Submodule S (∀ k, M k)) = Submodule.pi Set.univ fun k => (J • ⊤ : Submodule S (M k)) := by
  apply le_antisymm
  · refine Submodule.smul_le.2 fun r hr x _ => ?_
    refine Submodule.mem_pi.2 fun k _ => ?_
    rw [Pi.smul_apply]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro x hx
    rw [Submodule.mem_pi] at hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun k _ => ?_
    have hk : Pi.single k (x k) = LinearMap.single S M k (x k) := rfl
    rw [hk]
    have hmem : LinearMap.single S M k (x k) ∈
        (J • ⊤ : Submodule S (M k)).map (LinearMap.single S M k) :=
      Submodule.mem_map_of_mem (hx k (Set.mem_univ k))
    rw [Submodule.map_smul''] at hmem
    exact Submodule.smul_mono le_rfl le_top hmem

noncomputable def piQuotEquiv (n : ℕ) (J : Ideal S) :
    ((Fin n → S) ⧸ (J • ⊤ : Submodule S (Fin n → S))) ≃ₗ[S] (Fin n → S ⧸ J) :=
  (Submodule.quotEquivOfEq _ _ (by
      rw [smul_top_pi_eq]
      congr 1
      funext k
      change J • (⊤ : Ideal S) = J
      rw [Ideal.smul_eq_mul, Ideal.mul_top])).trans
    (Submodule.quotientPi fun _ : Fin n => (J : Submodule S S))

noncomputable def piQuotQuotEquiv (n : ℕ) (I J : Ideal S) :
    ((Fin n → S ⧸ I) ⧸ (J • ⊤ : Submodule S (Fin n → S ⧸ I))) ≃ₗ[S] (Fin n → S ⧸ (I ⊔ J)) := by
  let f₀ : (S ⧸ I) →ₗ[S] S ⧸ (I ⊔ J) := (Ideal.Quotient.factorₐ S (le_sup_left : I ≤ I ⊔ J)).toLinearMap
  have hf₀ : Function.Surjective f₀ := Ideal.Quotient.factor_surjective (le_sup_left : I ≤ I ⊔ J)
  let f : (Fin n → S ⧸ I) →ₗ[S] (Fin n → S ⧸ (I ⊔ J)) := f₀.compLeft (Fin n)
  have hf : Function.Surjective f := fun y => by
    refine ⟨fun k => (hf₀ (y k)).choose, funext fun k => ?_⟩
    change f₀ _ = y k
    exact (hf₀ (y k)).choose_spec
  have hker₀ : LinearMap.ker f₀ = (J • ⊤ : Submodule S (S ⧸ I)) := by
    rw [Ideal.smul_top_eq_map]
    ext x
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem]
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ J) (Ideal.Quotient.mk I x) = 0 ↔ _
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.algebraMap_eq,
      ← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, sup_comm]
  have hker : LinearMap.ker f = (J • ⊤ : Submodule S (Fin n → S ⧸ I)) := by
    rw [smul_top_pi_eq]
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_pi]
    constructor
    · intro hx k _
      rw [← hker₀, LinearMap.mem_ker]
      exact congr_fun hx k
    · intro hx
      funext k
      have := hx k (Set.mem_univ k)
      rw [← hker₀, LinearMap.mem_ker] at this
      exact this
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective f hf)

theorem eq_of_linearEquiv_pi_quot {a b : ℕ} (J : Ideal S) (hJ : J ≠ ⊤)
    (e : (Fin a → S ⧸ J) ≃ₗ[S] (Fin b → S ⧸ J)) : a = b := by
  haveI : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ
  let e' : (Fin a → S ⧸ J) ≃ₗ[S ⧸ J] (Fin b → S ⧸ J) :=
    e.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  have h := e'.finrank_eq
  rwa [Module.finrank_fin_fun, Module.finrank_fin_fun] at h

end PiQuot

section KeyCA

variable {R : Type*} [CommRing R]

noncomputable def quotQuotSMulEquiv (M : Type*) [AddCommGroup M] [Module R M] (A B : Ideal R) :
    ((M ⧸ (A • ⊤ : Submodule R M)) ⧸ (B • ⊤ : Submodule R (M ⧸ (A • ⊤ : Submodule R M)))) ≃ₗ[R]
      M ⧸ ((A ⊔ B) • ⊤ : Submodule R M) :=
  (Submodule.quotEquivOfEq _ _ (by
      rw [Submodule.sup_smul, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq,
        Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ])).trans
    (Submodule.quotientQuotientEquivQuotient (A • ⊤ : Submodule R M) ((A ⊔ B) • ⊤ : Submodule R M)
      (Submodule.smul_mono_left le_sup_left))

variable [IsNoetherianRing R] [IsLocalRing R]

open IsLocalRing

noncomputable def residueEquivOfTruncation (M : Type*) [AddCommGroup M] [Module R M]
    {A Q : Ideal R} (hA : A ≤ maximalIdeal R) (hQ : Q ≤ maximalIdeal R) {r : ℕ}
    (e : (M ⧸ (A • ⊤ : Submodule R M)) ≃ₗ[R] (Fin r → R ⧸ (A ⊔ Q))) :
    (M ⧸ (maximalIdeal R • ⊤ : Submodule R M)) ≃ₗ[R] (Fin r → R ⧸ maximalIdeal R) := by
  have hAm : A ⊔ maximalIdeal R = maximalIdeal R := sup_eq_right.2 hA
  have hAQm : (A ⊔ Q) ⊔ maximalIdeal R = maximalIdeal R := sup_eq_right.2 (sup_le hA hQ)

  let e₁ : (M ⧸ (maximalIdeal R • ⊤ : Submodule R M)) ≃ₗ[R]
      M ⧸ ((A ⊔ maximalIdeal R) • ⊤ : Submodule R M) :=
    Submodule.quotEquivOfEq (maximalIdeal R • ⊤ : Submodule R M)
      ((A ⊔ maximalIdeal R) • ⊤ : Submodule R M) (by rw [hAm])
  let e₂ : (M ⧸ ((A ⊔ maximalIdeal R) • ⊤ : Submodule R M)) ≃ₗ[R]
      (M ⧸ (A • ⊤ : Submodule R M)) ⧸
        (maximalIdeal R • ⊤ : Submodule R (M ⧸ (A • ⊤ : Submodule R M))) :=
    (quotQuotSMulEquiv M A (maximalIdeal R)).symm
  have hmap : Submodule.map (e : (M ⧸ (A • ⊤ : Submodule R M)) →ₗ[R] (Fin r → R ⧸ (A ⊔ Q)))
      (maximalIdeal R • ⊤ : Submodule R (M ⧸ (A • ⊤ : Submodule R M))) =
        (maximalIdeal R • ⊤ : Submodule R (Fin r → R ⧸ (A ⊔ Q))) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  let e₃ : ((M ⧸ (A • ⊤ : Submodule R M)) ⧸
        (maximalIdeal R • ⊤ : Submodule R (M ⧸ (A • ⊤ : Submodule R M)))) ≃ₗ[R]
      (Fin r → R ⧸ (A ⊔ Q)) ⧸ (maximalIdeal R • ⊤ : Submodule R (Fin r → R ⧸ (A ⊔ Q))) :=
    Submodule.Quotient.equiv (maximalIdeal R • ⊤ : Submodule R (M ⧸ (A • ⊤ : Submodule R M)))
      (maximalIdeal R • ⊤ : Submodule R (Fin r → R ⧸ (A ⊔ Q))) e hmap
  let e₄ : ((Fin r → R ⧸ (A ⊔ Q)) ⧸ (maximalIdeal R • ⊤ : Submodule R (Fin r → R ⧸ (A ⊔ Q)))) ≃ₗ[R]
      (Fin r → R ⧸ ((A ⊔ Q) ⊔ maximalIdeal R)) :=
    piQuotQuotEquiv r (A ⊔ Q) (maximalIdeal R)
  let e₅ : (Fin r → R ⧸ ((A ⊔ Q) ⊔ maximalIdeal R)) ≃ₗ[R] (Fin r → R ⧸ maximalIdeal R) :=
    LinearEquiv.piCongrRight fun _ => (Ideal.quotientEquivAlgOfEq R hAQm).toLinearEquiv
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))

theorem exists_linearEquiv_pi_quot_of_truncations (q : R) (hq : q ∈ maximalIdeal R)
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hqM : ∀ x : M, q • x = 0)
    (hM : ∀ i : ℕ, 0 < i → ∃ r : ℕ, Nonempty ((M ⧸ (maximalIdeal R ^ i • ⊤ : Submodule R M)) ≃ₗ[R]
        (Fin r → R ⧸ (maximalIdeal R ^ i ⊔ Ideal.span {q})))) :
    ∃ n : ℕ, Nonempty (M ≃ₗ[R] (Fin n → R ⧸ Ideal.span {q})) := by
  classical
  set 𝔪 : Ideal R := maximalIdeal R with h𝔪
  set Q : Ideal R := Ideal.span {q} with hQdef
  have hQ : Q ≤ 𝔪 := by
    rw [hQdef, Ideal.span_le, Set.singleton_subset_iff]
    exact hq
  have hpow : ∀ {i : ℕ}, 0 < i → 𝔪 ^ i ≤ 𝔪 := fun hi => Ideal.pow_le_self (Nat.pos_iff_ne_zero.1 hi)
  have h𝔪top : 𝔪 ≠ ⊤ := Ideal.IsPrime.ne_top'

  obtain ⟨n, ⟨e₁⟩⟩ := hM 1 Nat.one_pos
  let f₁ : (M ⧸ (𝔪 • ⊤ : Submodule R M)) ≃ₗ[R] (Fin n → R ⧸ 𝔪) :=
    residueEquivOfTruncation M (hpow Nat.one_pos) hQ e₁

  have hrank : ∀ {i r : ℕ}, 0 < i →
      ((M ⧸ (𝔪 ^ i • ⊤ : Submodule R M)) ≃ₗ[R] (Fin r → R ⧸ (𝔪 ^ i ⊔ Q))) → r = n := by
    intro i r hi e
    exact eq_of_linearEquiv_pi_quot 𝔪 h𝔪top
      ((residueEquivOfTruncation M (hpow hi) hQ e).symm.trans f₁)

  have hxs : ∀ k : Fin n, ∃ x : M,
      (𝔪 • ⊤ : Submodule R M).mkQ x = f₁.symm (Pi.single k 1) := fun k =>
    Submodule.mkQ_surjective _ _
  choose xs hxs using hxs
  let φ : (Fin n → R) →ₗ[R] M := Fintype.linearCombination R xs
  have hφ : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, ← IsLocalRing.map_mkQ_eq_top,
      Submodule.map_span, ← Set.range_comp]
    have hcomp : ((𝔪 • ⊤ : Submodule R M).mkQ ∘ xs) = fun k => f₁.symm (Pi.single k 1) :=
      funext fun k => hxs k
    rw [hcomp]
    have hspan : Submodule.span R (Set.range fun k : Fin n => (Pi.single k 1 : Fin n → R ⧸ 𝔪)) = ⊤ := by
      rw [← Submodule.restrictScalars_span R (R ⧸ 𝔪) Ideal.Quotient.mk_surjective]
      have hb : (Set.range fun k : Fin n => (Pi.single k 1 : Fin n → R ⧸ 𝔪)) =
          Set.range (Pi.basisFun (R ⧸ 𝔪) (Fin n)) := by
        congr 1
        funext k
        rw [Pi.basisFun_apply]
      rw [hb, (Pi.basisFun (R ⧸ 𝔪) (Fin n)).span_eq]
      rfl
    have hrange : (Set.range fun k : Fin n => f₁.symm (Pi.single k 1)) =
        f₁.symm '' Set.range fun k : Fin n => (Pi.single k 1 : Fin n → R ⧸ 𝔪) := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, show (⇑f₁.symm '' Set.range fun k : Fin n => (Pi.single k 1 : Fin n → R ⧸ 𝔪)) =
        ⇑(f₁.symm : (Fin n → R ⧸ 𝔪) →ₗ[R] (M ⧸ (𝔪 • ⊤ : Submodule R M))) ''
          Set.range fun k : Fin n => (Pi.single k 1 : Fin n → R ⧸ 𝔪) from rfl,
      Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]

  let P : Submodule R (Fin n → R) := Q • ⊤
  have hPker : P ≤ LinearMap.ker φ := by
    refine Submodule.smul_le.2 fun a ha y _ => ?_
    rw [LinearMap.mem_ker, map_smul]
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [mul_smul, hqM, smul_zero]
  have hkerP : LinearMap.ker φ ≤ P := by
    intro y hy
    rw [LinearMap.mem_ker] at hy

    suffices h : P.mkQ y ∈ (⨅ i : ℕ, 𝔪 ^ i • ⊤ : Submodule R ((Fin n → R) ⧸ P)) by
      have hK : (⨅ i : ℕ, 𝔪 ^ i • ⊤ : Submodule R ((Fin n → R) ⧸ P)) = ⊥ :=
        Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (I := 𝔪) (M := (Fin n → R) ⧸ P) h𝔪top
      rw [hK, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
      exact h
    rw [Submodule.mem_iInf]
    intro i
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact Submodule.mem_top
    obtain ⟨r, ⟨e⟩⟩ := hM i hi
    obtain rfl : n = r := (hrank hi e).symm

    let J : Ideal R := 𝔪 ^ i ⊔ Q
    let θ : (Fin n → R) →ₗ[R] (Fin n → R ⧸ J) :=
      e.toLinearMap.comp ((𝔪 ^ i • ⊤ : Submodule R M).mkQ.comp φ)
    have hθ : Function.Surjective θ :=
      e.surjective.comp ((Submodule.mkQ_surjective _).comp hφ)
    let Qi : Submodule R (Fin n → R) := J • ⊤
    have hQi : Qi ≤ LinearMap.ker θ := by
      refine Submodule.smul_le.2 fun a ha z _ => ?_
      rw [LinearMap.mem_ker, map_smul]
      funext k
      rw [Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
    let θbar : ((Fin n → R) ⧸ Qi) →ₗ[R] (Fin n → R ⧸ J) := Qi.liftQ θ hQi
    have hθbar : Function.Surjective θbar := by
      rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]
      exact hθ
    have hθbar_inj : Function.Injective θbar := by
      let g : (Fin n → R ⧸ J) →ₗ[R] (Fin n → R ⧸ J) := θbar.comp (piQuotEquiv n J).symm.toLinearMap
      have hg : Function.Surjective g := hθbar.comp (piQuotEquiv n J).symm.surjective
      have hginj : Function.Injective g := OrzechProperty.injective_of_surjective_endomorphism g hg
      intro a b hab
      have h1 : g (piQuotEquiv n J a) = g (piQuotEquiv n J b) := by
        change θbar ((piQuotEquiv n J).symm (piQuotEquiv n J a)) =
          θbar ((piQuotEquiv n J).symm (piQuotEquiv n J b))
        rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
        exact hab
      exact (piQuotEquiv n J).injective (hginj h1)
    have hyQi : y ∈ Qi := by
      have h0 : θbar (Qi.mkQ y) = 0 := by
        change θ y = 0
        change e ((𝔪 ^ i • ⊤ : Submodule R M).mkQ (φ y)) = 0
        rw [hy, map_zero, map_zero]
      have h1 : Qi.mkQ y = 0 := hθbar_inj (by rw [h0, map_zero])
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    have hsplit : Qi = 𝔪 ^ i • ⊤ ⊔ P := Submodule.sup_smul _ _ _
    rw [hsplit] at hyQi
    have hmap : P.mkQ y ∈ (𝔪 ^ i • ⊤ ⊔ P : Submodule R (Fin n → R)).map P.mkQ :=
      Submodule.mem_map_of_mem hyQi
    rwa [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq, Submodule.map_smul'', Submodule.map_top,
      Submodule.range_mkQ] at hmap
  have hker : LinearMap.ker φ = P := le_antisymm hkerP hPker
  exact ⟨n, ⟨((LinearMap.quotKerEquivOfSurjective φ hφ).symm.trans
    (Submodule.quotEquivOfEq _ _ hker)).trans (piQuotEquiv n Q)⟩⟩

end KeyCA

section Tower

variable {S : Type} [CommRing S] {p h : ℕ} (G : PDivisibleGroup S p h)

theorem exists_iterCotangentMap (v d : ℕ) :
    ∃ f : G.Cotangent (v + d) →ₗ[S] G.Cotangent v,
      Function.Surjective f ∧
        LinearMap.ker f = Ideal.span {(p : S) ^ v} • (⊤ : Submodule S (G.Cotangent (v + d))) := by
  induction d with
  | zero =>
    refine ⟨LinearMap.id, Function.surjective_id, ?_⟩
    rw [LinearMap.ker_id]
    exact (G.ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot v).2.symm
  | succ d ih =>
    obtain ⟨f, hf, hker⟩ := ih
    refine ⟨f.comp (G.cotangentMap (v + d)), hf.comp (G.cotangentMap_surjective (v + d)), ?_⟩
    have hc := (G.ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot (v + d)).1
    have hmap : Ideal.span {(p : S) ^ v} • (⊤ : Submodule S (G.Cotangent (v + d))) =
        (Ideal.span {(p : S) ^ v} • (⊤ : Submodule S (G.Cotangent (v + d + 1)))).map
          (G.cotangentMap (v + d)) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 (G.cotangentMap_surjective _)]
    rw [LinearMap.ker_comp, hker, hmap, Submodule.comap_map_eq, hc, sup_eq_left]
    exact Submodule.smul_mono_left
      (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_add_right v d)))

theorem nonempty_quotSMul_equiv_cotangent (v d : ℕ) :
    Nonempty ((G.Cotangent (v + d) ⧸
        (Ideal.span {(p : S) ^ v} • (⊤ : Submodule S (G.Cotangent (v + d))))) ≃ₗ[S] G.Cotangent v) := by
  obtain ⟨f, hf, hker⟩ := exists_iterCotangentMap G v d
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective f hf)⟩

theorem finite_cotangent [IsNoetherianRing S] (w : ℕ) : Module.Finite S (G.Cotangent w) :=
  Module.Finite.of_surjective (((G.augIdeal w).toCotangent).restrictScalars S)
    (Ideal.toCotangent_surjective _)

theorem pow_smul_cotangent_eq_zero (v : ℕ) (x : G.Cotangent v) : ((p : S) ^ v) • x = 0 := by
  have h := (G.ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot v).2
  rw [← Submodule.mem_bot S, ← h]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

end Tower

section Level

variable {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p h)
  (S : Type) [CommRing S] [Algebra R S] [IsArtinianRing S] [IsLocalRing S]

theorem exists_baseChange_cotangent_equiv (v d : ℕ) (hS : (p : S) ^ (v + d) = 0) :
    ∃ r : ℕ, Nonempty ((S ⊗[R] G.Cotangent v) ≃ₗ[S] (Fin r → S ⧸ Ideal.span {(p : S) ^ v})) := by
  set GS : PDivisibleGroup S p h := G.baseChange S with hGS
  haveI : Module.Free S (GS.Cotangent (v + d)) :=
    GS.free_cotangent_of_isArtinianRing_of_pow_eq_zero hS
  haveI : Module.Finite S (GS.Cotangent (v + d)) := finite_cotangent GS (v + d)
  set r : ℕ := Module.finrank S (GS.Cotangent (v + d)) with hr
  let eF : GS.Cotangent (v + d) ≃ₗ[S] (Fin r → S) := (Module.finBasis S (GS.Cotangent (v + d))).equivFun
  obtain ⟨eT⟩ := nonempty_quotSMul_equiv_cotangent GS v d
  set P : Ideal S := Ideal.span {(p : S) ^ v} with hP
  have hmap : Submodule.map (eF : GS.Cotangent (v + d) →ₗ[S] (Fin r → S))
      (P • ⊤ : Submodule S (GS.Cotangent (v + d))) = (P • ⊤ : Submodule S (Fin r → S)) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  let e₃ : (GS.Cotangent (v + d) ⧸ (P • ⊤ : Submodule S (GS.Cotangent (v + d)))) ≃ₗ[S]
      (Fin r → S) ⧸ (P • ⊤ : Submodule S (Fin r → S)) :=
    Submodule.Quotient.equiv _ _ eF hmap
  let e₀ : (S ⊗[R] G.Cotangent v) ≃ₗ[S] GS.Cotangent v :=
    LinearEquiv.ofBijective (G.cotangentBaseChange S v) (G.cotangentBaseChange_bijective S v)
  exact ⟨r, ⟨e₀.trans (eT.symm.trans (e₃.trans (piQuotEquiv r P)))⟩⟩

end Level

section Main

variable {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {p h : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p h)

open IsLocalRing

theorem exists_truncation_equiv (hp : (p : R) ∈ maximalIdeal R) (v i : ℕ) (hi : 0 < i) :
    ∃ r : ℕ, Nonempty ((G.Cotangent v ⧸ (maximalIdeal R ^ i • ⊤ : Submodule R (G.Cotangent v))) ≃ₗ[R]
      (Fin r → R ⧸ (maximalIdeal R ^ i ⊔ Ideal.span {(p : R) ^ v}))) := by
  set 𝔞 : Ideal R := maximalIdeal R ^ i with h𝔞
  have h𝔞le : 𝔞 ≤ maximalIdeal R := Ideal.pow_le_self (Nat.pos_iff_ne_zero.1 hi)
  have h𝔞top : 𝔞 ≠ ⊤ := fun h => (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h ▸ h𝔞le))
  haveI : Nontrivial (R ⧸ 𝔞) := Ideal.Quotient.nontrivial_iff.2 h𝔞top
  haveI : IsLocalRing (R ⧸ 𝔞) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔞) Ideal.Quotient.mk_surjective
  haveI : IsArtinianRing (R ⧸ 𝔞) := by
    rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
    refine ⟨i, ?_⟩
    have hle : maximalIdeal (R ⧸ 𝔞) ≤ (maximalIdeal R).map (Ideal.Quotient.mk 𝔞) := by
      intro x hx
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine Ideal.mem_map_of_mem _ ?_
      by_contra hxm
      exact (IsLocalRing.mem_maximalIdeal _).1 hx
        ((IsLocalRing.notMem_maximalIdeal.1 hxm).map (Ideal.Quotient.mk 𝔞))
    rw [Submodule.zero_eq_bot, ← le_bot_iff]
    calc maximalIdeal (R ⧸ 𝔞) ^ i ≤ ((maximalIdeal R).map (Ideal.Quotient.mk 𝔞)) ^ i :=
          Ideal.pow_right_mono hle i
      _ = (maximalIdeal R ^ i).map (Ideal.Quotient.mk 𝔞) := (Ideal.map_pow _ _ i).symm
      _ = ⊥ := by rw [← h𝔞, Ideal.map_quotient_self]
  have hpS : ((p : R ⧸ 𝔞)) ^ (v + i) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk 𝔞), ← map_pow, Ideal.Quotient.eq_zero_iff_mem, pow_add]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hp i)
  obtain ⟨r, ⟨e⟩⟩ := exists_baseChange_cotangent_equiv G (R ⧸ 𝔞) v i hpS
  refine ⟨r, ⟨?_⟩⟩

  have hspan : Ideal.span {((p : R ⧸ 𝔞)) ^ v} =
      (Ideal.span {(p : R) ^ v}).map (Ideal.Quotient.mkₐ R 𝔞) := by
    rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]
  let e₁ : (G.Cotangent v ⧸ (𝔞 • ⊤ : Submodule R (G.Cotangent v))) ≃ₗ[R] (R ⧸ 𝔞) ⊗[R] G.Cotangent v :=
    (TensorProduct.quotTensorEquivQuotSMul (G.Cotangent v) 𝔞).symm
  let e₂ : ((R ⧸ 𝔞) ⊗[R] G.Cotangent v) ≃ₗ[R] (Fin r → (R ⧸ 𝔞) ⧸ Ideal.span {((p : R ⧸ 𝔞)) ^ v}) :=
    e.restrictScalars R
  let e₃ : ((R ⧸ 𝔞) ⧸ Ideal.span {((p : R ⧸ 𝔞)) ^ v}) ≃ₗ[R] R ⧸ (𝔞 ⊔ Ideal.span {(p : R) ^ v}) :=
    ((Ideal.quotientEquivAlgOfEq R hspan).trans
      (DoubleQuot.quotQuotEquivQuotSupₐ R 𝔞 (Ideal.span {(p : R) ^ v}))).toLinearEquiv
  exact e₁.trans (e₂.trans (LinearEquiv.piCongrRight fun _ => e₃))

theorem exists_cotangent_equiv (hp : (p : R) ∈ maximalIdeal R) (v : ℕ) (hv : 0 < v) :
    ∃ n : ℕ, Nonempty (G.Cotangent v ≃ₗ[R] (Fin n → R ⧸ Ideal.span {(p : R) ^ v})) := by
  haveI : Module.Finite R (G.Cotangent v) := finite_cotangent G v
  exact exists_linearEquiv_pi_quot_of_truncations ((p : R) ^ v) (Ideal.pow_mem_of_mem _ hp v hv)
    (G.Cotangent v) (pow_smul_cotangent_eq_zero G v) (exists_truncation_equiv G hp v)

omit [IsNoetherianRing R] [Fact p.Prime] in

theorem rank_eq_rank_succ (hp : (p : R) ∈ maximalIdeal R) (v : ℕ) (hv : 0 < v) {a b : ℕ}
    (ea : G.Cotangent v ≃ₗ[R] (Fin a → R ⧸ Ideal.span {(p : R) ^ v}))
    (eb : G.Cotangent (v + 1) ≃ₗ[R] (Fin b → R ⧸ Ideal.span {(p : R) ^ (v + 1)})) : a = b := by
  set P : Ideal R := Ideal.span {(p : R) ^ v} with hP
  set P' : Ideal R := Ideal.span {(p : R) ^ (v + 1)} with hP'
  have hPtop : P ≠ ⊤ := fun h => (maximalIdeal.isMaximal R).ne_top
    (top_le_iff.1 (h ▸ (Ideal.span_le.2 (Set.singleton_subset_iff.2 (Ideal.pow_mem_of_mem _ hp v hv)))))
  have hPP' : P' ⊔ P = P :=
    sup_eq_right.2 (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ v)))
  obtain ⟨eT⟩ := nonempty_quotSMul_equiv_cotangent G v 1
  have hmap : Submodule.map (eb : G.Cotangent (v + 1) →ₗ[R] (Fin b → R ⧸ P'))
      (P • ⊤ : Submodule R (G.Cotangent (v + 1))) = (P • ⊤ : Submodule R (Fin b → R ⧸ P')) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  let e₁ : (G.Cotangent (v + 1) ⧸ (P • ⊤ : Submodule R (G.Cotangent (v + 1)))) ≃ₗ[R]
      (Fin b → R ⧸ P') ⧸ (P • ⊤ : Submodule R (Fin b → R ⧸ P')) :=
    Submodule.Quotient.equiv _ _ eb hmap
  let e₂ : ((Fin b → R ⧸ P') ⧸ (P • ⊤ : Submodule R (Fin b → R ⧸ P'))) ≃ₗ[R] (Fin b → R ⧸ (P' ⊔ P)) :=
    piQuotQuotEquiv b P' P
  let e₃ : (Fin b → R ⧸ (P' ⊔ P)) ≃ₗ[R] (Fin b → R ⧸ P) :=
    LinearEquiv.piCongrRight fun _ => (Ideal.quotientEquivAlgOfEq R hPP').toLinearEquiv
  exact eq_of_linearEquiv_pi_quot P hPtop (ea.symm.trans (eT.symm.trans (e₁.trans (e₂.trans e₃))))

end Main

end PDivExistsDim

theorem solution
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {p h : ℕ} [Fact p.Prime] (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (G : PDivisibleGroup R p h) : ∃ n : ℕ, G.HasDimension n := by
  have H : ∀ v : ℕ, 0 < v →
      ∃ n : ℕ, Nonempty (G.Cotangent v ≃ₗ[R] (Fin n → R ⧸ Ideal.span {(p : R) ^ v})) :=
    fun v hv => PDivExistsDim.exists_cotangent_equiv G hp v hv
  choose nv hnv using H

  have hconst : ∀ d : ℕ, nv (d + 1) (Nat.succ_pos d) = nv 1 Nat.one_pos := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      rw [← ih]
      exact (PDivExistsDim.rank_eq_rank_succ G hp (d + 1) (Nat.succ_pos d)
        (hnv (d + 1) (Nat.succ_pos d)).some (hnv (d + 1 + 1) (Nat.succ_pos (d + 1))).some).symm
  refine ⟨nv 1 Nat.one_pos, fun v => ?_⟩
  rcases Nat.eq_zero_or_pos v with rfl | hv
  ·
    haveI : Subsingleton (G.Cotangent 0) := by
      refine subsingleton_of_forall_eq 0 fun x => ?_
      have hx := PDivExistsDim.pow_smul_cotangent_eq_zero G 0 x
      rwa [pow_zero, one_smul] at hx
    haveI := PDivisibleGroup.subsingleton_target_zero (R := R) (p := p) (nv 1 Nat.one_pos)
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  · obtain ⟨d, rfl⟩ : ∃ d, v = d + 1 := ⟨v - 1, (Nat.sub_add_cancel hv).symm⟩
    rw [← hconst d]
    exact hnv (d + 1) (Nat.succ_pos d)

end S_PDivisibleGroup_exists_hasDimension
end P2MW
export P2MW.S_PDivisibleGroup_exists_hasDimension (solution)
