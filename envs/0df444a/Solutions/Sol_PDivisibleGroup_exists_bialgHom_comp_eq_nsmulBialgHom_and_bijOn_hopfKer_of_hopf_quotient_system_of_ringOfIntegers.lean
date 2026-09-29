-- Prove2me | solution 1 for PDivisibleGroup.exists_bialgHom_comp_eq_nsmulBialgHom_and_bijOn_hopfKer_of_hopf_quotient_system_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/cfa64219-f1f5-531b-8a50-81326861c706

import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Tower
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete
import Theorems.Thm_Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Theorems.Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
import Theorems.Thm_PDivisibleGroup_finrank_eq_pow_mul_finrank_and_finrank_hopfKer_eq_of_hopf_quotient_system_of_ringOfIntegers
import Theorems.Thm_Subalgebra_exists_forall_le_eq_of_monotone_of_le_integralClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_bialgHom_comp_eq_nsmulBialgHom_and_bijOn_hopfKer_of_hopf_quotient_system_of_ringOfIntegers
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

universe u

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem Ws47.C2B.eq_zero_of_forall_algHom_apply_eq_zero
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (B v)] [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (B v)]
    (v : ℕ) (b : B v)
    (hb : ∀ f : B v →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p, f b = 0) : b = 0 := by
  classical

  obtain ⟨-, hdvr, -⟩ := PadicAlgCl.ringOfIntegers.finite_and_isDiscreteValuationRing_and_isAdicComplete p K
  haveI : IsDiscreteValuationRing ↥(PadicAlgCl.ringOfIntegers p K) := hdvr
  haveI : CharZero ↥(PadicAlgCl.ringOfIntegers p K) := by
    refine charZero_of_injective_algebraMap (R := ℤ_[p]) (A := ↥(PadicAlgCl.ringOfIntegers p K)) ?_
    have hcomp : Function.Injective ((algebraMap ↥(PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)).comp
        (algebraMap ℤ_[p] ↥(PadicAlgCl.ringOfIntegers p K))) := by
      rw [← IsScalarTower.algebraMap_eq ℤ_[p] ↥(PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)]
      exact PadicAlgCl.ringOfIntegers.algebraMap_injective_padicInt p
    rw [RingHom.coe_comp] at hcomp
    exact Function.Injective.of_comp hcomp

  letI : Algebra ↥(PadicAlgCl.ringOfIntegers p K) (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) := inferInstance
  haveI : IsFractionRing ↥(PadicAlgCl.ringOfIntegers p K) (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) := inferInstance
  haveI : CharZero (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective ↥(PadicAlgCl.ringOfIntegers p K) (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)))
  have hinj : Function.Injective (algebraMap ↥(PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) := Subtype.val_injective
  letI : Algebra (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) (PadicAlgCl p) := (IsFractionRing.lift hinj).toAlgebra
  haveI : IsScalarTower ↥(PadicAlgCl.ringOfIntegers p K) (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) (PadicAlgCl p) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra]
      exact (IsFractionRing.lift_algebraMap hinj x).symm

  haveI : NoZeroSMulDivisors ↥(PadicAlgCl.ringOfIntegers p K) (B v) := ⟨fun {c x} hcx => by
    rcases eq_or_ne c 0 with hc | hc
    · exact Or.inl hc
    · right
      let bB := Module.Free.chooseBasis ↥(PadicAlgCl.ringOfIntegers p K) (B v)
      have h1 := congrArg bB.repr hcx
      rw [map_smul, map_zero] at h1
      exact bB.repr.injective (by rw [map_zero]; exact (smul_eq_zero.1 h1).resolve_left hc)⟩
  haveI : Algebra.FiniteType (FractionRing ↥(PadicAlgCl.ringOfIntegers p K))
      ((FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) ⊗[↥(PadicAlgCl.ringOfIntegers p K)] B v) := Module.Finite.finiteType _
  haveI : IsReduced ((FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) ⊗[↥(PadicAlgCl.ringOfIntegers p K)] B v) :=
    HopfAlgebra.isReduced_of_finiteType_of_charZero (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) _
  exact Algebra.eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct
    (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) (PadicAlgCl p) b hb

namespace Ws47
namespace O

open scoped TensorProduct

universe uO vO wO

theorem bijective_baseChange_of_injective_of_finrank_eq
    {R : Type uO} [CommRing R] [IsDomain R] (K : Type vO) [Field K] [Algebra R K] [IsFractionRing R K]
    {M N : Type wO} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Free R M] [Module.Finite R M] [Module.Free R N] [Module.Finite R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) (hrk : Module.finrank R M = Module.finrank R N) :
    Function.Bijective (f.baseChange K) := by
  haveI : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  have hinj : Function.Injective (f.baseChange K) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K) f hf
  have hdim : Module.finrank K (K ⊗[R] M) = Module.finrank K (K ⊗[R] N) := by
    rw [Module.finrank_baseChange, Module.finrank_baseChange, hrk]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩

theorem surjective_of_algHom_range_eq_of_injective {R : Type*} [CommSemiring R]
    {A B S : Type*} [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring S] [Algebra R S]
    (e : A →ₐ[R] S) (e' : B →ₐ[R] S) (u : A →ₐ[R] B) (he' : Function.Injective e')
    (hcomm : e'.comp u = e) (hrange : e.range = e'.range) : Function.Surjective u := by
  intro b
  have hb : e' b ∈ e.range := by rw [hrange]; exact ⟨b, rfl⟩
  obtain ⟨a, ha⟩ := hb
  refine ⟨a, he' ?_⟩
  rw [← ha, ← hcomm]; rfl

section System

variable {R : Type uO} [CommRing R] [IsDomain R] (K : Type vO) [Field K] [Algebra R K] [IsFractionRing R K]
variable (D : ℕ → Type wO) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)] [∀ i, Module.Free R (D i)]
  [∀ i, Module.Finite R (D i)]
variable (u : ∀ i, D i →ₐ[R] D (i + 1))

noncomputable def U (hu : ∀ i, Function.Injective (u i))
    (hrk : ∀ i, Module.finrank R (D (i + 1)) = Module.finrank R (D i)) (i : ℕ) :
    K ⊗[R] D i ≃ₐ[K] K ⊗[R] D (i + 1) :=
  AlgEquiv.ofBijective (Algebra.TensorProduct.map (AlgHom.id K K) (u i))
    (bijective_baseChange_of_injective_of_finrank_eq K (u i).toLinearMap (hu i) (hrk i).symm)

theorem U_tmul (hu : ∀ i, Function.Injective (u i)) (hrk : ∀ i, Module.finrank R (D (i + 1)) = Module.finrank R (D i))
    (i : ℕ) (k : K) (d : D i) : U K D u hu hrk i (k ⊗ₜ d) = k ⊗ₜ u i d := rfl

noncomputable def E (hu : ∀ i, Function.Injective (u i))
    (hrk : ∀ i, Module.finrank R (D (i + 1)) = Module.finrank R (D i)) : ∀ i : ℕ, K ⊗[R] D i ≃ₐ[K] K ⊗[R] D 0
  | 0 => AlgEquiv.refl
  | i + 1 => (U K D u hu hrk i).symm.trans (E hu hrk i)

noncomputable def e (hu : ∀ i, Function.Injective (u i))
    (hrk : ∀ i, Module.finrank R (D (i + 1)) = Module.finrank R (D i)) (i : ℕ) : D i →ₐ[R] K ⊗[R] D 0 :=
  ((E K D u hu hrk i : K ⊗[R] D i →ₐ[K] K ⊗[R] D 0).restrictScalars R).comp Algebra.TensorProduct.includeRight

theorem e_apply (hu : ∀ i, Function.Injective (u i)) (hrk : ∀ i, Module.finrank R (D (i + 1)) = Module.finrank R (D i))
    (i : ℕ) (d : D i) : e K D u hu hrk i d = E K D u hu hrk i (1 ⊗ₜ d) := rfl

theorem e_comp_u (hu : ∀ i, Function.Injective (u i)) (hrk : ∀ i, Module.finrank R (D (i + 1)) = Module.finrank R (D i))
    (i : ℕ) : (e K D u hu hrk (i + 1)).comp (u i) = e K D u hu hrk i := by
  refine AlgHom.ext fun d => ?_
  show (E K D u hu hrk i) ((U K D u hu hrk i).symm ((1 : K) ⊗ₜ u i d)) = (E K D u hu hrk i) ((1 : K) ⊗ₜ d)
  congr 1
  rw [AlgEquiv.symm_apply_eq, U_tmul]

theorem e_injective (hu : ∀ i, Function.Injective (u i)) (hrk : ∀ i, Module.finrank R (D (i + 1)) = Module.finrank R (D i))
    (i : ℕ) : Function.Injective (e K D u hu hrk i) :=
  (E K D u hu hrk i).injective.comp
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))

theorem range_e_le (hu : ∀ i, Function.Injective (u i)) (hrk : ∀ i, Module.finrank R (D (i + 1)) = Module.finrank R (D i))
    (i : ℕ) : (e K D u hu hrk i).range ≤ integralClosure R (K ⊗[R] D 0) := by
  rintro x ⟨d, rfl⟩
  rw [mem_integralClosure_iff]
  haveI : Algebra.IsIntegral R (D i) := Algebra.IsIntegral.of_finite R (D i)
  exact IsIntegral.map (e K D u hu hrk i) (Algebra.IsIntegral.isIntegral d)

theorem monotone_range_e (hu : ∀ i, Function.Injective (u i))
    (hrk : ∀ i, Module.finrank R (D (i + 1)) = Module.finrank R (D i)) :
    Monotone fun i => (e K D u hu hrk i).range := by
  refine monotone_nat_of_le_succ fun i => ?_
  rintro x ⟨d, rfl⟩
  exact ⟨u i d, AlgHom.congr_fun (e_comp_u K D u hu hrk i) d⟩

theorem exists_embeddings (hu : ∀ i, Function.Injective (u i))
    (hrk : ∀ i, Module.finrank R (D (i + 1)) = Module.finrank R (D i)) :
    ∃ e : ∀ i, D i →ₐ[R] K ⊗[R] D 0,
      (∀ i, Function.Injective (e i)) ∧ (∀ i, (e (i + 1)).comp (u i) = e i) ∧
      (∀ i, (e i).range ≤ integralClosure R (K ⊗[R] D 0)) ∧ Monotone fun i => (e i).range :=
  ⟨e K D u hu hrk, e_injective K D u hu hrk, e_comp_u K D u hu hrk, range_e_le K D u hu hrk, monotone_range_e K D u hu hrk⟩

theorem exists_forall_le_bijective [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero K]
    [IsReduced (K ⊗[R] D 0)] (hu : ∀ i, Function.Injective (u i))
    (hrk : ∀ i, Module.finrank R (D (i + 1)) = Module.finrank R (D i)) :
    ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → Function.Bijective (u i) := by
  obtain ⟨i₀, hi₀⟩ := Subalgebra.exists_forall_le_eq_of_monotone_of_le_integralClosure R K (K ⊗[R] D 0)
    (fun i => (e K D u hu hrk i).range) (monotone_range_e K D u hu hrk) (range_e_le K D u hu hrk)
  refine ⟨i₀, fun i hi => ⟨hu i, ?_⟩⟩
  refine surjective_of_algHom_range_eq_of_injective (e K D u hu hrk i) (e K D u hu hrk (i + 1)) (u i)
    (e_injective K D u hu hrk (i + 1)) (e_comp_u K D u hu hrk i) ?_
  rw [hi₀ i hi, hi₀ (i + 1) (hi.trans (Nat.le_succ i))]

end System

end Ws47.O

namespace Ws47
namespace C2B

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

def PointsIff (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    (π : ∀ v, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] B v) : Prop :=
  ∀ (v : ℕ) (g : G.Point (PadicAlgCl p) v),
    (∃ g' : B v →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p,
        g'.comp (π v : G.level v →ₐ[PadicAlgCl.ringOfIntegers p K] B v) = PDivisibleGroup.Point.toAlgHom g) ↔
      ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul g) = (x : ℕ → G.Points (PadicAlgCl p)) v

theorem algHom_comp_injective_of_surjective {R A B' C : Type} [CommSemiring R] [Semiring A] [Semiring B'] [Semiring C]
    [Algebra R A] [Algebra R B'] [Algebra R C] (π : A →ₐ[R] B') (hπ : Function.Surjective π) {f g : B' →ₐ[R] C}
    (hfg : f.comp π = g.comp π) : f = g := by
  refine AlgHom.ext fun b => ?_
  obtain ⟨a, rfl⟩ := hπ b
  exact DFunLike.congr_fun hfg a

theorem nsmulAlgHom_eq_zero_of_mem_ker
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (B v)] [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (B v)]
    (π : ∀ v, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] B v) (t : ∀ v, B (v + 1) →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    (hπ : ∀ v, Function.Surjective (π v)) (ht : ∀ v, Function.Surjective (t v))
    (hπt : ∀ v, (π v).comp (G.transition v) = (t v).comp (π (v + 1)))
    (hpts : PointsIff p K G M B π) (j : ℕ) (b : B (j + 1)) (hb : t j b = 0) :
    PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p b = 0 := by
  classical
  refine eq_zero_of_forall_algHom_apply_eq_zero p K B (j + 1) _ (fun f => ?_)

  let P : G.Point (PadicAlgCl p) (j + 1) :=
    PDivisibleGroup.Point.ofAlgHom (f.comp (π (j + 1) : G.level (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 1)))
  have hPdef : PDivisibleGroup.Point.toAlgHom P = f.comp (π (j + 1) : G.level (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 1)) := rfl
  obtain ⟨x, hxM, hx⟩ := (hpts (j + 1) P).1 ⟨f, hPdef.symm⟩

  have hPp : (P ^ p) ^ (p ^ j) = 1 := by
    rw [← pow_mul, ← pow_succ', PDivisibleGroup.Point.pow_card_eq_one]
  obtain ⟨Q, hQ⟩ := G.exists_pointIncl_eq_of_pow_eq_one j (P ^ p) hPp

  have hQx : G.pointsMkAdd (PadicAlgCl p) j (Additive.ofMul Q) = (x : ℕ → G.Points (PadicAlgCl p)) j := by
    rw [← G.pointsMkAdd_pointIncl j Q, hQ, ofMul_pow, map_nsmul, hx, ← natCast_zsmul]
    exact TateModule.compat x j
  obtain ⟨g', hg'⟩ := (hpts j Q).2 ⟨x, hxM, hQx⟩

  have h1 : PDivisibleGroup.Point.toAlgHom (P ^ p) =
      (f.comp (π (j + 1) : G.level (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 1))).comp
        (PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (j + 1)) p) := by
    show WithConv.ofConv ((WithConv.toConv (f.comp (π (j + 1) : G.level (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 1)))) ^ p) = _
    rw [PDivisibleGroup.Hopf.toConv_pow_eq_toConv_comp_nsmulAlgHom]
  have h2 : PDivisibleGroup.Point.toAlgHom (P ^ p) =
      (g'.comp (t j : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B j)).comp
        (π (j + 1) : G.level (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 1)) := by
    rw [← hQ, G.toAlgHom_pointIncl, ← hg', AlgHom.comp_assoc, AlgHom.comp_assoc]
    congr 1
    have := congrArg (fun φ : G.level (j + 1) →ₐc[PadicAlgCl.ringOfIntegers p K] B j => (φ : G.level (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B j)) (hπt j)
    exact this

  have h3 : f.comp (PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p) =
      g'.comp (t j : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B j) := by
    refine algHom_comp_injective_of_surjective (π (j + 1) : G.level (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 1)) (hπ (j + 1)) ?_
    rw [AlgHom.comp_assoc, PDivisibleGroup.Hopf.nsmulAlgHom_comp_bialgHom (π (j + 1)) p, ← AlgHom.comp_assoc, ← h1, h2]
  have := DFunLike.congr_fun h3 b
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at this
  rw [this]
  show g' (t j b) = 0
  rw [hb, map_zero]

theorem algHom_comp_injective_of_surjective' {R A B' C : Type} [CommSemiring R] [Semiring A] [Semiring B'] [Semiring C]
    [Algebra R A] [Algebra R B'] [Algebra R C] (π : A →ₐ[R] B') (hπ : Function.Surjective π) {f g : B' →ₐ[R] C}
    (hfg : f.comp π = g.comp π) : f = g := by
  refine AlgHom.ext fun b => ?_
  obtain ⟨a, rfl⟩ := hπ b
  exact DFunLike.congr_fun hfg a

theorem exists_rep_of_nsmul_eq_zero' {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    {L : Type} [Field L] [Algebra R L] (v : ℕ) (z : G.Points L) (hz : ((p ^ v : ℕ) : ℤ) • z = 0) :
    ∃ g : G.Point L v, G.pointsMkAdd L v (Additive.ofMul g) = z := by
  obtain ⟨w, x, rfl⟩ := PDivisibleGroup.Points.exists_mkAdd G z
  rcases le_total w v with hwv | hvw
  · exact ⟨G.pointInclLE L hwv x, G.pointsMkAdd_pointInclLE hwv x⟩
  · have hx : x ^ (p ^ v) = 1 := by
      refine (G.pointsMkAdd_eq_pointsMkAdd_iff (L := L) _ _).1 ?_
      rw [ofMul_pow, map_nsmul, ofMul_one, map_zero, ← natCast_zsmul]
      exact hz
    obtain ⟨g, hg⟩ := G.exists_pointInclLE_eq_of_pow_eq_one hvw x hx
    exact ⟨g, by rw [← hg, G.pointsMkAdd_pointInclLE]⟩

theorem exists_comp_m_eq
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (B v)] [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (B v)]
    (π : ∀ v, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] B v) (t : ∀ v, B (v + 1) →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (hπ : ∀ v, Function.Surjective (π v))
    (hπt : ∀ v, (π v).comp (G.transition v) = (t v).comp (π (v + 1)))
    (hpts : PointsIff p K G M B π) (m : ∀ j, B j →ₐc[PadicAlgCl.ringOfIntegers p K] B (j + 1))
    (hmt : ∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p)
    (j : ℕ) (f : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) :
    ∃ f' : B (j + 2) →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p,
      f'.comp (m (j + 1) : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 2)) = f := by
  classical

  let y : G.Point (PadicAlgCl p) (j + 1) :=
    PDivisibleGroup.Point.ofAlgHom (f.comp (π (j + 1) : G.level (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 1)))
  have hydef : PDivisibleGroup.Point.toAlgHom y =
      f.comp (π (j + 1) : G.level (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 1)) := rfl
  obtain ⟨x, hxM, hx⟩ := (hpts (j + 1) y).1 ⟨f, hydef.symm⟩

  obtain ⟨y', hy'⟩ := exists_rep_of_nsmul_eq_zero' G (j + 2) _ (TateModule.torsion x (j + 2))
  obtain ⟨f', hf'⟩ := (hpts (j + 2) y').2 ⟨x, hxM, hy'⟩
  refine ⟨f', ?_⟩

  have hpow : y' ^ p = G.pointIncl (PadicAlgCl p) (j + 1) y := by
    refine (G.pointsMkAdd_eq_pointsMkAdd_iff (L := PadicAlgCl p) _ _).1 ?_
    rw [ofMul_pow, map_nsmul, hy', G.pointsMkAdd_pointIncl, hx, ← natCast_zsmul]
    exact TateModule.compat x (j + 1)

  refine algHom_comp_injective_of_surjective' (π (j + 1) : G.level (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 1))
    (hπ (j + 1)) ?_
  refine algHom_comp_injective_of_surjective' (G.transitionAlgHom (j + 1)) (G.transitionAlgHom_surjective (j + 1)) ?_

  rw [← hydef, ← G.toAlgHom_pointIncl, ← hpow]

  have hsq : ((π (j + 1) : G.level (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 1))).comp (G.transitionAlgHom (j + 1))
      = ((t (j + 1) : B (j + 2) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 1))).comp
          (π (j + 2) : G.level (j + 2) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 2)) :=
    congrArg (fun φ : G.level (j + 2) →ₐc[PadicAlgCl.ringOfIntegers p K] B (j + 1) =>
      (φ : G.level (j + 2) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 1))) (hπt (j + 1))
  have hmt' : ((m (j + 1) : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 2))).comp
      (t (j + 1) : B (j + 2) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 1))
      = PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 2)) p := by
    rw [← PDivisibleGroup.Hopf.toAlgHom_nsmulBialgHom]
    exact congrArg (fun φ : B (j + 2) →ₐc[PadicAlgCl.ringOfIntegers p K] B (j + 2) =>
      (φ : B (j + 2) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 2))) (hmt (j + 1))
  rw [AlgHom.comp_assoc, AlgHom.comp_assoc, hsq]
  have e1 : ((m (j + 1) : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 2))).comp
      (((t (j + 1) : B (j + 2) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 1))).comp
        (π (j + 2) : G.level (j + 2) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 2)))
      = (PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 2)) p).comp
        (π (j + 2) : G.level (j + 2) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 2)) := by
    rw [← AlgHom.comp_assoc, hmt']
  rw [e1, PDivisibleGroup.Hopf.nsmulAlgHom_comp_bialgHom (π (j + 2)) p, ← AlgHom.comp_assoc, hf']
  show _ = PDivisibleGroup.Point.toAlgHom (y' ^ p)
  show _ = WithConv.ofConv ((WithConv.toConv (PDivisibleGroup.Point.toAlgHom y')) ^ p)
  rw [PDivisibleGroup.Hopf.toConv_pow_eq_toConv_comp_nsmulAlgHom]

theorem injective_m_succ
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (B v)] [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (B v)]
    (π : ∀ v, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] B v) (t : ∀ v, B (v + 1) →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (hπ : ∀ v, Function.Surjective (π v))
    (hπt : ∀ v, (π v).comp (G.transition v) = (t v).comp (π (v + 1)))
    (hpts : PointsIff p K G M B π) (m : ∀ j, B j →ₐc[PadicAlgCl.ringOfIntegers p K] B (j + 1))
    (hmt : ∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p)
    (j : ℕ) : Function.Injective (m (j + 1)) := by
  intro a b hab
  rw [← sub_eq_zero] at hab ⊢
  rw [← map_sub] at hab
  refine Ws47.C2B.eq_zero_of_forall_algHom_apply_eq_zero p K B (j + 1) _ fun f => ?_
  obtain ⟨f', hf'⟩ := exists_comp_m_eq p K G M B π t hπ hπt hpts m hmt j f
  rw [← hf', AlgHom.comp_apply]
  show f' (m (j + 1) (a - b)) = 0
  rw [hab, map_zero]

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

section
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
  {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
  (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
  (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
  [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
  [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (B v)] [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (B v)]
  (π : ∀ v, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] B v) (t : ∀ v, B (v + 1) →ₐc[PadicAlgCl.ringOfIntegers p K] B v)

theorem exists_comp_eq_nsmulBialgHom
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    (hπ : ∀ v, Function.Surjective (π v)) (ht : ∀ v, Function.Surjective (t v))
    (hπt : ∀ v, (π v).comp (G.transition v) = (t v).comp (π (v + 1)))
    (hpts : PointsIff p K G M B π) :
    ∃ m : ∀ j, B j →ₐc[PadicAlgCl.ringOfIntegers p K] B (j + 1),
      (∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p) ∧
      (∀ j, (t j).comp (m j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B j) p) := by
  have hle : ∀ j, RingHom.ker (t j : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B j) ≤
      RingHom.ker (PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p) := by
    intro j b hb
    rw [RingHom.mem_ker] at hb ⊢
    exact nsmulAlgHom_eq_zero_of_mem_ker p K G M B π t hMsat hπ ht hπt hpts j b hb
  let ma : ∀ j, B j →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 1) := fun j =>
    AlgHom.liftOfSurjective (t j : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B j) (ht j) (PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p) (hle j)
  have hma : ∀ j, (ma j).comp (t j : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B j) = PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p :=
    fun j => AlgHom.liftOfSurjective_comp _ _ _ _
  have hma' : ∀ j (a : B (j + 1)), ma j (t j a) = PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p a :=
    fun j a => DFunLike.congr_fun (hma j) a
  have hcounit : ∀ j, (Bialgebra.counitAlgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1))).comp (ma j) = Bialgebra.counitAlgHom (PadicAlgCl.ringOfIntegers p K) (B j) := by
    intro j
    apply AlgHom.ext
    intro b
    obtain ⟨a, rfl⟩ := ht j b
    rw [AlgHom.comp_apply, hma', Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
      ← PDivisibleGroup.Hopf.nsmulBialgHom_apply, PDivisibleGroup.Hopf.counit_bialgHom_apply,
      PDivisibleGroup.Hopf.counit_bialgHom_apply]
  have hcomul : ∀ j, (Algebra.TensorProduct.map (ma j) (ma j)).comp (Bialgebra.comulAlgHom (PadicAlgCl.ringOfIntegers p K) (B j)) =
      (Bialgebra.comulAlgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1))).comp (ma j) := by
    intro j
    apply AlgHom.ext
    intro b
    obtain ⟨a, rfl⟩ := ht j b
    have h1 : Bialgebra.comulAlgHom (PadicAlgCl.ringOfIntegers p K) (B j) ((t j : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B j) a) =
        Algebra.TensorProduct.map (t j : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B j) (t j : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B j)
          (Bialgebra.comulAlgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) a) :=
      (DFunLike.congr_fun (BialgHom.map_comp_comulAlgHom (t j)) a).symm
    have h2 := DFunLike.congr_fun (PDivisibleGroup.Hopf.map_comp_comulAlgHom_nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p) a
    simp only [AlgHom.comp_apply] at h2 ⊢
    erw [h1]
    rw [← AlgHom.comp_apply (Algebra.TensorProduct.map (ma j) (ma j)), ← Algebra.TensorProduct.map_comp, hma, h2, ← hma' j a]
  refine ⟨fun j => BialgHom.ofAlgHom (ma j) (hcounit j) (hcomul j), fun j => ?_, fun j => ?_⟩
  · apply DFunLike.ext
    intro a
    show ma j (t j a) = _
    rw [hma', PDivisibleGroup.Hopf.nsmulBialgHom_apply]
  · apply DFunLike.ext
    intro b
    obtain ⟨a, rfl⟩ := ht j b
    show t j (ma j (t j a)) = _
    rw [hma', PDivisibleGroup.Hopf.nsmulBialgHom_apply]
    exact (PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply (t j) p a).symm

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem apply_eq_algebraMap_counit_of_mem_hopfKer (j : ℕ) (d : B (j + 1)) (hd : d ∈ HopfAlgebra.hopfKer (t j)) :
    t j d = algebraMap (PadicAlgCl.ringOfIntegers p K) (B j) (Coalgebra.counit d) := by
  have hd' : HopfAlgebra.coaction (t j) d = d ⊗ₜ[PadicAlgCl.ringOfIntegers p K] 1 := hd

  let G₀ : B (j + 1) ⊗[PadicAlgCl.ringOfIntegers p K] B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 1) :=
    Algebra.TensorProduct.lift ((Algebra.ofId (PadicAlgCl.ringOfIntegers p K) (B (j + 1))).comp (Bialgebra.counitAlgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1))))
      (AlgHom.id (PadicAlgCl.ringOfIntegers p K) (B (j + 1))) (fun _ _ => Commute.all _ _)
  have hG₀lin : G₀.toLinearMap = (TensorProduct.lid (PadicAlgCl.ringOfIntegers p K) (B (j + 1))).toLinearMap ∘ₗ
      (Coalgebra.counit (R := PadicAlgCl.ringOfIntegers p K) (A := B (j + 1))).rTensor (B (j + 1)) := by
    apply TensorProduct.ext'
    intro x y
    simp only [G₀, AlgHom.toLinearMap_apply, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Algebra.ofId_apply,
      AlgHom.id_apply, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul,
      Algebra.smul_def]
    rfl
  have hG₀ : G₀ (Coalgebra.comul (R := PadicAlgCl.ringOfIntegers p K) d) = d := by
    have := LinearMap.congr_fun hG₀lin (Coalgebra.comul (R := PadicAlgCl.ringOfIntegers p K) d)
    rw [AlgHom.toLinearMap_apply] at this
    rw [this, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, one_smul]

  let E : B (j + 1) ⊗[PadicAlgCl.ringOfIntegers p K] B j →ₐ[PadicAlgCl.ringOfIntegers p K] B j :=
    Algebra.TensorProduct.lift ((Algebra.ofId (PadicAlgCl.ringOfIntegers p K) (B j)).comp (Bialgebra.counitAlgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1))))
      (AlgHom.id (PadicAlgCl.ringOfIntegers p K) (B j)) (fun _ _ => Commute.all _ _)
  have hz : ∀ z : B (j + 1) ⊗[PadicAlgCl.ringOfIntegers p K] B (j + 1),
      E (Algebra.TensorProduct.map (AlgHom.id (PadicAlgCl.ringOfIntegers p K) (B (j + 1))) (t j : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B j) z) = t j (G₀ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul]
      show E (x ⊗ₜ[PadicAlgCl.ringOfIntegers p K] t j y) = t j (G₀ (x ⊗ₜ[PadicAlgCl.ringOfIntegers p K] y))
      simp only [E, G₀, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.id_apply, map_mul]
      congr 1
      exact (AlgHomClass.commutes (t j) _).symm
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have key := congrArg E hd'
  have hE1 : E (d ⊗ₜ[PadicAlgCl.ringOfIntegers p K] 1) = algebraMap (PadicAlgCl.ringOfIntegers p K) (B j) (Coalgebra.counit d) := by
    simp [E, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
  have hE2 : E (HopfAlgebra.coaction (t j) d) = t j d := by
    rw [HopfAlgebra.coaction_apply, hz, hG₀]
  rw [← hE2, key, hE1]

theorem nsmulAlgHom_eq_counit_of_mem_hopfKer (m : ∀ j, B j →ₐc[PadicAlgCl.ringOfIntegers p K] B (j + 1))
    (hmt : ∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p)
    (j : ℕ) (d : B (j + 1)) (hd : d ∈ HopfAlgebra.hopfKer (t j)) :
    PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p d =
      algebraMap (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) (Coalgebra.counit d) := by
  have h := DFunLike.congr_fun (hmt j) d
  simp only [BialgHom.comp_apply, PDivisibleGroup.Hopf.nsmulBialgHom_apply] at h
  rw [← h, apply_eq_algebraMap_counit_of_mem_hopfKer p K B t j d hd]
  exact AlgHomClass.commutes (m j) _

theorem mapsTo_hopfKer (m : ∀ j, B j →ₐc[PadicAlgCl.ringOfIntegers p K] B (j + 1))
    (hmt : ∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p)
    (htm : ∀ j, (t j).comp (m j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B j) p) (j : ℕ) :
    Set.MapsTo (m (j + 1)) (HopfAlgebra.hopfKer (t j) : Set (B (j + 1)))
      (HopfAlgebra.hopfKer (t (j + 1)) : Set (B (j + 2))) := by
  intro d hd
  have hd' : HopfAlgebra.coaction (t j) d = d ⊗ₜ[PadicAlgCl.ringOfIntegers p K] 1 := hd
  show HopfAlgebra.coaction (t (j + 1)) (m (j + 1) d) = m (j + 1) d ⊗ₜ[PadicAlgCl.ringOfIntegers p K] 1

  have hcomul : Coalgebra.comul (R := PadicAlgCl.ringOfIntegers p K) (m (j + 1) d) =
      Algebra.TensorProduct.map (m (j + 1) : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 2)) (m (j + 1) : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 2))
        (Coalgebra.comul (R := PadicAlgCl.ringOfIntegers p K) d) := by
    exact (DFunLike.congr_fun (BialgHom.map_comp_comulAlgHom (m (j + 1))) d).symm

  have hfac : (t (j + 1) : B (j + 2) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 1)).comp (m (j + 1) : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 2)) =
      (m j : B j →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 1)).comp (t j : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B j) := by
    ext x
    show t (j + 1) (m (j + 1) x) = m j (t j x)
    have h1 := DFunLike.congr_fun (htm (j + 1)) x
    have h2 := DFunLike.congr_fun (hmt j) x
    simp only [BialgHom.comp_apply, PDivisibleGroup.Hopf.nsmulBialgHom_apply] at h1 h2
    rw [h1, h2]
  rw [HopfAlgebra.coaction_apply, hcomul, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp, hfac,
    ← AlgHom.comp_id (m (j + 1) : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 2)), Algebra.TensorProduct.map_comp, AlgHom.comp_apply]
  have : Algebra.TensorProduct.map (AlgHom.id (PadicAlgCl.ringOfIntegers p K) (B (j + 1))) (t j : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B j)
      (Coalgebra.comul (R := PadicAlgCl.ringOfIntegers p K) d) = d ⊗ₜ[PadicAlgCl.ringOfIntegers p K] 1 := hd'
  rw [this, Algebra.TensorProduct.map_tmul, map_one]
  rfl

noncomputable def uAlg (m : ∀ j, B j →ₐc[PadicAlgCl.ringOfIntegers p K] B (j + 1))
    (hmt : ∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p)
    (htm : ∀ j, (t j).comp (m j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B j) p) (j : ℕ) :
    ↥(HopfAlgebra.hopfKer (t j)) →ₐ[PadicAlgCl.ringOfIntegers p K] ↥(HopfAlgebra.hopfKer (t (j + 1))) :=
  (((m (j + 1) : B (j + 1) →ₐ[PadicAlgCl.ringOfIntegers p K] B (j + 2)).comp (HopfAlgebra.hopfKer (t j)).val).codRestrict
    (HopfAlgebra.hopfKer (t (j + 1))) (fun d => mapsTo_hopfKer p K B t m hmt htm j d.2))

theorem coe_uAlg (m : ∀ j, B j →ₐc[PadicAlgCl.ringOfIntegers p K] B (j + 1))
    (hmt : ∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p)
    (htm : ∀ j, (t j).comp (m j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B j) p) (j : ℕ)
    (d : ↥(HopfAlgebra.hopfKer (t j))) :
    ((uAlg p K B t m hmt htm j d : ↥(HopfAlgebra.hopfKer (t (j + 1)))) : B (j + 2)) = m (j + 1) (d : B (j + 1)) := rfl

theorem bijOn_of_bijective_uAlg (m : ∀ j, B j →ₐc[PadicAlgCl.ringOfIntegers p K] B (j + 1))
    (hmt : ∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p)
    (htm : ∀ j, (t j).comp (m j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B j) p) (j : ℕ)
    (hbij : Function.Bijective (uAlg p K B t m hmt htm j)) :
    Set.BijOn (m (j + 1)) (HopfAlgebra.hopfKer (t j) : Set (B (j + 1)))
      (HopfAlgebra.hopfKer (t (j + 1)) : Set (B (j + 2))) := by
  refine ⟨mapsTo_hopfKer p K B t m hmt htm j, fun x hx y hy hxy => ?_, fun z hz => ?_⟩
  · have := hbij.1 (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Subtype.ext (by simpa [coe_uAlg] using hxy))
    exact congrArg Subtype.val this
  · obtain ⟨d, hd⟩ := hbij.2 ⟨z, hz⟩
    exact ⟨d, d.2, by simpa [coe_uAlg] using congrArg Subtype.val hd⟩

theorem injective_uAlg
    (hMstab : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) (x : TateModule p (G.Points (PadicAlgCl p))),
      x ∈ M → G.tateModuleRep (PadicAlgCl p) τ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    (hπ : ∀ v, Function.Surjective (π v)) (ht : ∀ v, Function.Surjective (t v))
    (hπt : ∀ v, (π v).comp (G.transition v) = (t v).comp (π (v + 1)))
    (hpts : PointsIff p K G M B π) (m : ∀ j, B j →ₐc[PadicAlgCl.ringOfIntegers p K] B (j + 1))
    (hmt : ∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p)
    (htm : ∀ j, (t j).comp (m j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B j) p) (j : ℕ) :
    Function.Injective (uAlg p K B t m hmt htm j) := by
  intro x y hxy
  apply Subtype.ext
  apply injective_m_succ p K G M B π t hπ hπt hpts m hmt j
  have := congrArg Subtype.val hxy
  simpa [coe_uAlg] using this

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_forall_le_bijOn_hopfKer
    (hMstab : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) (x : TateModule p (G.Points (PadicAlgCl p))),
      x ∈ M → G.tateModuleRep (PadicAlgCl p) τ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    (hπ : ∀ v, Function.Surjective (π v)) (ht : ∀ v, Function.Surjective (t v))
    (hπt : ∀ v, (π v).comp (G.transition v) = (t v).comp (π (v + 1)))
    (hpts : PointsIff p K G M B π) (m : ∀ j, B j →ₐc[PadicAlgCl.ringOfIntegers p K] B (j + 1))
    (hmt : ∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p)
    (htm : ∀ j, (t j).comp (m j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B j) p) :
    ∃ i₀ : ℕ, ∀ i, i₀ ≤ i →
      Set.BijOn (m (i + 1)) (HopfAlgebra.hopfKer (t i) : Set (B (i + 1)))
        (HopfAlgebra.hopfKer (t (i + 1)) : Set (B (i + 2))) := by
  classical

  obtain ⟨-, hdvr, -⟩ := PadicAlgCl.ringOfIntegers.finite_and_isDiscreteValuationRing_and_isAdicComplete p K
  haveI : IsDiscreteValuationRing ↥(PadicAlgCl.ringOfIntegers p K) := hdvr
  haveI : CharZero ↥(PadicAlgCl.ringOfIntegers p K) := by
    refine charZero_of_injective_algebraMap (R := ℤ_[p]) (A := ↥(PadicAlgCl.ringOfIntegers p K)) ?_
    have hcomp : Function.Injective ((algebraMap ↥(PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)).comp (algebraMap ℤ_[p] ↥(PadicAlgCl.ringOfIntegers p K))) := by
      rw [← IsScalarTower.algebraMap_eq ℤ_[p] ↥(PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)]
      exact PadicAlgCl.ringOfIntegers.algebraMap_injective_padicInt p
    rw [RingHom.coe_comp] at hcomp
    exact Function.Injective.of_comp hcomp
  haveI : CharZero (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective ↥(PadicAlgCl.ringOfIntegers p K) (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)))

  haveI hfin : ∀ i, Module.Finite ↥(PadicAlgCl.ringOfIntegers p K) ↥(HopfAlgebra.hopfKer (t i)) := fun i =>
    (HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective (t i) (ht i)).2.1
  haveI hproj : ∀ i, Module.Projective ↥(PadicAlgCl.ringOfIntegers p K) ↥(HopfAlgebra.hopfKer (t i)) := fun i =>
    (HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective (t i) (ht i)).2.2.1
  haveI hfree : ∀ i, Module.Free ↥(PadicAlgCl.ringOfIntegers p K) ↥(HopfAlgebra.hopfKer (t i)) := fun i => Module.free_of_flat_of_isLocalRing

  haveI : Algebra.FiniteType (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) ((FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) ⊗[↥(PadicAlgCl.ringOfIntegers p K)] B 1) := Module.Finite.finiteType _
  haveI : IsReduced ((FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) ⊗[↥(PadicAlgCl.ringOfIntegers p K)] B 1) :=
    HopfAlgebra.isReduced_of_finiteType_of_charZero (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) _
  haveI : IsReduced ((FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) ⊗[↥(PadicAlgCl.ringOfIntegers p K)] ↥(HopfAlgebra.hopfKer (t 0))) := by
    refine isReduced_of_injective
      (Algebra.TensorProduct.map (AlgHom.id (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) (FractionRing ↥(PadicAlgCl.ringOfIntegers p K))) (HopfAlgebra.hopfKer (t 0)).val) ?_
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) (HopfAlgebra.hopfKer (t 0)).val.toLinearMap
      Subtype.val_injective

  have hrank := (PDivisibleGroup.finrank_eq_pow_mul_finrank_and_finrank_hopfKer_eq_of_hopf_quotient_system_of_ringOfIntegers
    p K G M hMstab hMsat B π t hπ ht hπt hpts).2
  have hrk : ∀ i, Module.finrank ↥(PadicAlgCl.ringOfIntegers p K) ↥(HopfAlgebra.hopfKer (t (i + 1))) = Module.finrank ↥(PadicAlgCl.ringOfIntegers p K) ↥(HopfAlgebra.hopfKer (t i)) :=
    fun i => by rw [hrank (i + 1), hrank i]
  have hu : ∀ i, Function.Injective (uAlg p K B t m hmt htm i) :=
    fun i => injective_uAlg p K G M B π t hMstab hMsat hπ ht hπt hpts m hmt htm i
  obtain ⟨i₀, hi₀⟩ := Ws47.O.exists_forall_le_bijective (FractionRing ↥(PadicAlgCl.ringOfIntegers p K))
    (fun i => ↥(HopfAlgebra.hopfKer (t i))) (uAlg p K B t m hmt htm) hu hrk
  exact ⟨i₀, fun i hi => bijOn_of_bijective_uAlg p K B t m hmt htm i (hi₀ i hi)⟩

end

end Ws47.C2B

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (hMstab : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p)
        (x : TateModule p (G.Points (PadicAlgCl p))),
      x ∈ M → G.tateModuleRep (PadicAlgCl p) τ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (B v)]
    (π : ∀ v, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (t : ∀ v, B (v + 1) →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (hπ : ∀ v, Function.Surjective (π v)) (ht : ∀ v, Function.Surjective (t v))
    (hπt : ∀ v, (π v).comp (G.transition v) = (t v).comp (π (v + 1)))
    (hpts : ∀ (v : ℕ) (g : G.Point (PadicAlgCl p) v),
        (∃ g' : B v →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p,
            g'.comp (π v : G.level v →ₐ[PadicAlgCl.ringOfIntegers p K] B v) =
              PDivisibleGroup.Point.toAlgHom g) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul g) =
            (x : ℕ → G.Points (PadicAlgCl p)) v) :
    ∃ m : ∀ j, B j →ₐc[PadicAlgCl.ringOfIntegers p K] B (j + 1),
      (∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p) ∧
      (∀ j, (t j).comp (m j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B j) p) ∧
      (∀ j, ∀ d ∈ HopfAlgebra.hopfKer (t j),
        PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p d =
          algebraMap (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) (Coalgebra.counit d)) ∧
      (∀ j, Set.MapsTo (m (j + 1)) (HopfAlgebra.hopfKer (t j) : Set (B (j + 1)))
        (HopfAlgebra.hopfKer (t (j + 1)) : Set (B (j + 2)))) ∧
      ∃ i₀ : ℕ, ∀ i, i₀ ≤ i →
        Set.BijOn (m (i + 1)) (HopfAlgebra.hopfKer (t i) : Set (B (i + 1)))
          (HopfAlgebra.hopfKer (t (i + 1)) : Set (B (i + 2))) := by
  obtain ⟨m, hmt, htm⟩ := Ws47.C2B.exists_comp_eq_nsmulBialgHom p K G M B π t hMsat hπ ht hπt hpts
  obtain ⟨i₀, hi₀⟩ := Ws47.C2B.exists_forall_le_bijOn_hopfKer p K G M B π t hMstab hMsat hπ ht hπt hpts m hmt htm
  exact ⟨m, hmt, htm, fun j d hd => Ws47.C2B.nsmulAlgHom_eq_counit_of_mem_hopfKer p K B t m hmt j d hd,
    fun j => Ws47.C2B.mapsTo_hopfKer p K B t m hmt htm j, i₀, hi₀⟩

end S_PDivisibleGroup_exists_bialgHom_comp_eq_nsmulBialgHom_and_bijOn_hopfKer_of_hopf_quotient_system_of_ringOfIntegers
end P2MW
export P2MW.S_PDivisibleGroup_exists_bialgHom_comp_eq_nsmulBialgHom_and_bijOn_hopfKer_of_hopf_quotient_system_of_ringOfIntegers (solution)
