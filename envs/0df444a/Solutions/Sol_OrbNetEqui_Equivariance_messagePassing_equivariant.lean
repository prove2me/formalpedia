-- Prove2me | solution 1 for OrbNetEqui.Equivariance.messagePassing_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:15:36.337851+00:00
-- url     : https://prove2.me/submissions/267a4bd4-c5f9-4c98-a269-c448f29c9a60

import Definitions.Def_OrbNetEqui_Equivariance_Basic
import Init
import Mathlib

section
noncomputable section
namespace Queelius.UniteEquivariance
open scoped MonoidAlgebra
open Representation
variable {K E : Type*} [Group K] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem representation_inverse_apply (ρ : Representation ℂ K E) (g : K) (x : E) :
    ρ g (ρ g⁻¹ x) = x := by
  rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one]
  rfl

def orthogonalSubrepresentation (ρ : Representation ℂ K E)
    (hu : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (W : Subrepresentation ρ) : Subrepresentation ρ where
  toSubmodule := W.toSubmoduleᗮ
  apply_mem_toSubmodule := by
    intro g x hx y hy
    have h := hu g (ρ g⁻¹ y) x
    rw [representation_inverse_apply] at h
    rw [h]
    exact hx _ (W.apply_mem_toSubmodule g⁻¹ hy)

theorem unitary_subrepresentation_isCompl [FiniteDimensional ℂ E]
    (ρ : Representation ℂ K E)
    (hu : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (W : Subrepresentation ρ) : IsCompl W (orthogonalSubrepresentation ρ hu W) := by
  constructor
  · rw [disjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    exact W.toSubmodule.inf_orthogonal_eq_bot
  · rw [codisjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    exact W.toSubmodule.sup_orthogonal_of_hasOrthogonalProjection

theorem unitary_representation_semisimple [FiniteDimensional ℂ E]
    (ρ : Representation ℂ K E)
    (hu : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y) :
    Representation.IsSemisimpleRepresentation ρ := by
  constructor
  intro W
  exact ⟨orthogonalSubrepresentation ρ hu W,unitary_subrepresentation_isCompl ρ hu W⟩

theorem unitary_module_semisimple [FiniteDimensional ℂ E]
    (ρ : Representation ℂ K E)
    (hu : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y) :
    IsSemisimpleModule ℂ[K] ρ.asModule :=
  (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp
    (unitary_representation_semisimple ρ hu)

theorem unitary_finite_simple_decomposition [FiniteDimensional ℂ E]
    (ρ : Representation ℂ K E)
    (hu : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y) :
    ∃ (n : ℕ) (S : Fin n → Submodule ℂ[K] ρ.asModule)
      (_ : ρ.asModule ≃ₗ[ℂ[K]] Π₀ i : Fin n, S i), ∀ i, IsSimpleModule ℂ[K] (S i) := by
  letI := unitary_module_semisimple ρ hu
  letI : Module.Finite ℂ[K] ρ.asModule := Module.Finite.of_restrictScalars_finite ℂ ℂ[K] ρ.asModule
  exact IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp ℂ[K] ρ.asModule

end Queelius.UniteEquivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open Matrix
variable {ι Λ : Type*} [Fintype ι] (lab : ι → Λ) (dim : Λ → ℕ)

noncomputable def labelMultiplicity (L : Λ) : ℕ := by
  classical
  exact Fintype.card {i : ι // lab i = L}

noncomputable def fiberVectorEquiv (L : Λ) (i : {i : ι // lab i = L}) :
    (Fin (dim (lab i.val)) → ℂ) ≃ₗ[ℂ] (Fin (dim L) → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (finCongr (congrArg dim i.property)).symm

noncomputable def fiberGroupEquiv (L : Λ) :
    ((i : {i : ι // lab i = L}) → Fin (dim (lab i.val)) → ℂ) ≃ₗ[ℂ]
      (Fin (labelMultiplicity lab L) → Fin (dim L) → ℂ) := by
  classical
  exact (LinearEquiv.piCongrRight (fiberVectorEquiv lab dim L)).trans
    (LinearEquiv.funCongrLeft ℂ (Fin (dim L) → ℂ)
      (Fintype.equivFin {i : ι // lab i = L}).symm)

noncomputable def catalogueGroupEquiv :
    ((i : ι) → Fin (dim (lab i)) → ℂ) ≃ₗ[ℂ]
      ((L : Λ) → Fin (labelMultiplicity lab L) → Fin (dim L) → ℂ) :=
  { Equiv.piCongrFiberwise (fun L => (fiberGroupEquiv lab dim L).toEquiv) with
    map_add' := by intro x y; ext L ν M; exact congrFun (congrFun ((fiberGroupEquiv lab dim L).map_add (fun i => x i.val) (fun i => y i.val)) ν) M
    map_smul' := by intro c x; ext L ν M; exact congrFun (congrFun ((fiberGroupEquiv lab dim L).map_smul c (fun i => x i.val)) ν) M }

 theorem labelMultiplicity_support : ∃ s : Finset Λ, ∀ L, L ∉ s → labelMultiplicity lab L = 0 := by
  classical
  refine ⟨Finset.univ.image lab,?_⟩
  intro L h
  unfold labelMultiplicity
  exact Fintype.card_eq_zero_iff.mpr ⟨fun i => h (Finset.mem_image.mpr ⟨i.val,Finset.mem_univ _,i.property⟩)⟩

 theorem fiberVector_intertwining {K : Type*} [Group K]
    (U : (L : Λ) → K →* unitaryGroup (Fin (dim L)) ℂ)
    (L : Λ) (i : {i : ι // lab i = L}) (g : K) (x : Fin (dim (lab i.val)) → ℂ) :
    fiberVectorEquiv lab dim L i ((U (lab i.val) g : Matrix _ _ ℂ) *ᵥ x) =
      (U L g : Matrix _ _ ℂ) *ᵥ fiberVectorEquiv lab dim L i x := by
  rcases i with ⟨i,hi⟩
  subst L
  rfl

 theorem catalogueGroup_intertwining {K : Type*} [Group K]
    (U : (L : Λ) → K →* unitaryGroup (Fin (dim L)) ℂ)
    (g : K) (x : (i : ι) → Fin (dim (lab i)) → ℂ) (L : Λ)
    (ν : Fin (labelMultiplicity lab L)) :
    catalogueGroupEquiv lab dim (fun i => (U (lab i) g : Matrix _ _ ℂ) *ᵥ x i) L ν =
      (U L g : Matrix _ _ ℂ) *ᵥ catalogueGroupEquiv lab dim x L ν := by
  classical
  exact fiberVector_intertwining lab dim U L
    ((Fintype.equivFin {i : ι // lab i = L}).symm ν) g _

 theorem labelMultiplicity_dimension [DecidableEq Λ] :
    ∑ L ∈ Finset.univ.image lab, labelMultiplicity lab L * dim L = ∑ i, dim (lab i) := by
  classical
  simpa [labelMultiplicity, Fintype.card_subtype] using
    (Finset.sum_fiberwise_of_maps_to' (s:=Finset.univ) (t:=Finset.univ.image lab)
      (g:=lab) (fun i hi => Finset.mem_image.mpr ⟨i,hi,rfl⟩) dim)

 theorem labelMultiplicity_outside_image [DecidableEq Λ] (L : Λ)
    (h : L ∉ Finset.univ.image lab) : labelMultiplicity lab L = 0 := by
  classical
  have hempty : IsEmpty {i : ι // lab i = L} := ⟨fun i => h (Finset.mem_image.mpr ⟨i.val,Finset.mem_univ _,i.property⟩)⟩
  unfold labelMultiplicity
  rw [Fintype.card_eq_nat_card]
  exact Nat.card_eq_zero.mpr (Or.inl hempty)

end Queelius.UniteEquivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open Matrix Finset OrbNetEqui.Equivariance
universe u

theorem unitary_sum_normSq {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix.unitaryGroup ι ℂ) (x : ι → ℂ) :
    ∑ i, Complex.normSq (((A : Matrix ι ι ℂ) *ᵥ x) i) = ∑ i, Complex.normSq (x i) := by
  apply Complex.ofReal_injective
  push_cast
  simp only [Complex.normSq_eq_conj_mul_self]
  change star ((A : Matrix ι ι ℂ) *ᵥ x) ⬝ᵥ ((A : Matrix ι ι ℂ) *ᵥ x) = star x ⬝ᵥ x
  rw [Matrix.star_mulVec,← Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec,
    ← Matrix.star_eq_conjTranspose,Matrix.UnitaryGroup.star_mul_self,Matrix.one_mulVec]

theorem regNorm_unitary {m : ℕ} (A : Matrix.unitaryGroup (Fin m) ℂ)
    (ε : ℝ) (x : Fin m → ℂ) : regNorm ε ((A : Matrix (Fin m) (Fin m) ℂ) *ᵥ x) = regNorm ε x := by
  simp only [regNorm,Finset.sum_add_distrib,unitary_sum_normSq]

theorem evNorm_general {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ} {nmax : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (μ σ β : Λ → Fin nmax → ℝ) (ε : ℝ) (k : K) (x : Feature Λ dim nmax) :
    evNormBar μ σ ε (featAct U k x) = evNormBar μ σ ε x ∧
      evNormHat β ε (featAct U k x) = featAct U k (evNormHat β ε x) := by
  constructor
  · funext L c
    simp only [evNormBar,featAct,regNorm_unitary]
  · funext L c M
    change ((U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ x L c) M /
      ((regNorm ε ((U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ x L c) + 1 / β L c + ε : ℝ) : ℂ) =
      ((U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ
        (fun m => x L c m / ((regNorm ε (x L c) + 1 / β L c + ε : ℝ) : ℂ))) M
    rw [regNorm_unitary]
    simp only [Matrix.mulVec,dotProduct,← mul_div_assoc,← Finset.sum_div]

end Queelius.UniteEquivariance

namespace OrbNetEqui.Equivariance
open Matrix

theorem evNorm_equivariant {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ} {nmax : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (μ σ β : Λ → Fin nmax → ℝ) (ε : ℝ) (hβ : ∀ L c, 0 < β L c) (hε : 0 < ε)
    (k : K) (x : Feature Λ dim nmax) :
    evNormBar μ σ ε (featAct U k x) = evNormBar μ σ ε x ∧
      evNormHat β ε (featAct U k x) = featAct U k (evNormHat β ε x) :=
  Queelius.UniteEquivariance.evNorm_general U μ σ β ε k x

end OrbNetEqui.Equivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open Finset OrbNetEqui.Equivariance
variable {Λ β : Type*} {dim μ : Λ → ℕ} {N : ℕ} [Fintype β]

def coefficientsOfLinearMap
    (ψ : ((Fin N → β) → ℂ) →ₗ[ℂ] ((L : Λ) → Fin (μ L) → Fin (dim L) → ℂ)) :
    (L : Λ) → Fin (μ L) → Fin (dim L) → (Fin N → β) → ℂ :=
  by
    classical
    exact fun L ν M v => ψ (Pi.single v 1) L ν M

theorem linearMap_eq_coeffMap
    (ψ : ((Fin N → β) → ℂ) →ₗ[ℂ] ((L : Λ) → Fin (μ L) → Fin (dim L) → ℂ))
    (T : (Fin N → β) → ℂ) :
    ψ T = coeffMap (coefficientsOfLinearMap ψ) T := by
  classical
  have hT : T = ∑ v, T v • Pi.single v (1 : ℂ) := by
    ext w
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hT]
  simp only [map_sum, map_smul]
  ext L ν M
  simp [coeffMap, coefficientsOfLinearMap, Finset.sum_apply]

theorem coeffMap_injective_of_linearEquiv
    (e : ((Fin N → β) → ℂ) ≃ₗ[ℂ] ((L : Λ) → Fin (μ L) → Fin (dim L) → ℂ)) :
    Function.Injective (coeffMap (coefficientsOfLinearMap e.toLinearMap)) := by
  intro T S h
  apply e.injective
  change e.toLinearMap T = e.toLinearMap S
  simpa only [linearMap_eq_coeffMap] using h

end Queelius.UniteEquivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open Matrix Finset OrbNetEqui.Equivariance
universe u v w

def pairVector {ι : Type u} {κ : Type v} (x : ι → ℂ) (y : κ → ℂ) : ι × κ → ℂ :=
  fun ij => x ij.1 * y ij.2

theorem kronecker_pairVector {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (x : ι → ℂ) (y : κ → ℂ) :
    (Matrix.kroneckerMap (· * ·) A B) *ᵥ pairVector x y = pairVector (A *ᵥ x) (B *ᵥ y) := by
  funext ij
  simp only [Matrix.mulVec,dotProduct,pairVector,Matrix.kroneckerMap_apply,Fintype.sum_prod_type,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

def couple {ι : Type u} {κ : Type v} {τ : Type w} [Fintype ι] [Fintype κ]
    (C : Matrix τ (ι × κ) ℂ) (x : ι → ℂ) (y : κ → ℂ) : τ → ℂ := C *ᵥ pairVector x y

theorem couple_intertwines {ι : Type u} {κ : Type v} {τ : Type w}
    [Fintype ι] [Fintype κ] [Fintype τ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (D : Matrix τ τ ℂ)
    (C : Matrix τ (ι × κ) ℂ) (hC : C * Matrix.kroneckerMap (· * ·) A B = D * C)
    (x : ι → ℂ) (y : κ → ℂ) :
    couple C (A *ᵥ x) (B *ᵥ y) = D *ᵥ couple C x y := by
  unfold couple
  rw [← kronecker_pairVector,Matrix.mulVec_mulVec,hC,Matrix.mulVec_mulVec]

theorem couple_apply {ι : Type u} {κ : Type v} {τ : Type w} [Fintype ι] [Fintype κ]
    (C : Matrix τ (ι × κ) ℂ) (x : ι → ℂ) (y : κ → ℂ) (i : τ) :
    couple C x y i = ∑ a, ∑ b, x a * y b * C i (a,b) := by
  simp only [couple,Matrix.mulVec,dotProduct,pairVector,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

def coupledFeatures {Λ : Type*} [Fintype Λ] {dim : Λ → ℕ} {nmax : ℕ}
    (C : Fin nmax → (L₁ L₂ L : Λ) → Matrix (Fin (dim L)) (Fin (dim L₁) × Fin (dim L₂)) ℂ)
    (h g : Feature Λ dim nmax) : Feature Λ dim nmax :=
  fun L c => ∑ L₁, ∑ L₂, couple (C c L₁ L₂ L) (h L₁ c) (g L₂ c)

theorem coupledFeatures_equivariant {K : Type*} [Group K] {Λ : Type*} [Fintype Λ]
    {dim : Λ → ℕ} {nmax : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (C : Fin nmax → (L₁ L₂ L : Λ) → Matrix (Fin (dim L)) (Fin (dim L₁) × Fin (dim L₂)) ℂ)
    (k : K) (hC : ∀ c L₁ L₂ L, C c L₁ L₂ L * Matrix.kroneckerMap (· * ·)
      (U L₁ k : Matrix (Fin (dim L₁)) (Fin (dim L₁)) ℂ)
      (U L₂ k : Matrix (Fin (dim L₂)) (Fin (dim L₂)) ℂ) =
      (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) * C c L₁ L₂ L)
    (h g : Feature Λ dim nmax) :
    coupledFeatures C (featAct U k h) (featAct U k g) = featAct U k (coupledFeatures C h g) := by
  funext L c
  dsimp [coupledFeatures,featAct]
  simp only [Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro L₁ hL₁
  apply Finset.sum_congr rfl
  intro L₂ hL₂
  exact couple_intertwines _ _ _ _ (hC c L₁ L₂ L) _ _

end Queelius.UniteEquivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open Matrix Finset OrbNetEqui.Equivariance
variable {Λ β : Type*} {dim μ : Λ → ℕ} {N : ℕ} [Fintype β]

def multiplicityEmbedding (s : Finset Λ) :
    ((Σ L : s, Fin (μ L)) → ℂ) →ₗ[ℂ] ((L : Λ) → Fin (μ L) → Fin (dim L) → ℂ) := by
  classical
  exact {
    toFun := fun f L ν _M => if h : L ∈ s then f ⟨⟨L,h⟩,ν⟩ else 0
    map_add' := by intro f g; ext L ν M; by_cases h : L ∈ s <;> simp [h]
    map_smul' := by intro c f; ext L ν M; by_cases h : L ∈ s <;> simp [h]
  }

theorem multiplicityEmbedding_injective (s : Finset Λ)
    (hpos : ∀ L ∈ s, 0 < dim L) :
    Function.Injective (multiplicityEmbedding (μ := μ) (dim := dim) s) := by
  classical
  intro f g h
  ext a
  have hv := congrFun (congrFun (congrFun h a.1) a.2) ⟨0,hpos a.1 a.1.property⟩
  simpa [multiplicityEmbedding] using hv

theorem catalogue_multiplicity_bound (s : Finset Λ) (hpos : ∀ L ∈ s, 0 < dim L)
    (e : ((Fin N → β) → ℂ) ≃ₗ[ℂ] ((L : Λ) → Fin (μ L) → Fin (dim L) → ℂ)) :
    ∑ L ∈ s, μ L ≤ Fintype.card β ^ N := by
  classical
  let f := e.symm.toLinearMap.comp (multiplicityEmbedding s)
  have hf : Function.Injective f := e.symm.injective.comp (multiplicityEmbedding_injective s hpos)
  have hb := LinearMap.finrank_le_finrank_of_injective hf
  simpa [Module.finrank_pi, Fintype.card_sigma, Finset.sum_attach] using hb

theorem coefficient_reduction_of_decomposition {K : Type*} [Group K]
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (hirr : ∀ L, IsIrreducibleUnitary (U L))
    (A : K → Matrix β β ℂ) [DecidableEq β]
    (s : Finset Λ) (hs : ∀ L, L ∉ s → μ L = 0)
    (e : ((Fin N → β) → ℂ) ≃ₗ[ℂ] ((L : Λ) → Fin (μ L) → Fin (dim L) → ℂ))
    (he : ∀ k T L ν, e (diagAct (A k) T) L ν =
      (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ e T L ν) :
    ∃ Q : (L : Λ) → Fin (μ L) → Fin (dim L) → (Fin N → β) → ℂ,
      Function.Injective (coeffMap Q) ∧
      ∑ L ∈ s, μ L ≤ Fintype.card β ^ N ∧
      ∀ k T L ν, coeffMap Q (diagAct (A k) T) L ν =
        (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ coeffMap Q T L ν := by
  refine ⟨coefficientsOfLinearMap e.toLinearMap, coeffMap_injective_of_linearEquiv e,
    catalogue_multiplicity_bound s (fun L _ => (hirr L).1) e, ?_⟩
  intro k T L ν
  simp only [← linearMap_eq_coeffMap, LinearEquiv.coe_coe]
  exact he k T L ν

end Queelius.UniteEquivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open Matrix Finset OrbNetEqui.Equivariance

def gatedFeature {Λ : Type*} {dim : Λ → ℕ} {nmax : ℕ}
    (mlp : (Λ → Fin nmax → ℝ) → (Λ → Fin nmax → ℝ))
    (μ σ β : Λ → Fin nmax → ℝ) (ε : ℝ) (h : Feature Λ dim nmax) : Feature Λ dim nmax :=
  fun L c M => (mlp (evNormBar μ σ ε h) L c : ℂ) * evNormHat β ε h L c M

theorem featAct_add {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ} {nmax : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ) (k : K)
    (h g : Feature Λ dim nmax) : featAct U k (h+g) = featAct U k h + featAct U k g := by
  funext L c M
  exact congrFun (Matrix.mulVec_add _ (h L c) (g L c)) M

theorem gatedFeature_equivariant {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ} {nmax : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ) (k : K)
    (mlp : (Λ → Fin nmax → ℝ) → (Λ → Fin nmax → ℝ))
    (μ σ β : Λ → Fin nmax → ℝ) (ε : ℝ) (h : Feature Λ dim nmax) :
    gatedFeature mlp μ σ β ε (featAct U k h) = featAct U k (gatedFeature mlp μ σ β ε h) := by
  have hb := (evNorm_general U μ σ β ε k h).1
  have hh := (evNorm_general U μ σ β ε k h).2
  unfold gatedFeature
  rw [hb,hh]
  funext L c M
  change (mlp (evNormBar μ σ ε h) L c : ℂ) *
      ((U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ evNormHat β ε h L c) M =
    ((U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ
      (fun m => (mlp (evNormBar μ σ ε h) L c : ℂ) * evNormHat β ε h L c m)) M
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem coupledFeatures_expansion {Λ : Type*} [Fintype Λ] {dim : Λ → ℕ} {nmax : ℕ}
    (C : Fin nmax → (L₁ L₂ L : Λ) → Matrix (Fin (dim L)) (Fin (dim L₁) × Fin (dim L₂)) ℂ)
    (h g : Feature Λ dim nmax) :
    coupledFeatures C h g = fun L c M => ∑ L₁, ∑ L₂, ∑ M₁, ∑ M₂,
      h L₁ c M₁ * g L₂ c M₂ * C c L₁ L₂ L M (M₁,M₂) := by
  funext L c M
  simp only [coupledFeatures,Finset.sum_apply,couple_apply]

theorem pointwise_factorization {Λ : Type*} [Fintype Λ] {dim : Λ → ℕ} {nmax : ℕ}
    (P : PointwiseParams Λ dim nmax) (ε : ℝ) (h g : Feature Λ dim nmax) :
    pointwise P ε h g = h + gatedFeature P.mlp₂ P.μq P.σq P.βq ε
      (g + coupledFeatures P.C (gatedFeature P.mlp₁ P.μh P.σh P.βh ε h) g) := by
  rw [coupledFeatures_expansion]
  rfl

theorem pointwise_general {K : Type*} [Group K] {Λ : Type*} [Fintype Λ]
    {dim : Λ → ℕ} {nmax : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (P : PointwiseParams Λ dim nmax) (ε : ℝ) (k : K)
    (hC : ∀ c L₁ L₂ L, P.C c L₁ L₂ L * Matrix.kroneckerMap (· * ·)
      (U L₁ k : Matrix (Fin (dim L₁)) (Fin (dim L₁)) ℂ)
      (U L₂ k : Matrix (Fin (dim L₂)) (Fin (dim L₂)) ℂ) =
      (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) * P.C c L₁ L₂ L)
    (h g : Feature Λ dim nmax) :
    pointwise P ε (featAct U k h) (featAct U k g) = featAct U k (pointwise P ε h g) := by
  rw [pointwise_factorization,pointwise_factorization,gatedFeature_equivariant,
    coupledFeatures_equivariant U P.C k hC]
  rw [← featAct_add,gatedFeature_equivariant,← featAct_add]

end Queelius.UniteEquivariance

namespace OrbNetEqui.Equivariance
open Matrix

theorem pointwise_equivariant {K : Type*} [Group K] {Λ : Type*} [Fintype Λ]
    {dim : Λ → ℕ} {nmax : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (P : PointwiseParams Λ dim nmax) (ε : ℝ)
    (hβ : ∀ L c, 0 < P.βh L c ∧ 0 < P.βq L c) (hε : 0 < ε) (k : K)
    (hC : ∀ (c : Fin nmax) (L₁ L₂ L : Λ),
      P.C c L₁ L₂ L * Matrix.kroneckerMap (· * ·)
          (U L₁ k : Matrix (Fin (dim L₁)) (Fin (dim L₁)) ℂ)
          (U L₂ k : Matrix (Fin (dim L₂)) (Fin (dim L₂)) ℂ) =
        (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) * P.C c L₁ L₂ L)
    (h g' : Feature Λ dim nmax) :
    pointwise P ε (featAct U k h) (featAct U k g') = featAct U k (pointwise P ε h g') :=
  Queelius.UniteEquivariance.pointwise_general U P ε k hC h g'

end OrbNetEqui.Equivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open Matrix Finset OrbNetEqui.Equivariance

theorem regNorm_nonnegative {m : ℕ} (ε : ℝ) (x : Fin m → ℂ) : 0 ≤ regNorm ε x := by
  have hsum : 0 ≤ ∑ M, Complex.normSq (x M) := Finset.sum_nonneg (fun M hM => Complex.normSq_nonneg _)
  unfold regNorm
  apply sub_nonneg.mpr
  calc
    ε ≤ |ε| := le_abs_self ε
    _ = Real.sqrt (ε^2) := (Real.sqrt_sq_eq_abs ε).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by linarith)

theorem direction_denominator_positive {m : ℕ} (β ε : ℝ) (hβ : 0 < β) (hε : 0 < ε)
    (x : Fin m → ℂ) : 0 < regNorm ε x + 1/β + ε := by
  have hn := regNorm_nonnegative ε x
  have hi := one_div_pos.mpr hβ
  linarith

theorem regNorm_zero {m : ℕ} (ε : ℝ) (hε : 0 ≤ ε) :
    regNorm ε (fun _ : Fin m => (0 : ℂ)) = 0 := by
  simp [regNorm,Real.sqrt_sq_eq_abs,abs_of_nonneg hε]

end Queelius.UniteEquivariance

namespace Queelius.UniteEquivariance.Controls
open Matrix Finset OrbNetEqui.Equivariance

def quarterTurn : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨!![0,-1;1,0], by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.star_eq_conjTranspose,Matrix.mul_apply,Fin.sum_univ_two]⟩

def sampleVector : Fin 2 → ℂ := ![3,4]

theorem quarterTurn_sample : (quarterTurn : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ sampleVector = ![-4,3] := by
  ext i
  fin_cases i <;> norm_num [quarterTurn,sampleVector,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem regularized_sample : regNorm 12 sampleVector = 1 := by
  norm_num [regNorm,sampleVector,Fin.sum_univ_two,Complex.normSq]

theorem regularized_rotated : regNorm 12 ((quarterTurn : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ sampleVector) = 1 := by
  rw [regNorm_unitary,regularized_sample]

def standardRep (_ : Unit) : Matrix.unitaryGroup (Fin 2) ℂ →* Matrix.unitaryGroup (Fin 2) ℂ :=
  MonoidHom.id _

def sampleFeature : Feature Unit (fun _ => 2) 1 := fun _ _ => sampleVector

theorem sample_direction : evNormHat (fun (_ : Unit) (_ : Fin 1) => 1) 12 sampleFeature () 0 =
    fun m => sampleVector m / 14 := by
  ext m
  norm_num [evNormHat,sampleFeature,regularized_sample]

theorem sample_bar : evNormBar (fun (_ : Unit) (_ : Fin 1) => 0) (fun _ _ => 1)
    12 sampleFeature () 0 = 1 := by
  simp [evNormBar,sampleFeature,regularized_sample]

theorem rotated_direction :
    evNormHat (fun (_ : Unit) (_ : Fin 1) => 1) 12 (featAct standardRep quarterTurn sampleFeature) () 0 =
      fun m => (![-4,3] : Fin 2 → ℂ) m / 14 := by
  change (fun m => (((quarterTurn : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ sampleVector) m) /
    ((regNorm 12 ((quarterTurn : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ sampleVector) + 1/(1 : ℝ) + 12 : ℝ) : ℂ)) = _
  rw [regularized_rotated,quarterTurn_sample]
  norm_num

end Queelius.UniteEquivariance.Controls

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open Matrix Finset OrbNetEqui.Equivariance

variable {K : Type*} [Group K] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
  {dim : Λ → ℕ} {d nmax I : ℕ} {Kmul : Fin d → Λ → ℕ}
  {ι : Fin d → Type*} [∀ u, Fintype (ι u)] [∀ u, DecidableEq (ι u)]

theorem pi2_mulVec (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (u : Fin d) (k : K) (x : MIdx dim Kmul u → ℂ) (L : Λ) (r : Fin (Kmul u L)) (M : Fin (dim L)) :
    (π₂mat U Kmul u k *ᵥ x) ⟨L,(r,M)⟩ =
      ∑ M', (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) M M' * x ⟨L,(r,M')⟩ := by
  simp [π₂mat,Matrix.mulVec,dotProduct,Fintype.sum_sigma,Matrix.blockDiagonal'_apply,
    Fintype.sum_prod_type,Matrix.kroneckerMap_apply,Matrix.one_apply]

def channelMix (W : (u : Fin d) → Fin I → (L : Λ) → Matrix (Fin (Kmul u L)) (Fin nmax) ℂ)
    (u : Fin d) (i : Fin I) (h : Feature Λ dim nmax) : MIdx dim Kmul u → ℂ :=
  fun x => ∑ c, W u i x.1 x.2.1 c * h x.1 c x.2.2

theorem channelMix_equivariant (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (W : (u : Fin d) → Fin I → (L : Λ) → Matrix (Fin (Kmul u L)) (Fin nmax) ℂ)
    (u : Fin d) (i : Fin I) (k : K) (h : Feature Λ dim nmax) :
    channelMix W u i (featAct U k h) = π₂mat U Kmul u k *ᵥ channelMix W u i h := by
  funext ⟨L,r,M⟩
  rw [pi2_mulVec]
  simp only [channelMix,featAct,Matrix.mulVec,dotProduct,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem matching_equivariant (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (D : (u : Fin d) → Matrix (ι u) (MIdx dim Kmul u) ℂ)
    (W : (u : Fin d) → Fin I → (L : Λ) → Matrix (Fin (Kmul u L)) (Fin nmax) ℂ)
    (u : Fin d) (i : Fin I) (k : K) (A : Matrix (ι u) (ι u) ℂ)
    (hD : D u * π₂mat U Kmul u k = A * D u) (h : Feature Λ dim nmax) :
    matching D W u i (featAct U k h) = A *ᵥ matching D W u i h := by
  change D u *ᵥ channelMix W u i (featAct U k h) = A *ᵥ (D u *ᵥ channelMix W u i h)
  rw [channelMix_equivariant,Matrix.mulVec_mulVec,hD,Matrix.mulVec_mulVec]

end Queelius.UniteEquivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance.Controls
open Matrix Finset OrbNetEqui.Equivariance

def phaseUnitary : Matrix.unitaryGroup (Fin 1) ℂ :=
  ⟨!![Complex.I], by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.star_eq_conjTranspose,Matrix.mul_apply,Fin.sum_univ_one]⟩

def scalarCoupling : Matrix (Fin 1) (Fin 1 × Fin 1) ℂ := fun _ _ => 1

theorem phase_intertwines :
    scalarCoupling * Matrix.kroneckerMap (· * ·)
      (phaseUnitary : Matrix (Fin 1) (Fin 1) ℂ) (phaseUnitary : Matrix (Fin 1) (Fin 1) ℂ) =
    (-1 : Matrix (Fin 1) (Fin 1) ℂ) * scalarCoupling := by
  ext i j
  fin_cases i
  rcases j with ⟨j,k⟩
  fin_cases j
  fin_cases k
  norm_num [scalarCoupling,phaseUnitary,Matrix.mul_apply,Matrix.kroneckerMap,Fintype.sum_prod_type,Fin.sum_univ_one]

theorem phase_coupling_nonzero :
    couple scalarCoupling (fun _ => (2 : ℂ)) (fun _ => (3 : ℂ)) 0 = 6 ∧
    couple scalarCoupling
      ((phaseUnitary : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ fun _ => (2 : ℂ))
      ((phaseUnitary : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ fun _ => (3 : ℂ)) 0 = -6 := by
  constructor
  · norm_num [couple,scalarCoupling,pairVector,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_one]
  · rw [couple_intertwines _ _ _ _ phase_intertwines]
    norm_num [couple,scalarCoupling,pairVector,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_one]

theorem wrong_output_phase_fails :
    couple scalarCoupling
      ((phaseUnitary : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ fun _ => (2 : ℂ))
      ((phaseUnitary : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ fun _ => (3 : ℂ)) ≠
    (1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ couple scalarCoupling (fun _ => (2 : ℂ)) (fun _ => (3 : ℂ)) := by
  intro h
  have hh := congrFun h 0
  rw [Matrix.one_mulVec,phase_coupling_nonzero.1,phase_coupling_nonzero.2] at hh
  norm_num at hh

end Queelius.UniteEquivariance.Controls

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open Matrix Finset OrbNetEqui.Equivariance

variable {K : Type*} [Group K] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
  {dim : Λ → ℕ} {d nmax I J : ℕ} {Kmul : Fin d → Λ → ℕ}
  {ι : Fin d → Type*} [∀ u, Fintype (ι u)] [∀ u, DecidableEq (ι u)]

theorem pi2_unitary (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (u : Fin d) (k : K) : π₂mat U Kmul u k ∈ Matrix.unitaryGroup (MIdx dim Kmul u) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (π₂mat U Kmul u k)ᴴ * π₂mat U Kmul u k = 1
  unfold π₂mat
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  have h : ∀ L : Λ, (Matrix.kroneckerMap (· * ·)
      (1 : Matrix (Fin (Kmul u L)) (Fin (Kmul u L)) ℂ) (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ))ᴴ *
      Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin (Kmul u L)) (Fin (Kmul u L)) ℂ)
      (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) = 1 := by
    intro L
    exact (Matrix.kronecker_mem_unitary (one_mem _) (U L k).property).1
  simp_rw [h]
  exact Matrix.blockDiagonal'_one

theorem adjoint_intertwines {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (A : Matrix.unitaryGroup α ℂ)
    (B : Matrix.unitaryGroup β ℂ) (D : Matrix α β ℂ)
    (hD : D * (B : Matrix β β ℂ) = (A : Matrix α α ℂ) * D) :
    Dᴴ * (A : Matrix α α ℂ) = (B : Matrix β β ℂ) * Dᴴ := by
  have h := congrArg Matrix.conjTranspose hD
  simp only [Matrix.conjTranspose_mul] at h
  have h' := congrArg (fun X => (B : Matrix β β ℂ) * X * (A : Matrix α α ℂ)) h
  change (B : Matrix β β ℂ) * ((B : Matrix β β ℂ)ᴴ * Dᴴ) * (A : Matrix α α ℂ) =
    (B : Matrix β β ℂ) * (Dᴴ * (A : Matrix α α ℂ)ᴴ) * (A : Matrix α α ℂ) at h'
  calc
    Dᴴ * (A : Matrix α α ℂ) = (B : Matrix β β ℂ) * ((B : Matrix β β ℂ)ᴴ * Dᴴ) * (A : Matrix α α ℂ) := by
      rw [← Matrix.mul_assoc,show (B : Matrix β β ℂ) * (B : Matrix β β ℂ)ᴴ = 1 from B.property.2,Matrix.one_mul]
    _ = (B : Matrix β β ℂ) * (Dᴴ * (A : Matrix α α ℂ)ᴴ) * (A : Matrix α α ℂ) := h'
    _ = (B : Matrix β β ℂ) * Dᴴ := by
      rw [Matrix.mul_assoc,Matrix.mul_assoc,
        show (A : Matrix α α ℂ)ᴴ * (A : Matrix α α ℂ) = 1 from A.property.1,Matrix.mul_one]

theorem reverseMatching_equivariant (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (D : (u : Fin d) → Matrix (ι u) (MIdx dim Kmul u) ℂ)
    (Wd : (u : Fin d) → (L : Λ) → Matrix (Fin nmax) (Fin (Kmul u L) × Fin I × Fin J) ℂ)
    (u : Fin d) (k : K) (A : Matrix.unitaryGroup (ι u) ℂ)
    (hD : D u * π₂mat U Kmul u k = (A : Matrix (ι u) (ι u) ℂ) * D u)
    (m : Fin I × Fin J → ι u → ℂ) :
    revMatching D Wd u (fun ij => (A : Matrix (ι u) (ι u) ℂ) *ᵥ m ij) =
      featAct U k (revMatching D Wd u m) := by
  have hd := adjoint_intertwines A ⟨π₂mat U Kmul u k,pi2_unitary U u k⟩ (D u) hD
  have hh (ij : Fin I × Fin J) (L : Λ) (r : Fin (Kmul u L)) (M : Fin (dim L)) :
      ∑ v, starRingEnd ℂ (D u v ⟨L,(r,M)⟩) *
        ((A : Matrix (ι u) (ι u) ℂ) *ᵥ m ij) v =
      ∑ M', (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) M M' *
        ∑ v, starRingEnd ℂ (D u v ⟨L,(r,M')⟩) * m ij v := by
    change ((D u)ᴴ *ᵥ ((A : Matrix (ι u) (ι u) ℂ) *ᵥ m ij)) ⟨L,(r,M)⟩ = _
    rw [Matrix.mulVec_mulVec,hd,← Matrix.mulVec_mulVec,pi2_mulVec]
    rfl
  funext L c M
  simp only [featAct,revMatching]
  simp_rw [hh]
  simp only [featAct,Matrix.mulVec,dotProduct,revMatching,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M' hM
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro v hv
  ring

end Queelius.UniteEquivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open Matrix Finset OrbNetEqui.Equivariance

def productMatrix {J : Type*} [Fintype J] {κ : J → Type*}
    (A : (j : J) → Matrix (κ j) (κ j) ℂ) : Matrix ((j : J) → κ j) ((j : J) → κ j) ℂ :=
  fun x y => ∏ j, A j (x j) (y j)

theorem productMatrix_unitary {J : Type*} [Fintype J] [DecidableEq J]
    {κ : J → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (A : (j : J) → Matrix.unitaryGroup (κ j) ℂ) :
    productMatrix (fun j => (A j : Matrix (κ j) (κ j) ℂ)) ∈
      Matrix.unitaryGroup ((j : J) → κ j) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  ext x y
  simp only [Matrix.star_eq_conjTranspose,Matrix.mul_apply,Matrix.conjTranspose_apply,productMatrix]
  simp only [star_prod,← Finset.prod_mul_distrib]
  have h (j : J) : ∑ z, star ((A j : Matrix (κ j) (κ j) ℂ) z (x j)) *
      (A j : Matrix (κ j) (κ j) ℂ) z (y j) = if x j = y j then 1 else 0 := by
    exact congrFun (congrFun (A j).property.1 (x j)) (y j)
  trans ∏ j : J, ∑ z : κ j, star ((A j : Matrix (κ j) (κ j) ℂ) z (x j)) *
    (A j : Matrix (κ j) (κ j) ℂ) z (y j)
  · exact (Fintype.prod_sum (fun (j : J) (z : κ j) => star ((A j : Matrix (κ j) (κ j) ℂ) z (x j)) * (A j : Matrix (κ j) (κ j) ℂ) z (y j))).symm
  simp_rw [h]
  by_cases hxy : x = y
  · subst y
    simp
  · obtain ⟨j,hj⟩ := Function.ne_iff.mp hxy
    rw [Matrix.one_apply_ne hxy]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hj]

theorem contraction_covariant {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (A : Matrix α α ℂ) (B : Matrix.unitaryGroup β ℂ)
    (T : Matrix α β ℂ) (x : β → ℂ) :
    (A * T * (B : Matrix β β ℂ)ᵀ) *ᵥ star ((B : Matrix β β ℂ) *ᵥ x) =
      A *ᵥ (T *ᵥ star x) := by
  have hb : (B : Matrix β β ℂ)ᵀ * ((B : Matrix β β ℂ).map star) = 1 := by
    ext i j
    have h := congrArg star (congrFun (congrFun B.property.1 i) j)
    simpa only [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
      star_sum,star_mul,star_star,Matrix.transpose_apply,Matrix.map_apply,
      Matrix.one_apply,apply_ite,star_one,star_zero,mul_comm] using h
  have hs : star ((B : Matrix β β ℂ) *ᵥ x) = ((B : Matrix β β ℂ).map star) *ᵥ star x := by
    funext i
    simp [Matrix.mulVec,dotProduct,star_sum,star_mul,mul_comm]
  rw [hs,Matrix.mulVec_mulVec,Matrix.mul_assoc, hb,Matrix.mul_one,← Matrix.mulVec_mulVec]

def productVector {J : Type*} [Fintype J] {κ : J → Type*}
    (x : (j : J) → κ j → ℂ) : ((j : J) → κ j) → ℂ := fun v => ∏ j, x j (v j)

theorem productMatrix_mulVec {J : Type*} [Fintype J] [DecidableEq J]
    {κ : J → Type*} [∀ j, Fintype (κ j)]
    (A : (j : J) → Matrix (κ j) (κ j) ℂ) (x : (j : J) → κ j → ℂ) :
    productMatrix A *ᵥ productVector x = productVector (fun j => A j *ᵥ x j) := by
  funext v
  simp only [productMatrix,productVector,Matrix.mulVec,dotProduct,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (j : J) (w : κ j) => A j (v j) w * x j w)).symm

theorem tensorAct_matrix {n : ℕ} {κ : Fin (n+1) → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (A : (j : Fin (n+1)) → Matrix (κ j) (κ j) ℂ)
    (T : ((j : Fin (n+1)) → κ j) → ℂ) (a : κ 0) (v : (j : Fin n) → κ j.succ) :
    tensorProdAct A T (Fin.cons a v) =
      ((A 0 * (Matrix.of (fun b w => T (Fin.cons b w)) : Matrix (κ 0) ((j : Fin n) → κ j.succ) ℂ) : Matrix (κ 0) ((j : Fin n) → κ j.succ) ℂ) *
        (productMatrix (fun j : Fin n => A j.succ))ᵀ) a v := by
  unfold tensorProdAct
  rw [← (Fin.consEquiv κ).sum_comp (fun w => (∏ j, A j (Fin.cons a v j) (w j)) * T w)]
  simp only [Fintype.sum_prod_type,Fin.consEquiv_apply,Fin.prod_univ_succ,
    Fin.cons_zero,Fin.cons_succ,Matrix.mul_apply,Matrix.transpose_apply,Matrix.of_apply,productMatrix,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro b hb
  change (A 0 a b * ∏ j, A j.succ (v j) (w j)) * T (Fin.cons b w) = _
  ring

def tensorContract {n : ℕ} {κ : Fin (n+1) → Type*}
    [∀ j, Fintype (κ j)] (T : ((j : Fin (n+1)) → κ j) → ℂ)
    (h : (j : Fin n) → κ j.succ → ℂ) : κ 0 → ℂ :=
  fun a => ∑ v, T (Fin.cons a v) * ∏ j, star (h j (v j))

theorem tensorContract_eq_matrix {n : ℕ} {κ : Fin (n+1) → Type*}
    [∀ j, Fintype (κ j)] (T : ((j : Fin (n+1)) → κ j) → ℂ)
    (h : (j : Fin n) → κ j.succ → ℂ) :
    tensorContract T h = (fun a v => T (Fin.cons a v)) *ᵥ star (productVector h) := by
  funext a
  simp [tensorContract,productVector,Matrix.mulVec,dotProduct,star_prod]

theorem tensorContract_equivariant {n : ℕ} {κ : Fin (n+1) → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (A : (j : Fin (n+1)) → Matrix.unitaryGroup (κ j) ℂ)
    (T : ((j : Fin (n+1)) → κ j) → ℂ) (h : (j : Fin n) → κ j.succ → ℂ) :
    tensorContract (tensorProdAct (fun j => (A j : Matrix (κ j) (κ j) ℂ)) T)
      (fun j => (A j.succ : Matrix (κ j.succ) (κ j.succ) ℂ) *ᵥ h j) =
      (A 0 : Matrix (κ 0) (κ 0) ℂ) *ᵥ tensorContract T h := by
  rw [tensorContract_eq_matrix,tensorContract_eq_matrix]
  simp_rw [tensorAct_matrix]
  rw [← productMatrix_mulVec]
  exact contraction_covariant (A 0 : Matrix (κ 0) (κ 0) ℂ)
    (⟨productMatrix (fun j : Fin n => (A j.succ : Matrix (κ j.succ) (κ j.succ) ℂ)),
      productMatrix_unitary (fun j : Fin n => A j.succ)⟩ : Matrix.unitaryGroup ((j : Fin n) → κ j.succ) ℂ)
    (Matrix.of (fun a v => T (Fin.cons a v)) : Matrix (κ 0) ((j : Fin n) → κ j.succ) ℂ) (productVector h)

end Queelius.UniteEquivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open Matrix Finset OrbNetEqui.Equivariance

theorem block_tensor_restriction {d N : ℕ} {ι : Fin d → Type*}
    [∀ u, Fintype (ι u)] [∀ u, DecidableEq (ι u)]
    (A : (u : Fin d) → Matrix (ι u) (ι u) ℂ)
    (T : (Fin N → Orb ι) → ℂ) (uvec : Fin N → Fin d)
    (v : (j : Fin N) → ι (uvec j)) :
    diagAct (Matrix.blockDiagonal' A) T (fun j => ⟨uvec j,v j⟩) =
      tensorProdAct (fun j => A (uvec j)) (fun w => T (fun j => ⟨uvec j,w j⟩)) v := by
  let e : ((j : Fin N) → ι (uvec j)) → (Fin N → Orb ι) := fun w j => ⟨uvec j,w j⟩
  have he : Function.Injective e := by
    intro x y h
    funext j
    exact Sigma.mk.inj_iff.mp (congrFun h j) |>.2 |> eq_of_heq
  unfold diagAct tensorProdAct
  symm
  apply Fintype.sum_of_injective e he
  · intro x hx
    have hn : ∃ j, (x j).1 ≠ uvec j := by
      by_contra hn
      push_neg at hn
      apply hx
      refine ⟨fun j => hn j ▸ (x j).2, ?_⟩
      funext j
      dsimp [e]
      apply Sigma.ext (hn j).symm
      exact eqRec_heq (hn j) ((x j).2)
    obtain ⟨j,hj⟩ := hn
    have hz : (∏ l, Matrix.blockDiagonal' A ⟨uvec l,v l⟩ (x l)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      exact Matrix.blockDiagonal'_apply_ne A (v j) (x j).2 hj.symm
    rw [hz,zero_mul]
  · intro w
    simp [e,Matrix.blockDiagonal'_apply_eq]

end Queelius.UniteEquivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance.Controls
open Matrix

theorem phase_contraction_control :
    (((1 : Matrix (Fin 1) (Fin 1) ℂ) * !![(2 : ℂ)] *
      (phaseUnitary : Matrix (Fin 1) (Fin 1) ℂ)ᵀ) *ᵥ
      star ((phaseUnitary : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ ![(3 : ℂ)])) 0 = 6 := by
  rw [contraction_covariant]
  norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_one]

theorem omitting_conjugation_fails :
    (((1 : Matrix (Fin 1) (Fin 1) ℂ) * !![(2 : ℂ)] *
      (phaseUnitary : Matrix (Fin 1) (Fin 1) ℂ)ᵀ) *ᵥ
      ((phaseUnitary : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ ![(3 : ℂ)])) 0 = -6 := by
  norm_num [phaseUnitary,Matrix.mul_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_one]
  ring_nf
  simp [Complex.I_sq]

theorem nonunitary_contraction_fails :
    (((1 : Matrix (Fin 1) (Fin 1) ℂ) * !![(2 : ℂ)] * !![(2 : ℂ)]ᵀ) *ᵥ
      star (!![(2 : ℂ)] *ᵥ ![(3 : ℂ)])) 0 = 24 ∧
    ((1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ (!![(2 : ℂ)] *ᵥ star ![(3 : ℂ)])) 0 = 6 := by
  constructor <;> norm_num [Matrix.mul_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_one]

end Queelius.UniteEquivariance.Controls

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open Matrix Finset OrbNetEqui.Equivariance
open scoped MonoidAlgebra
variable {K ι : Type*} [Group K] [Fintype ι] [DecidableEq ι]

def matrixRepresentation (ρ : K →* Matrix.unitaryGroup ι ℂ) :
    Representation ℂ K (EuclideanSpace ℂ ι) where
  toFun g := Matrix.toEuclideanLin (ρ g : Matrix ι ι ℂ)
  map_one' := by
    ext x i
    simp [Matrix.toEuclideanLin_apply]
  map_mul' := by
    intro g h
    ext x i
    simp [Matrix.toEuclideanLin_apply,Matrix.mulVec_mulVec]

theorem matrixRepresentation_inner (ρ : K →* Matrix.unitaryGroup ι ℂ)
    (g : K) (x y : EuclideanSpace ℂ ι) :
    inner ℂ (matrixRepresentation ρ g x) (matrixRepresentation ρ g y) = inner ℂ x y := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct]
  conv_lhs => rw [dotProduct_comm]
  conv_rhs => rw [dotProduct_comm]
  change star ((ρ g : Matrix ι ι ℂ) *ᵥ WithLp.ofLp x) ⬝ᵥ
    ((ρ g : Matrix ι ι ℂ) *ᵥ WithLp.ofLp y) = star (WithLp.ofLp x) ⬝ᵥ WithLp.ofLp y
  rw [Matrix.star_mulVec,← Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec,
    ← Matrix.star_eq_conjTranspose,Matrix.UnitaryGroup.star_mul_self,Matrix.one_mulVec]

theorem matrix_representation_semisimple (ρ : K →* Matrix.unitaryGroup ι ℂ) :
    Representation.IsSemisimpleRepresentation (matrixRepresentation ρ) :=
  unitary_representation_semisimple _ (matrixRepresentation_inner ρ)

theorem matrix_module_semisimple (ρ : K →* Matrix.unitaryGroup ι ℂ) :
    IsSemisimpleModule ℂ[K] (matrixRepresentation ρ).asModule :=
  unitary_module_semisimple _ (matrixRepresentation_inner ρ)

theorem matrix_finite_simple_decomposition (ρ : K →* Matrix.unitaryGroup ι ℂ) :
    ∃ (n : ℕ) (S : Fin n → Submodule ℂ[K] (matrixRepresentation ρ).asModule)
      (_ : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[K]] Π₀ i : Fin n, S i),
      ∀ i, IsSimpleModule ℂ[K] (S i) :=
  unitary_finite_simple_decomposition _ (matrixRepresentation_inner ρ)

theorem productMatrix_one {J : Type*} [Fintype J] [DecidableEq J]
    {κ : J → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] :
    productMatrix (fun j => (1 : Matrix (κ j) (κ j) ℂ)) = 1 := by
  ext x y
  simp only [productMatrix,Matrix.one_apply]
  by_cases hxy : x=y
  · subst y
    simp
  · obtain ⟨j,hj⟩ := Function.ne_iff.mp hxy
    rw [if_neg hxy]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

theorem productMatrix_mul {J : Type*} [Fintype J] [DecidableEq J]
    {κ : J → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (A B : (j : J) → Matrix (κ j) (κ j) ℂ) :
    productMatrix (fun j => A j * B j) = productMatrix A * productMatrix B := by
  ext x y
  simp only [productMatrix,Matrix.mul_apply,← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun j z => A j (x j) z * B j z (y j))

def tensorRepresentation {J : Type*} [Fintype J] [DecidableEq J]
    {κ : J → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (U : (j : J) → K →* Matrix.unitaryGroup (κ j) ℂ) :
    K →* Matrix.unitaryGroup ((j : J) → κ j) ℂ where
  toFun g := ⟨productMatrix (fun j => (U j g : Matrix (κ j) (κ j) ℂ)),
    productMatrix_unitary (fun j => U j g)⟩
  map_one' := by
    apply Subtype.ext
    simpa using (productMatrix_one (κ:=κ))
  map_mul' := by
    intro g h
    apply Subtype.ext
    simpa using productMatrix_mul (fun j => (U j g : Matrix (κ j) (κ j) ℂ))
      (fun j => (U j h : Matrix (κ j) (κ j) ℂ))

theorem tensor_representation_action {N : ℕ} {κ : Fin N → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (U : (j : Fin N) → K →* Matrix.unitaryGroup (κ j) ℂ) (g : K)
    (T : ((j : Fin N) → κ j) → ℂ) :
    ((tensorRepresentation U g : Matrix ((j : Fin N) → κ j) ((j : Fin N) → κ j) ℂ) *ᵥ T) =
      tensorProdAct (fun j => (U j g : Matrix (κ j) (κ j) ℂ)) T := rfl

end Queelius.UniteEquivariance

end

section
noncomputable section
namespace OrbNetEqui.Equivariance

open Matrix

theorem blockConv_equivariant {K : Type*} [Group K] {d n : ℕ} {ι : Fin d → Type*}
    [∀ u, Fintype (ι u)] [∀ u, DecidableEq (ι u)] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {dim : Λ → ℕ} {nmax I : ℕ} {Kmul : Fin d → Λ → ℕ}
    (S : Fin d → Subgroup K)
    (π₁ : (u : Fin d) → K →* Matrix.unitaryGroup (ι u) ℂ)
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (D : (u : Fin d) → Matrix (ι u) (MIdx dim Kmul u) ℂ)
    (W : (u : Fin d) → Fin I → (L : Λ) → Matrix (Fin (Kmul u L)) (Fin nmax) ℂ)
    (hD : ∀ u, ∀ k ∈ S u, D u * π₂mat U Kmul u k = (π₁ u k : Matrix (ι u) (ι u) ℂ) * D u)
    (g : Fin d → K) (hg : ∀ u, g u ∈ S u)
    (T : (Fin (n + 1) → Orb ι) → ℂ) (h : Fin d → Feature Λ dim nmax)
    (uvec : Fin (n + 1) → Fin d) (i : Fin I) :
    blockConv D W (tensorAct π₁ g T) (fun u => featAct U (g u) (h u)) uvec i =
      (π₁ (uvec 0) (g (uvec 0)) : Matrix (ι (uvec 0)) (ι (uvec 0)) ℂ) *ᵥ
        blockConv D W T h uvec i := by
  let A : (j : Fin (n+1)) → Matrix.unitaryGroup (ι (uvec j)) ℂ := fun j => π₁ (uvec j) (g (uvec j))
  have ht (v : (j : Fin (n+1)) → ι (uvec j)) :
      tensorAct π₁ g T (fun j => ⟨uvec j,v j⟩) =
      tensorProdAct (fun j => (A j : Matrix (ι (uvec j)) (ι (uvec j)) ℂ))
        (fun w => T (fun j => ⟨uvec j,w j⟩)) v :=
    Queelius.UniteEquivariance.block_tensor_restriction (fun u => (π₁ u (g u) : Matrix (ι u) (ι u) ℂ)) T uvec v
  have hm (u : Fin d) := Queelius.UniteEquivariance.matching_equivariant U D W u i (g u)
    (π₁ u (g u) : Matrix (ι u) (ι u) ℂ) (hD u (g u) (hg u)) (h u)
  change Queelius.UniteEquivariance.tensorContract
    (fun v => tensorAct π₁ g T (fun j => ⟨uvec j,v j⟩))
    (fun j => matching D W (uvec j.succ) i (featAct U (g (uvec j.succ)) (h (uvec j.succ)))) =
    (A 0 : Matrix (ι (uvec 0)) (ι (uvec 0)) ℂ) *ᵥ
      Queelius.UniteEquivariance.tensorContract (fun v => T (fun j => ⟨uvec j,v j⟩))
        (fun j => matching D W (uvec j.succ) i (h (uvec j.succ)))
  simp_rw [ht,hm]
  exact Queelius.UniteEquivariance.tensorContract_equivariant A _ _

end OrbNetEqui.Equivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open scoped MonoidAlgebra
open Finset
variable {K E : Type*} [Group K] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem simple_decomposition_dimension (ρ : Representation ℂ K E)
    {n : ℕ} (S : Fin n → Submodule ℂ[K] ρ.asModule)
    (e : ρ.asModule ≃ₗ[ℂ[K]] Π₀ i : Fin n, S i)
    (hs : ∀ i, IsSimpleModule ℂ[K] (S i)) :
    (∑ i, Module.finrank ℂ (S i)) = Module.finrank ℂ E ∧ n ≤ Module.finrank ℂ E := by
  letI (i : Fin n) : Module.Finite ℂ (S i) :=
    Module.Finite.of_injective ((S i).subtype.restrictScalars ℂ) (S i).subtype_injective
  have he := (e.restrictScalars ℂ).finrank_eq
  have hd := (DFinsupp.linearEquivFunOnFintype (R := ℂ) (M := fun i => S i)).finrank_eq
  rw [hd, Module.finrank_pi_fintype] at he
  have hdim : (∑ i, Module.finrank ℂ (S i)) = Module.finrank ℂ E :=
    he.symm.trans ρ.asModuleEquiv.finrank_eq
  refine ⟨hdim, ?_⟩
  rw [← hdim]
  calc n = ∑ _i : Fin n, 1 := by simp
       _ ≤ ∑ i : Fin n, Module.finrank ℂ (S i) := by
         apply Finset.sum_le_sum
         intro i _
         letI := hs i
         letI := IsSimpleModule.nontrivial ℂ[K] (S i)
         exact Module.finrank_pos

theorem unitary_finite_simple_decomposition_bound (ρ : Representation ℂ K E)
    (hu : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y) :
    ∃ (n : ℕ) (S : Fin n → Submodule ℂ[K] ρ.asModule)
      (_ : ρ.asModule ≃ₗ[ℂ[K]] Π₀ i : Fin n, S i),
      (∀ i, IsSimpleModule ℂ[K] (S i)) ∧
      (∑ i, Module.finrank ℂ (S i)) = Module.finrank ℂ E ∧ n ≤ Module.finrank ℂ E := by
  obtain ⟨n,S,e,hs⟩ := unitary_finite_simple_decomposition ρ hu
  exact ⟨n,S,e,hs,simple_decomposition_dimension ρ S e hs⟩

theorem tensor_finite_simple_decomposition_bound {J : Type*} [Fintype J] [DecidableEq J]
    {κ : J → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (U : (j : J) → K →* Matrix.unitaryGroup (κ j) ℂ) :
    ∃ (n : ℕ) (S : Fin n → Submodule ℂ[K] (matrixRepresentation (tensorRepresentation U)).asModule)
      (_ : (matrixRepresentation (tensorRepresentation U)).asModule ≃ₗ[ℂ[K]] Π₀ i : Fin n, S i),
      (∀ i, IsSimpleModule ℂ[K] (S i)) ∧
      (∑ i, Module.finrank ℂ (S i)) = (∏ j, Fintype.card (κ j)) ∧
      n ≤ (∏ j, Fintype.card (κ j)) := by
  simpa using unitary_finite_simple_decomposition_bound
    (matrixRepresentation (tensorRepresentation U)) (matrixRepresentation_inner _)

end Queelius.UniteEquivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open Matrix Finset OrbNetEqui.Equivariance
variable {K Λ : Type*} [Group K] {dim : Λ → ℕ} {r : ℕ}

theorem labelRep_unitary (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (lab : Fin r → Λ) (k : K) :
    labelRep U lab k ∈ Matrix.unitaryGroup (Σ a : Fin r, Fin (dim (lab a))) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (labelRep U lab k)ᴴ * labelRep U lab k = 1
  unfold labelRep
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  have h : ∀ a : Fin r, (U (lab a) k : Matrix (Fin (dim (lab a))) (Fin (dim (lab a))) ℂ)ᴴ * (U (lab a) k : Matrix (Fin (dim (lab a))) (Fin (dim (lab a))) ℂ) = 1 := by
    intro a
    exact (U (lab a) k).property.1
  simp_rw [h]
  exact Matrix.blockDiagonal'_one

def labelRepresentation (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (lab : Fin r → Λ) : K →* Matrix.unitaryGroup (Σ a : Fin r, Fin (dim (lab a))) ℂ where
  toFun k := ⟨labelRep U lab k, labelRep_unitary U lab k⟩
  map_one' := by
    apply Subtype.ext
    simp only [labelRep,map_one,OneMemClass.coe_one]
    exact Matrix.blockDiagonal'_one
  map_mul' := by
    intro g h
    apply Subtype.ext
    simp [labelRep,Matrix.blockDiagonal'_mul]

theorem label_tensor_representation_action
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (lab : Fin r → Λ) (N : ℕ) (g : K)
    (T : (Fin N → Σ a : Fin r, Fin (dim (lab a))) → ℂ) :
    ((tensorRepresentation (fun _ : Fin N => labelRepresentation U lab) g : Matrix _ _ ℂ) *ᵥ T) =
      diagAct (labelRep U lab g) T := rfl

end Queelius.UniteEquivariance

end

section
noncomputable section
namespace OrbNetEqui.Equivariance

open Matrix

theorem messagePassing_equivariant {K : Type*} [Group K] {d n : ℕ} {ι : Fin d → Type*}
    [∀ u, Fintype (ι u)] [∀ u, DecidableEq (ι u)] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {dim : Λ → ℕ} {nmax I J : ℕ} {Kmul : Fin d → Λ → ℕ}
    (S : Fin d → Subgroup K)
    (π₁ : (u : Fin d) → K →* Matrix.unitaryGroup (ι u) ℂ)
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (D : (u : Fin d) → Matrix (ι u) (MIdx dim Kmul u) ℂ)
    (W : (u : Fin d) → Fin I → (L : Λ) → Matrix (Fin (Kmul u L)) (Fin nmax) ℂ)
    (Wd : (u : Fin d) → (L : Λ) → Matrix (Fin nmax) (Fin (Kmul u L) × Fin I × Fin J) ℂ)
    (hD : ∀ u, ∀ k ∈ S u, D u * π₂mat U Kmul u k = (π₁ u k : Matrix (ι u) (ι u) ℂ) * D u)
    (g : Fin d → K) (hg : ∀ u, g u ∈ S u)
    (T : (Fin (n + 1) → Orb ι) → ℂ) (h : Fin d → Feature Λ dim nmax)
    (α : (Fin (n + 1) → Fin d) → Fin J → ℂ) (u : Fin d) :
    aggregate D W (tensorAct π₁ g T) (fun w => featAct U (g w) (h w)) α u =
        (fun ij => (π₁ u (g u) : Matrix (ι u) (ι u) ℂ) *ᵥ aggregate D W T h α u ij) ∧
      revMatching D Wd u (aggregate D W (tensorAct π₁ g T) (fun w => featAct U (g w) (h w)) α u) =
        featAct U (g u) (revMatching D Wd u (aggregate D W T h α u)) := by
  have ha : aggregate D W (tensorAct π₁ g T) (fun w => featAct U (g w) (h w)) α u =
      (fun ij => (π₁ u (g u) : Matrix (ι u) (ι u) ℂ) *ᵥ aggregate D W T h α u ij) := by
    funext ij v
    simp only [aggregate,blockConv_equivariant S π₁ U D W hD g hg,Fin.cons_zero]
    simp only [Matrix.mulVec,dotProduct,aggregate,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro ur hur
    change ((π₁ u (g u) : Matrix (ι u) (ι u) ℂ) v ur *
      blockConv D W T h (Fin.cons u b) ij.1 ur) * α (Fin.cons u b) ij.2 =
      (π₁ u (g u) : Matrix (ι u) (ι u) ℂ) v ur *
        (blockConv D W T h (Fin.cons u b) ij.1 ur * α (Fin.cons u b) ij.2)
    ring
  refine ⟨ha,?_⟩
  rw [ha]
  exact Queelius.UniteEquivariance.reverseMatching_equivariant U D Wd u (g u) (π₁ u (g u))
    (hD u (g u) (hg u)) _

end OrbNetEqui.Equivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open Matrix Finset OrbNetEqui.Equivariance
open scoped MonoidAlgebra
variable {K E : Type*} [Group K] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

def representationEquiv (ρ : Representation ℂ K E) (g : K) : E ≃ₗ[ℂ] E where
  toLinearMap := ρ g
  invFun := ρ g⁻¹
  left_inv := by intro x; simpa using representation_inverse_apply ρ g⁻¹ x
  right_inv := representation_inverse_apply ρ g

def representationIsometry (ρ : Representation ℂ K E)
    (hu : ∀ g x y, inner ℂ (ρ g x) (ρ g y)=inner ℂ x y) (g : K) : E ≃ₗᵢ[ℂ] E :=
  (representationEquiv ρ g).isometryOfInner (hu g)

def coordinateRepresentation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Representation ℂ K E) (hu : ∀ g x y, inner ℂ (ρ g x) (ρ g y)=inner ℂ x y)
    (b : OrthonormalBasis ι ℂ E) : K →* Matrix.unitaryGroup ι ℂ where
  toFun g := ⟨LinearMap.toMatrix b.toBasis b.toBasis (ρ g),
    (representationIsometry ρ hu g).toMatrix_mem_unitaryGroup b b⟩
  map_one' := by
    apply Subtype.ext
    simpa using (LinearMap.toMatrixAlgEquiv b.toBasis).map_one
  map_mul' := by
    intro g h
    apply Subtype.ext
    change LinearMap.toMatrix b.toBasis b.toBasis (ρ (g*h)) = _
    rw [map_mul]
    exact (LinearMap.toMatrixAlgEquiv b.toBasis).map_mul (ρ g) (ρ h)

def coordinateEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) : E ≃ₗ[ℂ] (ι → ℂ) :=
  b.toBasis.equivFun

theorem coordinate_intertwining {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Representation ℂ K E) (hu : ∀ g x y, inner ℂ (ρ g x) (ρ g y)=inner ℂ x y)
    (b : OrthonormalBasis ι ℂ E) (g : K) (x : E) :
    coordinateEquiv b (ρ g x) = (coordinateRepresentation ρ hu b g : Matrix ι ι ℂ) *ᵥ
      coordinateEquiv b x := by
  exact (LinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis (ρ g) x).symm

theorem coordinate_irreducible (ρ : Representation ℂ K E)
    (hu : ∀ g x y, inner ℂ (ρ g x) (ρ g y)=inner ℂ x y)
    (hi : Representation.IsIrreducible ρ) [Nontrivial E]
    (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) :
    IsIrreducibleUnitary (coordinateRepresentation ρ hu b) := by
  letI := hi
  refine ⟨Module.finrank_pos,?_⟩
  intro W hW
  let Z : Subrepresentation ρ :=
    { toSubmodule := W.comap (coordinateEquiv b).toLinearMap
      apply_mem_toSubmodule := by
        intro g x hx
        change coordinateEquiv b (ρ g x) ∈ W
        rw [coordinate_intertwining]
        exact hW g _ hx }
  have hz : Z=⊥ ∨ Z=⊤ := eq_bot_or_eq_top Z
  rcases hz with hz | hz
  · left
    apply le_antisymm _ bot_le
    intro y hy
    have hx : (coordinateEquiv b).symm y ∈ Z := by
      change coordinateEquiv b ((coordinateEquiv b).symm y) ∈ W
      simpa using hy
    rw [hz] at hx
    have he : (coordinateEquiv b).symm y=0 := hx
    exact (coordinateEquiv b).symm.map_eq_zero_iff.mp he
  · right
    apply top_unique
    intro y hy
    have hx : (coordinateEquiv b).symm y ∈ Z := by rw [hz]; trivial
    change coordinateEquiv b ((coordinateEquiv b).symm y) ∈ W at hx
    simpa using hx

theorem irreducible_catalogue_match {Λ : Type*} {dim : Λ → ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ) (hc : CatalogComplete U)
    (ρ : Representation ℂ K E) (hu : ∀ g x y, inner ℂ (ρ g x) (ρ g y)=inner ℂ x y)
    (hi : Representation.IsIrreducible ρ) [Nontrivial E] :
    ∃ L, ∃ e : E ≃ₗ[ℂ] (Fin (dim L) → ℂ),
      ∀ g x, e (ρ g x) = (U L g : Matrix _ _ ℂ) *ᵥ e x := by
  let b := stdOrthonormalBasis ℂ E
  obtain ⟨L,e,he⟩ := hc _ (coordinateRepresentation ρ hu b) (coordinate_irreducible ρ hu hi b)
  refine ⟨L,(coordinateEquiv b).trans e,?_⟩
  intro g x
  change e (coordinateEquiv b (ρ g x)) = _
  rw [coordinate_intertwining ρ hu b,he]
  rfl

end Queelius.UniteEquivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance.Controls
open Matrix Finset OrbNetEqui.Equivariance
open scoped MonoidAlgebra

def shear : Matrix (Fin 2) (Fin 2) ℂ := !![1,1;0,1]

theorem shear_preserves_first_axis (x : ℂ) : shear *ᵥ ![x,0] = ![x,0] := by
  ext i
  fin_cases i <;> simp [shear,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem shear_fails_orthogonal_preservation :
    star (![(1 : ℂ),0]) ⬝ᵥ ![(0 : ℂ),1] = 0 ∧
    star (shear *ᵥ ![(1 : ℂ),0]) ⬝ᵥ (shear *ᵥ ![(0 : ℂ),1]) = 1 := by
  constructor <;> norm_num [shear,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem zero_dimensional_copies_not_injective :
    ¬ Function.Injective (multiplicityEmbedding (μ := fun _ : Unit => 1)
      (dim := fun _ : Unit => 0) (Finset.univ : Finset Unit)) := by
  intro h
  have he : multiplicityEmbedding (μ := fun _ : Unit => 1) (dim := fun _ : Unit => 0)
      Finset.univ (fun _ => (0 : ℂ)) = multiplicityEmbedding Finset.univ (fun _ => (1 : ℂ)) := by
    ext L ν M
    exact Fin.elim0 M
  have he' := congrFun (h he) ⟨⟨(),Finset.mem_univ ()⟩,0⟩
  norm_num at he'

theorem zero_space_has_no_simple_summands {K : Type*} [Group K]
    (ρ : Representation ℂ K (EuclideanSpace ℂ (Fin 0)))
    {n : ℕ} (S : Fin n → Submodule ℂ[K] ρ.asModule)
    (e : ρ.asModule ≃ₗ[ℂ[K]] Π₀ i : Fin n, S i)
    (hs : ∀ i, IsSimpleModule ℂ[K] (S i)) : n = 0 := by
  have h := (simple_decomposition_dimension ρ S e hs).2
  simpa using h

end Queelius.UniteEquivariance.Controls

end

section
noncomputable section
namespace OrbNetEqui.Equivariance

open Matrix

theorem unite_equivariant {K : Type*} [Group K] {d n : ℕ} {ι : Fin d → Type*}
    [∀ u, Fintype (ι u)] [∀ u, DecidableEq (ι u)] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {dim : Λ → ℕ} {nmax I J : ℕ} {Kmul : Fin d → Λ → ℕ}
    (S : Fin d → Subgroup K)
    (π₁ : (u : Fin d) → K →* Matrix.unitaryGroup (ι u) ℂ)
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (D : (u : Fin d) → Matrix (ι u) (MIdx dim Kmul u) ℂ)
    (θ : UniteParams d n ι Λ dim nmax Kmul I J)
    (hD : ∀ u, ∀ k ∈ S u, D u * π₂mat U Kmul u k = (π₁ u k : Matrix (ι u) (ι u) ℂ) * D u)
    (hC : ∀ (t : ℕ) (u : Fin d), ∀ k ∈ S u, ∀ (c : Fin nmax) (L₁ L₂ L : Λ),
      (θ.P t).C c L₁ L₂ L * Matrix.kroneckerMap (· * ·)
          (U L₁ k : Matrix (Fin (dim L₁)) (Fin (dim L₁)) ℂ)
          (U L₂ k : Matrix (Fin (dim L₂)) (Fin (dim L₂)) ℂ) =
        (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) * (θ.P t).C c L₁ L₂ L)
    (hψ : ∀ u, ∀ k ∈ S u, ∀ (T : (Fin (n + 1) → ι u) → ℂ) (L : Λ) (ν : Fin (θ.μd u L)),
      θ.ψ u (diagAct (π₁ u k : Matrix (ι u) (ι u) ℂ) T) L ν =
        (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ θ.ψ u T L ν)
    (hα : ∀ (t : ℕ) (g : Fin d → K), (∀ u, g u ∈ S u) →
      ∀ (T : (Fin (n + 1) → Orb ι) → ℂ) (h : Fin d → Feature Λ dim nmax),
        θ.α t (tensorAct π₁ g T) (fun u => featAct U (g u) (h u)) = θ.α t T h)
    (hβ : ∀ (t : ℕ) (L : Λ) (c : Fin nmax), 0 < (θ.P t).βh L c ∧ 0 < (θ.P t).βq L c)
    (hε : 0 < θ.ε)
    (g : Fin d → K) (hg : ∀ u, g u ∈ S u) (T : (Fin (n + 1) → Orb ι) → ℂ) (u : Fin d) :
    unite θ D (tensorAct π₁ g T) u = featAct U (g u) (unite θ D T u) := by
  have hdg (v : Fin d) : diagBlock (tensorAct π₁ g T) v =
      diagAct (π₁ v (g v) : Matrix (ι v) (ι v) ℂ) (diagBlock T v) := by
    funext x
    exact Queelius.UniteEquivariance.block_tensor_restriction
      (fun v => (π₁ v (g v) : Matrix (ι v) (ι v) ℂ)) T (fun _ => v) x
  have h0 : diagReduce θ (tensorAct π₁ g T) =
      fun v => featAct U (g v) (diagReduce θ T v) := by
    funext v L c M
    simp only [diagReduce,hdg]
    simp_rw [hψ v (g v) (hg v)]
    simp only [featAct,Matrix.mulVec,dotProduct,diagReduce,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro M' hM
    apply Finset.sum_congr rfl
    intro ν hν
    ring
  have hf (t : ℕ) : fullSteps θ D (tensorAct π₁ g T) t =
      fun v => featAct U (g v) (fullSteps θ D T t v) := by
    induction t with
    | zero => exact h0
    | succ t ih =>
      funext v
      simp only [fullSteps]
      rw [ih,hα t g hg T (fullSteps θ D T t)]
      rw [(messagePassing_equivariant S π₁ U D (θ.W t) (θ.Wd t) hD g hg T
        (fullSteps θ D T t) (θ.α t T (fullSteps θ D T t)) v).2]
      exact pointwise_equivariant U (θ.P t) θ.ε (hβ t) hε (g v)
        (hC t v (g v) (hg v)) _ _
  have hl (h : Fin d → Feature Λ dim nmax) (s : ℕ) :
      localSteps θ (fun v => featAct U (g v) (h v)) s =
      fun v => featAct U (g v) (localSteps θ h s v) := by
    induction s with
    | zero => rfl
    | succ s ih =>
      funext v
      simp only [localSteps,ih]
      exact pointwise_equivariant U (θ.P (θ.t₁+s)) θ.ε (hβ (θ.t₁+s)) hε (g v)
        (hC (θ.t₁+s) v (g v) (hg v)) _ _
  unfold unite
  rw [hf,hl]

end OrbNetEqui.Equivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open scoped MonoidAlgebra
open Matrix OrbNetEqui.Equivariance
variable {K E : Type*} [Group K] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

set_option backward.isDefEq.respectTransparency false in
def simpleSubspaceModuleEquiv (ρ : Representation ℂ K E)
    (S : Submodule ℂ[K] ρ.asModule) :
    (Subrepresentation.ofSubmodule' S).toRepresentation.asModule ≃ₗ[ℂ[K]] S where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    apply Subtype.ext
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add c d hc hd => 
      simp only [RingHom.id_apply,add_smul] at *
      exact congrArg₂ (fun (a b : ρ.asModule) => a+b) hc hd
    | single g a =>
      rw [Representation.single_smul]
      change a • ρ g x.val = ((MonoidAlgebra.single g a) • (show ρ.asModule from x.val) : ρ.asModule)
      rw [Representation.single_smul]
      rfl

 theorem simple_subspace_irreducible (ρ : Representation ℂ K E)
    (S : Submodule ℂ[K] ρ.asModule) [IsSimpleModule ℂ[K] S] :
    Representation.IsIrreducible (Subrepresentation.ofSubmodule' S).toRepresentation := by
  apply (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
  exact (simpleSubspaceModuleEquiv ρ S).isSimpleModule_iff.mpr inferInstance

 theorem simple_subspace_unitary (ρ : Representation ℂ K E)
    (hu : ∀ g x y, inner ℂ (ρ g x) (ρ g y)=inner ℂ x y)
    (S : Submodule ℂ[K] ρ.asModule) :
    ∀ g (x y : (Subrepresentation.ofSubmodule' S).toSubmodule),
      inner ℂ ((Subrepresentation.ofSubmodule' S).toRepresentation g x)
        ((Subrepresentation.ofSubmodule' S).toRepresentation g y) = inner ℂ x y := by
  intro g x y
  exact hu g x.val y.val

set_option backward.isDefEq.respectTransparency false in
def simpleSubspaceEquiv (ρ : Representation ℂ K E)
    (S : Submodule ℂ[K] ρ.asModule) :
    S ≃ₗ[ℂ] (Subrepresentation.ofSubmodule' S).toSubmodule where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem simple_catalogue_match {Λ : Type*} {dim : Λ → ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ) (hc : CatalogComplete U)
    (ρ : Representation ℂ K E) (hu : ∀ g x y, inner ℂ (ρ g x) (ρ g y)=inner ℂ x y)
    (S : Submodule ℂ[K] ρ.asModule) [IsSimpleModule ℂ[K] S] :
    ∃ L, ∃ e : S ≃ₗ[ℂ] (Fin (dim L) → ℂ),
      ∀ g x, e ((MonoidAlgebra.single g (1 : ℂ)) • x) = (U L g : Matrix _ _ ℂ) *ᵥ e x := by
  let W := Subrepresentation.ofSubmodule' S
  letI : Nontrivial S := IsSimpleModule.nontrivial ℂ[K] S
  letI : Nontrivial W.toSubmodule := (simpleSubspaceEquiv ρ S).injective.nontrivial
  obtain ⟨L,e,he⟩ := irreducible_catalogue_match U hc W.toRepresentation
    (simple_subspace_unitary ρ hu S) (simple_subspace_irreducible ρ S)
  refine ⟨L,(simpleSubspaceEquiv ρ S).trans e,?_⟩
  intro g x
  change e (simpleSubspaceEquiv ρ S ((MonoidAlgebra.single g (1 : ℂ)) • x)) = _
  have hx : simpleSubspaceEquiv ρ S ((MonoidAlgebra.single g (1 : ℂ)) • x) =
      W.toRepresentation g (simpleSubspaceEquiv ρ S x) := by
    apply Subtype.ext
    change ((MonoidAlgebra.single g (1 : ℂ)) • (x : ρ.asModule) : ρ.asModule) = ρ g x.val
    rw [Representation.single_smul,one_smul]
    rfl
  rw [hx,he]
  rfl

end Queelius.UniteEquivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open scoped MonoidAlgebra
open Matrix OrbNetEqui.Equivariance
variable {K E : Type*} [Group K] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

 theorem unitary_indexed_catalogue_decomposition {Λ : Type*} {dim : Λ → ℕ}
    (U : (L : Λ) → K →* unitaryGroup (Fin (dim L)) ℂ) (hc : CatalogComplete U)
    (ρ : Representation ℂ K E) (hu : ∀ g x y, inner ℂ (ρ g x) (ρ g y)=inner ℂ x y) :
    ∃ (n : ℕ) (lab : Fin n → Λ) (e : E ≃ₗ[ℂ] ((i : Fin n) → Fin (dim (lab i)) → ℂ)),
      (∀ g x i, e (ρ g x) i = (U (lab i) g : Matrix _ _ ℂ) *ᵥ e x i) ∧
      (∑ i, dim (lab i)) = Module.finrank ℂ E := by
  classical
  obtain ⟨n,S,e,hs⟩ := unitary_finite_simple_decomposition ρ hu
  have hm : ∀ i, ∃ L, ∃ f : S i ≃ₗ[ℂ] (Fin (dim L) → ℂ),
      ∀ g x, f ((MonoidAlgebra.single g (1 : ℂ)) • x) = (U L g : Matrix _ _ ℂ) *ᵥ f x := by
    intro i
    letI := hs i
    exact simple_catalogue_match U hc ρ hu (S i)
  choose lab f hf using hm
  let e₀ := ρ.asModuleEquiv.symm.trans ((e.restrictScalars ℂ).trans
    (DFinsupp.linearEquivFunOnFintype (R:=ℂ) (M:=fun i => S i)))
  let e₁ := e₀.trans (LinearEquiv.piCongrRight f)
  refine ⟨n,lab,e₁,?_,?_⟩
  · intro g x i
    have hx : ρ.asModuleEquiv.symm (ρ g x) =
        MonoidAlgebra.single g (1 : ℂ) • ρ.asModuleEquiv.symm x := by
      rw [Representation.single_smul,one_smul]
      rfl
    change f i ((e (ρ.asModuleEquiv.symm (ρ g x))) i) = _
    rw [hx,e.map_smul]
    exact hf i g _
  · have h := e₁.finrank_eq
    simpa [Module.finrank_pi,Module.finrank_pi_fintype] using h.symm

 theorem unitary_catalogue_decomposition {Λ : Type*} {dim : Λ → ℕ}
    (U : (L : Λ) → K →* unitaryGroup (Fin (dim L)) ℂ) (hc : CatalogComplete U)
    (ρ : Representation ℂ K E) (hu : ∀ g x y, inner ℂ (ρ g x) (ρ g y)=inner ℂ x y) :
    ∃ (μ : Λ → ℕ) (s : Finset Λ), (∀ L, L ∉ s → μ L = 0) ∧
      ∃ e : E ≃ₗ[ℂ] ((L : Λ) → Fin (μ L) → Fin (dim L) → ℂ),
        ∀ g x L ν, e (ρ g x) L ν = (U L g : Matrix _ _ ℂ) *ᵥ e x L ν := by
  obtain ⟨n,lab,e,he,hd⟩ := unitary_indexed_catalogue_decomposition U hc ρ hu
  obtain ⟨s,hs⟩ := labelMultiplicity_support lab
  refine ⟨labelMultiplicity lab,s,hs,e.trans (catalogueGroupEquiv lab dim),?_⟩
  intro g x L ν
  change catalogueGroupEquiv lab dim (e (ρ g x)) L ν = _
  have h : e (ρ g x) = fun i => (U (lab i) g : Matrix _ _ ℂ) *ᵥ e x i := funext (he g x)
  rw [h]
  exact catalogueGroup_intertwining lab dim U g (e x) L ν

 theorem unitary_catalogue_decomposition_dimension {Λ : Type*} {dim : Λ → ℕ}
    (U : (L : Λ) → K →* unitaryGroup (Fin (dim L)) ℂ) (hc : CatalogComplete U)
    (ρ : Representation ℂ K E) (hu : ∀ g x y, inner ℂ (ρ g x) (ρ g y)=inner ℂ x y) :
    ∃ (μ : Λ → ℕ) (s : Finset Λ), (∀ L, L ∉ s → μ L = 0) ∧
      (∃ e : E ≃ₗ[ℂ] ((L : Λ) → Fin (μ L) → Fin (dim L) → ℂ),
        ∀ g x L ν, e (ρ g x) L ν = (U L g : Matrix _ _ ℂ) *ᵥ e x L ν) ∧
      (∑ L ∈ s, μ L * dim L) = Module.finrank ℂ E := by
  classical
  obtain ⟨n,lab,e,he,hd⟩ := unitary_indexed_catalogue_decomposition U hc ρ hu
  refine ⟨labelMultiplicity lab,Finset.univ.image lab,labelMultiplicity_outside_image lab,
    ⟨e.trans (catalogueGroupEquiv lab dim),?_⟩,(labelMultiplicity_dimension lab dim).trans hd⟩
  intro g x L ν
  change catalogueGroupEquiv lab dim (e (ρ g x)) L ν = _
  have h : e (ρ g x) = fun i => (U (lab i) g : Matrix _ _ ℂ) *ᵥ e x i := funext (he g x)
  rw [h]
  exact catalogueGroup_intertwining lab dim U g (e x) L ν

end Queelius.UniteEquivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open Matrix OrbNetEqui.Equivariance

 theorem matrix_catalogue_decomposition {K Λ ι : Type*} [Group K] [Fintype ι] [DecidableEq ι]
    {dim : Λ → ℕ} (U : (L : Λ) → K →* unitaryGroup (Fin (dim L)) ℂ)
    (hc : CatalogComplete U) (ρ : K →* unitaryGroup ι ℂ) :
    ∃ (μ : Λ → ℕ) (s : Finset Λ), (∀ L, L ∉ s → μ L = 0) ∧
      (∃ e : (ι → ℂ) ≃ₗ[ℂ] ((L : Λ) → Fin (μ L) → Fin (dim L) → ℂ),
        ∀ g x L ν, e ((ρ g : Matrix _ _ ℂ) *ᵥ x) L ν = (U L g : Matrix _ _ ℂ) *ᵥ e x L ν) ∧
      (∑ L ∈ s, μ L * dim L) = Fintype.card ι := by
  obtain ⟨μ,s,hs,⟨e,he⟩,hd⟩ := unitary_catalogue_decomposition_dimension U hc
    (matrixRepresentation ρ) (matrixRepresentation_inner ρ)
  refine ⟨μ,s,hs,⟨(WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.trans e,?_⟩,?_⟩
  · intro g x L ν
    exact he g (WithLp.toLp 2 x) L ν
  · simpa using hd

end Queelius.UniteEquivariance

end

section
namespace OrbNetEqui.Equivariance

open Matrix

theorem theorem_S1 {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (hirr : ∀ L, IsIrreducibleUnitary (U L)) (hcat : CatalogComplete U)
    {N : ℕ} (Ls : Fin N → Λ) :
    ∃ (μ : Λ → ℕ) (s : Finset Λ), (∀ L, L ∉ s → μ L = 0) ∧
      (∃ ψ : (((j : Fin N) → Fin (dim (Ls j))) → ℂ) ≃ₗ[ℂ]
          ((L : Λ) → Fin (μ L) → Fin (dim L) → ℂ),
        ∀ (k : K) (T : ((j : Fin N) → Fin (dim (Ls j))) → ℂ) (L : Λ) (ν : Fin (μ L)),
          ψ (tensorProdAct (fun j => (U (Ls j) k : Matrix (Fin (dim (Ls j))) (Fin (dim (Ls j))) ℂ)) T)
              L ν =
            (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ ψ T L ν) ∧
      ∑ L ∈ s, μ L * dim L = ∏ j, dim (Ls j) := by
  classical
  simpa [Fintype.card_pi, Fintype.card_fin, Queelius.UniteEquivariance.tensor_representation_action] using
    Queelius.UniteEquivariance.matrix_catalogue_decomposition U hcat
      (Queelius.UniteEquivariance.tensorRepresentation (fun j => U (Ls j)))

end OrbNetEqui.Equivariance

namespace OrbNetEqui.Equivariance

open Matrix

theorem corollary_S2 {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (hirr : ∀ L, IsIrreducibleUnitary (U L)) (hcat : CatalogComplete U)
    {r : ℕ} (lab : Fin r → Λ) (N : ℕ) :
    ∃ (μ : Λ → ℕ) (s : Finset Λ), (∀ L, L ∉ s → μ L = 0) ∧
      ∃ ψ : ((Fin N → Σ a : Fin r, Fin (dim (lab a))) → ℂ) ≃ₗ[ℂ]
          ((L : Λ) → Fin (μ L) → Fin (dim L) → ℂ),
        ∀ (k : K) (T : (Fin N → Σ a : Fin r, Fin (dim (lab a))) → ℂ) (L : Λ) (ν : Fin (μ L)),
          ψ (diagAct (labelRep U lab k) T) L ν =
            (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ ψ T L ν := by
  classical
  obtain ⟨μ,s,hs,⟨e,he⟩,hd⟩ := Queelius.UniteEquivariance.matrix_catalogue_decomposition U hcat
    (Queelius.UniteEquivariance.tensorRepresentation
      (fun _ : Fin N => Queelius.UniteEquivariance.labelRepresentation U lab))
  exact ⟨μ,s,hs,e,he⟩

end OrbNetEqui.Equivariance

namespace OrbNetEqui.Equivariance

open Matrix

theorem corollary_S3 {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (hirr : ∀ L, IsIrreducibleUnitary (U L)) (hcat : CatalogComplete U)
    {r : ℕ} (lab : Fin r → Λ) (N : ℕ) :
    ∃ (μ : Λ → ℕ) (s : Finset Λ), (∀ L, L ∉ s → μ L = 0) ∧
      ∃ Q : (L : Λ) → Fin (μ L) → Fin (dim L) → (Fin N → Σ a : Fin r, Fin (dim (lab a))) → ℂ,
        Function.Injective (coeffMap Q) ∧
        ∑ L ∈ s, μ L ≤ Fintype.card (Σ a : Fin r, Fin (dim (lab a))) ^ N ∧
        ∀ (k : K) (T : (Fin N → Σ a : Fin r, Fin (dim (lab a))) → ℂ) (L : Λ) (ν : Fin (μ L)),
          coeffMap Q (diagAct (labelRep U lab k) T) L ν =
            (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ coeffMap Q T L ν := by
  classical
  obtain ⟨μ,s,hs,e,he⟩ := corollary_S2 U hirr hcat lab N
  obtain ⟨Q,hQ,hb,hinter⟩ := Queelius.UniteEquivariance.coefficient_reduction_of_decomposition
    U hirr (labelRep U lab) s hs e he
  exact ⟨μ,s,hs,Q,hQ,hb,hinter⟩

end OrbNetEqui.Equivariance


end

section
namespace Queelius.UniteEquivariance.Controls
open Queelius.UniteEquivariance

 theorem repeated_label_multiplicity :
    labelMultiplicity (fun _ : Fin 2 => (0 : ℕ)) 0 = 2 := by
  simp [labelMultiplicity]

 theorem unused_label_multiplicity :
    labelMultiplicity (fun _ : Fin 2 => (0 : ℕ)) 1 = 0 := by
  simp [labelMultiplicity]

 theorem empty_decomposition_multiplicity (L : ℕ) :
    labelMultiplicity (fun i : Fin 0 => Fin.elim0 i) L = 0 := by
  simp [labelMultiplicity]

 theorem grouping_preserves_distinct_repeated_copies :
    catalogueGroupEquiv (fun _ : Fin 2 => (0 : ℕ)) (fun _ => 1)
      (fun i _ => if i = 0 then (1 : ℂ) else 0) ≠
    catalogueGroupEquiv (fun _ : Fin 2 => (0 : ℕ)) (fun _ => 1)
      (fun i _ => if i = 1 then (1 : ℂ) else 0) := by
  intro h
  have hx := (catalogueGroupEquiv (fun _ : Fin 2 => (0 : ℕ)) (fun _ => 1)).injective h
  have hz := congrFun (congrFun hx (0 : Fin 2)) (0 : Fin 1)
  norm_num at hz

end Queelius.UniteEquivariance.Controls

end

universe audit_u0 audit_u1 audit_u2

theorem solution : (
  ∀ {K : Type audit_u0} [inst : Group K] {d n : Nat} {ι : Fin d → Type audit_u1} [inst_1 : (u : Fin d) → Fintype (ι u)]
    [inst_2 : (u : Fin d) → DecidableEq (ι u)] {Λ : Type audit_u2} [inst_3 : Fintype Λ] [inst_4 : DecidableEq Λ]
    {dim : Λ → Nat} {nmax I J : Nat} {Kmul : Fin d → Λ → Nat} (S : Fin d → @Subgroup K inst)
    (π₁ :
      (u : Fin d) →
        @MonoidHom K
          (@Subtype (Matrix (ι u) (ι u) Complex) fun (x : Matrix (ι u) (ι u) Complex) =>
            @Membership.mem (Matrix (ι u) (ι u) Complex)
              (@Submonoid (Matrix (ι u) (ι u) Complex)
                (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                  (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                    (@Matrix.semiring (ι u) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)) (inst_1 u)
                      (inst_2 u)))))
              (@SetLike.instMembership
                (@Submonoid (Matrix (ι u) (ι u) Complex)
                  (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                    (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                      (@Matrix.semiring (ι u) Complex
                        (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)) (inst_1 u)
                        (inst_2 u)))))
                (Matrix (ι u) (ι u) Complex)
                (@Submonoid.instSetLike (Matrix (ι u) (ι u) Complex)
                  (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                    (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                      (@Matrix.semiring (ι u) Complex
                        (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)) (inst_1 u)
                        (inst_2 u))))))
              (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing Complex.instStarRing) x)
          (@MulOneClass.toMulOne K (@Monoid.toMulOneClass K (@DivInvMonoid.toMonoid K (@Group.toDivInvMonoid K inst))))
          (@MulOneClass.toMulOne
            (@Subtype (Matrix (ι u) (ι u) Complex) fun (x : Matrix (ι u) (ι u) Complex) =>
              @Membership.mem (Matrix (ι u) (ι u) Complex)
                (@Submonoid (Matrix (ι u) (ι u) Complex)
                  (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                    (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                      (@Matrix.semiring (ι u) Complex
                        (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)) (inst_1 u)
                        (inst_2 u)))))
                (@SetLike.instMembership
                  (@Submonoid (Matrix (ι u) (ι u) Complex)
                    (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                      (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                        (@Matrix.semiring (ι u) Complex
                          (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                          (inst_1 u) (inst_2 u)))))
                  (Matrix (ι u) (ι u) Complex)
                  (@Submonoid.instSetLike (Matrix (ι u) (ι u) Complex)
                    (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                      (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                        (@Matrix.semiring (ι u) Complex
                          (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                          (inst_1 u) (inst_2 u))))))
                (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing Complex.instStarRing) x)
            (@Submonoid.toMulOneClass (Matrix (ι u) (ι u) Complex)
              (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                  (@Matrix.semiring (ι u) Complex
                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)) (inst_1 u)
                    (inst_2 u))))
              (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing Complex.instStarRing))))
    (U :
      (L : Λ) →
        @MonoidHom K
          (@Subtype (Matrix (Fin (dim L)) (Fin (dim L)) Complex) fun (x : Matrix (Fin (dim L)) (Fin (dim L)) Complex) =>
            @Membership.mem (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
              (@Submonoid (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                (@MulZeroOneClass.toMulOneClass (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                  (@instMulZeroOneClassOfSemiring (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                    (@Matrix.semiring (Fin (dim L)) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                      (Fin.fintype (dim L)) (instDecidableEqFin (dim L))))))
              (@SetLike.instMembership
                (@Submonoid (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                  (@MulZeroOneClass.toMulOneClass (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                    (@instMulZeroOneClassOfSemiring (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                      (@Matrix.semiring (Fin (dim L)) Complex
                        (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                        (Fin.fintype (dim L)) (instDecidableEqFin (dim L))))))
                (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                (@Submonoid.instSetLike (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                  (@MulZeroOneClass.toMulOneClass (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                    (@instMulZeroOneClassOfSemiring (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                      (@Matrix.semiring (Fin (dim L)) Complex
                        (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                        (Fin.fintype (dim L)) (instDecidableEqFin (dim L)))))))
              (@Matrix.unitaryGroup (Fin (dim L)) (instDecidableEqFin (dim L)) (Fin.fintype (dim L)) Complex
                Complex.commRing Complex.instStarRing)
              x)
          (@MulOneClass.toMulOne K (@Monoid.toMulOneClass K (@DivInvMonoid.toMonoid K (@Group.toDivInvMonoid K inst))))
          (@MulOneClass.toMulOne
            (@Subtype (Matrix (Fin (dim L)) (Fin (dim L)) Complex) fun (x : Matrix (Fin (dim L)) (Fin (dim L)) Complex) =>
              @Membership.mem (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                (@Submonoid (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                  (@MulZeroOneClass.toMulOneClass (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                    (@instMulZeroOneClassOfSemiring (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                      (@Matrix.semiring (Fin (dim L)) Complex
                        (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                        (Fin.fintype (dim L)) (instDecidableEqFin (dim L))))))
                (@SetLike.instMembership
                  (@Submonoid (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                    (@MulZeroOneClass.toMulOneClass (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                      (@instMulZeroOneClassOfSemiring (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                        (@Matrix.semiring (Fin (dim L)) Complex
                          (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                          (Fin.fintype (dim L)) (instDecidableEqFin (dim L))))))
                  (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                  (@Submonoid.instSetLike (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                    (@MulZeroOneClass.toMulOneClass (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                      (@instMulZeroOneClassOfSemiring (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                        (@Matrix.semiring (Fin (dim L)) Complex
                          (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                          (Fin.fintype (dim L)) (instDecidableEqFin (dim L)))))))
                (@Matrix.unitaryGroup (Fin (dim L)) (instDecidableEqFin (dim L)) (Fin.fintype (dim L)) Complex
                  Complex.commRing Complex.instStarRing)
                x)
            (@Submonoid.toMulOneClass (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
              (@MulZeroOneClass.toMulOneClass (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                (@instMulZeroOneClassOfSemiring (Matrix (Fin (dim L)) (Fin (dim L)) Complex)
                  (@Matrix.semiring (Fin (dim L)) Complex
                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                    (Fin.fintype (dim L)) (instDecidableEqFin (dim L)))))
              (@Matrix.unitaryGroup (Fin (dim L)) (instDecidableEqFin (dim L)) (Fin.fintype (dim L)) Complex
                Complex.commRing Complex.instStarRing))))
    (D : (u : Fin d) → Matrix (ι u) (@OrbNetEqui.Equivariance.MIdx Λ dim d Kmul u) Complex)
    (W : (u : Fin d) → Fin I → (L : Λ) → Matrix (Fin (Kmul u L)) (Fin nmax) Complex)
    (Wd : (u : Fin d) → (L : Λ) → Matrix (Fin nmax) (Prod (Fin (Kmul u L)) (Prod (Fin I) (Fin J))) Complex),
    (∀ (u : Fin d) (k : K),
        @Membership.mem K (@Subgroup K inst) (@SetLike.instMembership (@Subgroup K inst) K (@Subgroup.instSetLike K inst))
            (S u) k →
          @Eq (Matrix (ι u) (@OrbNetEqui.Equivariance.MIdx Λ dim d Kmul u) Complex)
            (@HMul.hMul (Matrix (ι u) (@OrbNetEqui.Equivariance.MIdx Λ dim d Kmul u) Complex)
              (Matrix (@OrbNetEqui.Equivariance.MIdx Λ dim d Kmul u) (@OrbNetEqui.Equivariance.MIdx Λ dim d Kmul u)
                Complex)
              (Matrix (ι u) (@OrbNetEqui.Equivariance.MIdx Λ dim d Kmul u) Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (ι u) (@OrbNetEqui.Equivariance.MIdx Λ dim d Kmul u)
                (@OrbNetEqui.Equivariance.MIdx Λ dim d Kmul u) Complex
                (@Sigma.instFintype Λ (fun (L : Λ) => Prod (Fin (Kmul u L)) (Fin (dim L)))
                  (fun (i : Λ) =>
                    @instFintypeProd (Fin (Kmul u i)) (Fin (dim i)) (Fin.fintype (Kmul u i)) (Fin.fintype (dim i)))
                  inst_3)
                Complex.instMul Complex.instAddCommMonoid)
              (D u) (@OrbNetEqui.Equivariance.π₂mat K inst Λ inst_4 dim d U Kmul u k))
            (@HMul.hMul (Matrix (ι u) (ι u) Complex) (Matrix (ι u) (@OrbNetEqui.Equivariance.MIdx Λ dim d Kmul u) Complex)
              (Matrix (ι u) (@OrbNetEqui.Equivariance.MIdx Λ dim d Kmul u) Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (ι u) (ι u) (@OrbNetEqui.Equivariance.MIdx Λ dim d Kmul u)
                Complex (inst_1 u) Complex.instMul Complex.instAddCommMonoid)
              (@Subtype.val (Matrix (ι u) (ι u) Complex)
                (fun (x : Matrix (ι u) (ι u) Complex) =>
                  @Membership.mem (Matrix (ι u) (ι u) Complex)
                    (@Submonoid (Matrix (ι u) (ι u) Complex)
                      (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                        (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                          (@Matrix.semiring (ι u) Complex
                            (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                            (inst_1 u) (inst_2 u)))))
                    (@SetLike.instMembership
                      (@Submonoid (Matrix (ι u) (ι u) Complex)
                        (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                          (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                            (@Matrix.semiring (ι u) Complex
                              (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                              (inst_1 u) (inst_2 u)))))
                      (Matrix (ι u) (ι u) Complex)
                      (@Submonoid.instSetLike (Matrix (ι u) (ι u) Complex)
                        (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                          (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                            (@Matrix.semiring (ι u) Complex
                              (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                              (inst_1 u) (inst_2 u))))))
                    (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing Complex.instStarRing) x)
                (@DFunLike.coe
                  (@MonoidHom K
                    (@Subtype (Matrix (ι u) (ι u) Complex) fun (x : Matrix (ι u) (ι u) Complex) =>
                      @Membership.mem (Matrix (ι u) (ι u) Complex)
                        (@Submonoid (Matrix (ι u) (ι u) Complex)
                          (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                            (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                              (@Matrix.semiring (ι u) Complex
                                (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                (inst_1 u) (inst_2 u)))))
                        (@SetLike.instMembership
                          (@Submonoid (Matrix (ι u) (ι u) Complex)
                            (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                              (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                (@Matrix.semiring (ι u) Complex
                                  (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                  (inst_1 u) (inst_2 u)))))
                          (Matrix (ι u) (ι u) Complex)
                          (@Submonoid.instSetLike (Matrix (ι u) (ι u) Complex)
                            (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                              (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                (@Matrix.semiring (ι u) Complex
                                  (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                  (inst_1 u) (inst_2 u))))))
                        (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing Complex.instStarRing)
                        x)
                    (@MulOneClass.toMulOne K
                      (@Monoid.toMulOneClass K (@DivInvMonoid.toMonoid K (@Group.toDivInvMonoid K inst))))
                    (@MulOneClass.toMulOne
                      (@Subtype (Matrix (ι u) (ι u) Complex) fun (x : Matrix (ι u) (ι u) Complex) =>
                        @Membership.mem (Matrix (ι u) (ι u) Complex)
                          (@Submonoid (Matrix (ι u) (ι u) Complex)
                            (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                              (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                (@Matrix.semiring (ι u) Complex
                                  (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                  (inst_1 u) (inst_2 u)))))
                          (@SetLike.instMembership
                            (@Submonoid (Matrix (ι u) (ι u) Complex)
                              (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                  (@Matrix.semiring (ι u) Complex
                                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                    (inst_1 u) (inst_2 u)))))
                            (Matrix (ι u) (ι u) Complex)
                            (@Submonoid.instSetLike (Matrix (ι u) (ι u) Complex)
                              (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                  (@Matrix.semiring (ι u) Complex
                                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                    (inst_1 u) (inst_2 u))))))
                          (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing Complex.instStarRing)
                          x)
                      (@Submonoid.toMulOneClass (Matrix (ι u) (ι u) Complex)
                        (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                          (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                            (@Matrix.semiring (ι u) Complex
                              (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                              (inst_1 u) (inst_2 u))))
                        (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing
                          Complex.instStarRing))))
                  K
                  (fun (x : K) =>
                    @Subtype (Matrix (ι u) (ι u) Complex) fun (x : Matrix (ι u) (ι u) Complex) =>
                      @Membership.mem (Matrix (ι u) (ι u) Complex)
                        (@Submonoid (Matrix (ι u) (ι u) Complex)
                          (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                            (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                              (@Matrix.semiring (ι u) Complex
                                (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                (inst_1 u) (inst_2 u)))))
                        (@SetLike.instMembership
                          (@Submonoid (Matrix (ι u) (ι u) Complex)
                            (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                              (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                (@Matrix.semiring (ι u) Complex
                                  (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                  (inst_1 u) (inst_2 u)))))
                          (Matrix (ι u) (ι u) Complex)
                          (@Submonoid.instSetLike (Matrix (ι u) (ι u) Complex)
                            (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                              (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                (@Matrix.semiring (ι u) Complex
                                  (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                  (inst_1 u) (inst_2 u))))))
                        (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing Complex.instStarRing)
                        x)
                  (@MonoidHom.instFunLike K
                    (@Subtype (Matrix (ι u) (ι u) Complex) fun (x : Matrix (ι u) (ι u) Complex) =>
                      @Membership.mem (Matrix (ι u) (ι u) Complex)
                        (@Submonoid (Matrix (ι u) (ι u) Complex)
                          (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                            (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                              (@Matrix.semiring (ι u) Complex
                                (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                (inst_1 u) (inst_2 u)))))
                        (@SetLike.instMembership
                          (@Submonoid (Matrix (ι u) (ι u) Complex)
                            (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                              (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                (@Matrix.semiring (ι u) Complex
                                  (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                  (inst_1 u) (inst_2 u)))))
                          (Matrix (ι u) (ι u) Complex)
                          (@Submonoid.instSetLike (Matrix (ι u) (ι u) Complex)
                            (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                              (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                (@Matrix.semiring (ι u) Complex
                                  (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                  (inst_1 u) (inst_2 u))))))
                        (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing Complex.instStarRing)
                        x)
                    (@MulOneClass.toMulOne K
                      (@Monoid.toMulOneClass K (@DivInvMonoid.toMonoid K (@Group.toDivInvMonoid K inst))))
                    (@MulOneClass.toMulOne
                      (@Subtype (Matrix (ι u) (ι u) Complex) fun (x : Matrix (ι u) (ι u) Complex) =>
                        @Membership.mem (Matrix (ι u) (ι u) Complex)
                          (@Submonoid (Matrix (ι u) (ι u) Complex)
                            (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                              (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                (@Matrix.semiring (ι u) Complex
                                  (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                  (inst_1 u) (inst_2 u)))))
                          (@SetLike.instMembership
                            (@Submonoid (Matrix (ι u) (ι u) Complex)
                              (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                  (@Matrix.semiring (ι u) Complex
                                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                    (inst_1 u) (inst_2 u)))))
                            (Matrix (ι u) (ι u) Complex)
                            (@Submonoid.instSetLike (Matrix (ι u) (ι u) Complex)
                              (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                  (@Matrix.semiring (ι u) Complex
                                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                    (inst_1 u) (inst_2 u))))))
                          (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing Complex.instStarRing)
                          x)
                      (@Submonoid.toMulOneClass (Matrix (ι u) (ι u) Complex)
                        (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                          (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                            (@Matrix.semiring (ι u) Complex
                              (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                              (inst_1 u) (inst_2 u))))
                        (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing
                          Complex.instStarRing))))
                  (π₁ u) k))
              (D u))) →
      ∀ (g : Fin d → K),
        (∀ (u : Fin d),
            @Membership.mem K (@Subgroup K inst)
              (@SetLike.instMembership (@Subgroup K inst) K (@Subgroup.instSetLike K inst)) (S u) (g u)) →
          ∀
            (T :
              (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                  @OrbNetEqui.Equivariance.Orb d ι) →
                Complex)
            (h : Fin d → OrbNetEqui.Equivariance.Feature Λ dim nmax)
            (α :
              (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                  Fin d) →
                Fin J → Complex)
            (u : Fin d),
            And
              (@Eq (Prod (Fin I) (Fin J) → ι u → Complex)
                (@OrbNetEqui.Equivariance.aggregate Λ inst_3 dim d n nmax I J Kmul ι inst_1 D W
                  (@OrbNetEqui.Equivariance.tensorAct K inst d n ι inst_1 inst_2 π₁ g T)
                  (fun (w : Fin d) => @OrbNetEqui.Equivariance.featAct K inst Λ dim nmax U (g w) (h w)) α u)
                fun (ij : Prod (Fin I) (Fin J)) =>
                @Matrix.mulVec (ι u) (ι u) Complex
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                  (inst_1 u)
                  (@Subtype.val (Matrix (ι u) (ι u) Complex)
                    (fun (x : Matrix (ι u) (ι u) Complex) =>
                      @Membership.mem (Matrix (ι u) (ι u) Complex)
                        (@Submonoid (Matrix (ι u) (ι u) Complex)
                          (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                            (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                              (@Matrix.semiring (ι u) Complex
                                (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                (inst_1 u) (inst_2 u)))))
                        (@SetLike.instMembership
                          (@Submonoid (Matrix (ι u) (ι u) Complex)
                            (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                              (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                (@Matrix.semiring (ι u) Complex
                                  (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                  (inst_1 u) (inst_2 u)))))
                          (Matrix (ι u) (ι u) Complex)
                          (@Submonoid.instSetLike (Matrix (ι u) (ι u) Complex)
                            (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                              (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                (@Matrix.semiring (ι u) Complex
                                  (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                  (inst_1 u) (inst_2 u))))))
                        (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing Complex.instStarRing)
                        x)
                    (@DFunLike.coe
                      (@MonoidHom K
                        (@Subtype (Matrix (ι u) (ι u) Complex) fun (x : Matrix (ι u) (ι u) Complex) =>
                          @Membership.mem (Matrix (ι u) (ι u) Complex)
                            (@Submonoid (Matrix (ι u) (ι u) Complex)
                              (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                  (@Matrix.semiring (ι u) Complex
                                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                    (inst_1 u) (inst_2 u)))))
                            (@SetLike.instMembership
                              (@Submonoid (Matrix (ι u) (ι u) Complex)
                                (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                  (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                    (@Matrix.semiring (ι u) Complex
                                      (@CommSemiring.toSemiring Complex
                                        (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (inst_1 u) (inst_2 u)))))
                              (Matrix (ι u) (ι u) Complex)
                              (@Submonoid.instSetLike (Matrix (ι u) (ι u) Complex)
                                (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                  (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                    (@Matrix.semiring (ι u) Complex
                                      (@CommSemiring.toSemiring Complex
                                        (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (inst_1 u) (inst_2 u))))))
                            (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing
                              Complex.instStarRing)
                            x)
                        (@MulOneClass.toMulOne K
                          (@Monoid.toMulOneClass K (@DivInvMonoid.toMonoid K (@Group.toDivInvMonoid K inst))))
                        (@MulOneClass.toMulOne
                          (@Subtype (Matrix (ι u) (ι u) Complex) fun (x : Matrix (ι u) (ι u) Complex) =>
                            @Membership.mem (Matrix (ι u) (ι u) Complex)
                              (@Submonoid (Matrix (ι u) (ι u) Complex)
                                (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                  (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                    (@Matrix.semiring (ι u) Complex
                                      (@CommSemiring.toSemiring Complex
                                        (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (inst_1 u) (inst_2 u)))))
                              (@SetLike.instMembership
                                (@Submonoid (Matrix (ι u) (ι u) Complex)
                                  (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                    (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                      (@Matrix.semiring (ι u) Complex
                                        (@CommSemiring.toSemiring Complex
                                          (@CommRing.toCommSemiring Complex Complex.commRing))
                                        (inst_1 u) (inst_2 u)))))
                                (Matrix (ι u) (ι u) Complex)
                                (@Submonoid.instSetLike (Matrix (ι u) (ι u) Complex)
                                  (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                    (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                      (@Matrix.semiring (ι u) Complex
                                        (@CommSemiring.toSemiring Complex
                                          (@CommRing.toCommSemiring Complex Complex.commRing))
                                        (inst_1 u) (inst_2 u))))))
                              (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing
                                Complex.instStarRing)
                              x)
                          (@Submonoid.toMulOneClass (Matrix (ι u) (ι u) Complex)
                            (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                              (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                (@Matrix.semiring (ι u) Complex
                                  (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                  (inst_1 u) (inst_2 u))))
                            (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing
                              Complex.instStarRing))))
                      K
                      (fun (x : K) =>
                        @Subtype (Matrix (ι u) (ι u) Complex) fun (x : Matrix (ι u) (ι u) Complex) =>
                          @Membership.mem (Matrix (ι u) (ι u) Complex)
                            (@Submonoid (Matrix (ι u) (ι u) Complex)
                              (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                  (@Matrix.semiring (ι u) Complex
                                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                    (inst_1 u) (inst_2 u)))))
                            (@SetLike.instMembership
                              (@Submonoid (Matrix (ι u) (ι u) Complex)
                                (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                  (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                    (@Matrix.semiring (ι u) Complex
                                      (@CommSemiring.toSemiring Complex
                                        (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (inst_1 u) (inst_2 u)))))
                              (Matrix (ι u) (ι u) Complex)
                              (@Submonoid.instSetLike (Matrix (ι u) (ι u) Complex)
                                (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                  (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                    (@Matrix.semiring (ι u) Complex
                                      (@CommSemiring.toSemiring Complex
                                        (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (inst_1 u) (inst_2 u))))))
                            (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing
                              Complex.instStarRing)
                            x)
                      (@MonoidHom.instFunLike K
                        (@Subtype (Matrix (ι u) (ι u) Complex) fun (x : Matrix (ι u) (ι u) Complex) =>
                          @Membership.mem (Matrix (ι u) (ι u) Complex)
                            (@Submonoid (Matrix (ι u) (ι u) Complex)
                              (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                  (@Matrix.semiring (ι u) Complex
                                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                    (inst_1 u) (inst_2 u)))))
                            (@SetLike.instMembership
                              (@Submonoid (Matrix (ι u) (ι u) Complex)
                                (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                  (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                    (@Matrix.semiring (ι u) Complex
                                      (@CommSemiring.toSemiring Complex
                                        (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (inst_1 u) (inst_2 u)))))
                              (Matrix (ι u) (ι u) Complex)
                              (@Submonoid.instSetLike (Matrix (ι u) (ι u) Complex)
                                (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                  (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                    (@Matrix.semiring (ι u) Complex
                                      (@CommSemiring.toSemiring Complex
                                        (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (inst_1 u) (inst_2 u))))))
                            (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing
                              Complex.instStarRing)
                            x)
                        (@MulOneClass.toMulOne K
                          (@Monoid.toMulOneClass K (@DivInvMonoid.toMonoid K (@Group.toDivInvMonoid K inst))))
                        (@MulOneClass.toMulOne
                          (@Subtype (Matrix (ι u) (ι u) Complex) fun (x : Matrix (ι u) (ι u) Complex) =>
                            @Membership.mem (Matrix (ι u) (ι u) Complex)
                              (@Submonoid (Matrix (ι u) (ι u) Complex)
                                (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                  (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                    (@Matrix.semiring (ι u) Complex
                                      (@CommSemiring.toSemiring Complex
                                        (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (inst_1 u) (inst_2 u)))))
                              (@SetLike.instMembership
                                (@Submonoid (Matrix (ι u) (ι u) Complex)
                                  (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                    (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                      (@Matrix.semiring (ι u) Complex
                                        (@CommSemiring.toSemiring Complex
                                          (@CommRing.toCommSemiring Complex Complex.commRing))
                                        (inst_1 u) (inst_2 u)))))
                                (Matrix (ι u) (ι u) Complex)
                                (@Submonoid.instSetLike (Matrix (ι u) (ι u) Complex)
                                  (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                                    (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                      (@Matrix.semiring (ι u) Complex
                                        (@CommSemiring.toSemiring Complex
                                          (@CommRing.toCommSemiring Complex Complex.commRing))
                                        (inst_1 u) (inst_2 u))))))
                              (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing
                                Complex.instStarRing)
                              x)
                          (@Submonoid.toMulOneClass (Matrix (ι u) (ι u) Complex)
                            (@MulZeroOneClass.toMulOneClass (Matrix (ι u) (ι u) Complex)
                              (@instMulZeroOneClassOfSemiring (Matrix (ι u) (ι u) Complex)
                                (@Matrix.semiring (ι u) Complex
                                  (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                  (inst_1 u) (inst_2 u))))
                            (@Matrix.unitaryGroup (ι u) (inst_2 u) (inst_1 u) Complex Complex.commRing
                              Complex.instStarRing))))
                      (π₁ u) (g u)))
                  (@OrbNetEqui.Equivariance.aggregate Λ inst_3 dim d n nmax I J Kmul ι inst_1 D W T h α u ij))
              (@Eq (OrbNetEqui.Equivariance.Feature Λ dim nmax)
                (@OrbNetEqui.Equivariance.revMatching Λ dim d nmax I J Kmul ι inst_1 D Wd u
                  (@OrbNetEqui.Equivariance.aggregate Λ inst_3 dim d n nmax I J Kmul ι inst_1 D W
                    (@OrbNetEqui.Equivariance.tensorAct K inst d n ι inst_1 inst_2 π₁ g T)
                    (fun (w : Fin d) => @OrbNetEqui.Equivariance.featAct K inst Λ dim nmax U (g w) (h w)) α u))
                (@OrbNetEqui.Equivariance.featAct K inst Λ dim nmax U (g u)
                  (@OrbNetEqui.Equivariance.revMatching Λ dim d nmax I J Kmul ι inst_1 D Wd u
                    (@OrbNetEqui.Equivariance.aggregate Λ inst_3 dim d n nmax I J Kmul ι inst_1 D W T h α u))))
) := @OrbNetEqui.Equivariance.messagePassing_equivariant
