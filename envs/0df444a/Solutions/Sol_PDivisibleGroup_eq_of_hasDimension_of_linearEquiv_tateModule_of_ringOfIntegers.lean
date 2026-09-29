-- Prove2me | solution 1 for PDivisibleGroup.eq_of_hasDimension_of_linearEquiv_tateModule_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0413464d-ba08-5720-a962-0260882560a8

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Theorems.Thm_PDivisibleGroup_exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers
import Theorems.Thm_PadicComplex_eq_zero_of_forall_mem_fixingSubgroup_smul_eq_cyclotomicCharacter_zpow_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_eq_of_hasDimension_of_linearEquiv_tateModule_of_ringOfIntegers
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions PDivisibleGroup.CPoints.instDistribMulAction PrimaryTorsion.instSMul PrimaryTorsion.instModule"
p2m_attr_erase "simp" "PDivisibleGroup.CartierDuality.mk.injEq PDivisibleGroup.CartierDuality.toDualEquiv_apply PDivisibleGroup.CartierDuality.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul PDivisibleGroup.cotangentBaseChange_tmul PDivisibleGroup.baseChange_transition_tmul PDivisibleGroup.cotangentToBaseChange_toCotangent PDivisibleGroup.baseChange_level HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff PDivisibleGroup.cotangentClass_algebraMap PDivisibleGroup.cotangentClass_one"
p2m_attr_erase "simp" "PDivisibleGroup.cpointsProj_cpointsMap PDivisibleGroup.pointsMap_reduceModPow_cpointsProj_succ PDivisibleGroup.cpointsProj_toCPoints PDivisibleGroup.mapModPow_mk PDivisibleGroup.reduceModPow_mk PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map"

set_option autoImplicit false

open scoped TensorProduct
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace Ws47
namespace HTDIM

theorem map_smul_left {k C V V' : Type} [Field k] [CommRing C] [Algebra k C]
    [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
    (f : C →ₐ[k] C) (g : V →ₗ[k] V') (c : C) (w : C ⊗[k] V) :
    TensorProduct.map f.toLinearMap g (c • w) = f c • TensorProduct.map f.toLinearMap g w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul x y =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.smul_tmul']
    simp [smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem baseChange_intertwine {R A M N : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (f : M →ₗ[R] M) (g : N →ₗ[R] N) (h : ∀ x, e (f x) = g (e x)) (w : A ⊗[R] M) :
    LinearEquiv.baseChange R A M N e (f.baseChange A w) = g.baseChange A (LinearEquiv.baseChange R A M N e w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem map_baseChange_intertwine {k C V V' : Type} [Field k] [CommRing C] [Algebra k C]
    [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
    (e : V ≃ₗ[k] V') (φ : C →ₗ[k] C) (f : V →ₗ[k] V) (g : V' →ₗ[k] V') (h : ∀ x, e (f x) = g (e x)) (w : C ⊗[k] V) :
    LinearEquiv.baseChange k C V V' e (TensorProduct.map φ f w) = TensorProduct.map φ g (LinearEquiv.baseChange k C V V' e w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rw [TensorProduct.map_tmul, LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul, TensorProduct.map_tmul, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem card_le_finrank_of_mem {k W : Type} [Field k] [AddCommGroup W] [Module k W]
    {ι : Type} [Fintype ι] (v : ι → W) (hv : LinearIndependent k v) (S : Submodule k W) [FiniteDimensional k S]
    (hS : ∀ i, v i ∈ S) : Fintype.card ι ≤ Module.finrank k S := by
  have hv' : LinearIndependent k (fun i => (⟨v i, hS i⟩ : S)) := by
    rw [linearIndependent_iff'] at hv ⊢
    intro s g hg i hi
    apply hv s g _ i hi
    have := congrArg (Submodule.subtype S) hg
    simpa using this
  exact hv'.fintype_card_le_finrank

theorem core {C W W' S : Type} [Field C] [AddCommGroup W] [Module C W] [AddCommGroup W'] [Module C W']
    {h n n' : ℕ} (hn : n ≤ h) (hn' : n' ≤ h)
    (bG : Module.Basis (Fin h) C W) (bΓ : Module.Basis (Fin h) C W')
    (s : S → C →+* C) (a : S → C)
    (A : S → W →+ W) (A' : S → W' →+ W')
    (hA_smul : ∀ σ (c : C) (x : W), A σ (c • x) = s σ c • A σ x)
    (hbG : ∀ σ i, A σ (bG i) = a σ ^ (if (i : ℕ) < n then 1 else 0) • bG i)
    (hbΓ : ∀ σ j, A' σ (bΓ j) = a σ ^ (if (j : ℕ) < n' then 1 else 0) • bΓ j)
    (E : W' ≃ₗ[C] W) (hE : ∀ σ w, E (A' σ w) = A σ (E w))
    (hvan₁ : ∀ c : C, (∀ σ, s σ c = a σ * c) → c = 0)
    (hvan₂ : ∀ c : C, (∀ σ, s σ c * a σ = c) → c = 0) : n = n' := by
  classical

  have hcoef : ∀ σ (j i : Fin h), s σ (bG.repr (E (bΓ j)) i) * a σ ^ (if (i : ℕ) < n then 1 else 0) =
      a σ ^ (if (j : ℕ) < n' then 1 else 0) * bG.repr (E (bΓ j)) i := by
    intro σ j i
    have h1 : A σ (E (bΓ j)) = a σ ^ (if (j : ℕ) < n' then 1 else 0) • E (bΓ j) := by
      rw [← hE, hbΓ, map_smul]
    have h2 : A σ (E (bΓ j)) = ∑ i, (s σ (bG.repr (E (bΓ j)) i) * a σ ^ (if (i : ℕ) < n then 1 else 0)) • bG i := by
      conv_lhs => rw [← bG.sum_repr (E (bΓ j))]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hA_smul, hbG, smul_smul]
    have h3 := congrArg (fun w => bG.repr w i) (h2.symm.trans h1)
    simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h3
    exact h3
  have hzero₁ : ∀ j i : Fin h, (j : ℕ) < n' → n ≤ (i : ℕ) → bG.repr (E (bΓ j)) i = 0 := by
    intro j i hj hi
    apply hvan₁
    intro σ
    have h := hcoef σ j i
    rwa [if_neg (not_lt.2 hi), if_pos hj, pow_zero, mul_one, pow_one] at h
  have hzero₂ : ∀ j i : Fin h, n' ≤ (j : ℕ) → (i : ℕ) < n → bG.repr (E (bΓ j)) i = 0 := by
    intro j i hj hi
    apply hvan₂
    intro σ
    have h := hcoef σ j i
    rwa [if_pos hi, if_neg (not_lt.2 hj), pow_zero, one_mul, pow_one] at h

  let S₁ : Submodule C W := Submodule.span C (Set.range fun i : Fin n => bG (Fin.castLE hn i))
  let S₂ : Submodule C W := Submodule.span C (Set.range fun i : Fin (h - n) => bG (Fin.cast (by omega) (Fin.natAdd n i)))
  haveI : FiniteDimensional C S₁ := FiniteDimensional.span_of_finite C (Set.finite_range _)
  haveI : FiniteDimensional C S₂ := FiniteDimensional.span_of_finite C (Set.finite_range _)
  have hS₁ : Module.finrank C S₁ ≤ n := by
    refine (finrank_span_le_card (Set.range fun i : Fin n => bG (Fin.castLE hn i))).trans ?_
    rw [Set.toFinset_range]
    exact Finset.card_image_le.trans (by simp)
  have hS₂ : Module.finrank C S₂ ≤ h - n := by
    refine (finrank_span_le_card (Set.range fun i : Fin (h - n) => bG (Fin.cast (by omega) (Fin.natAdd n i)))).trans ?_
    rw [Set.toFinset_range]
    exact Finset.card_image_le.trans (by simp)
  have hmem₁ : ∀ j : Fin h, (j : ℕ) < n' → E (bΓ j) ∈ S₁ := by
    intro j hj
    rw [← bG.sum_repr (E (bΓ j))]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : (i : ℕ) < n
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, ?_⟩)
      show bG _ = bG i
      congr 1
    · rw [hzero₁ j i hj (not_lt.1 hi), zero_smul]; exact Submodule.zero_mem _
  have hmem₂ : ∀ j : Fin h, n' ≤ (j : ℕ) → E (bΓ j) ∈ S₂ := by
    intro j hj
    rw [← bG.sum_repr (E (bΓ j))]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : (i : ℕ) < n
    · rw [hzero₂ j i hj hi, zero_smul]; exact Submodule.zero_mem _
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨(i : ℕ) - n, by omega⟩, ?_⟩)
      show bG _ = bG i
      congr 1
      ext
      simp only [Fin.val_cast, Fin.natAdd_mk]
      omega
  have hind : LinearIndependent C (fun j : Fin h => E (bΓ j)) :=
    bΓ.linearIndependent.map' E.toLinearMap (LinearMap.ker_eq_bot.2 E.injective)
  have hle₁ : n' ≤ n := by
    have hind' : LinearIndependent C (fun j : Fin n' => E (bΓ (Fin.castLE hn' j))) :=
      hind.comp (Fin.castLE hn') (Fin.castLE_injective hn')
    have := card_le_finrank_of_mem _ hind' S₁ (fun j => hmem₁ _ (by simp))
    simpa using this.trans hS₁
  have hle₂ : h - n' ≤ h - n := by
    have hinj : Function.Injective (fun j : Fin (h - n') => (Fin.cast (by omega) (Fin.natAdd n' j) : Fin h)) := by
      intro x y hxy
      simp only [Fin.ext_iff, Fin.val_cast, Fin.val_natAdd] at hxy
      exact Fin.ext (by omega)
    have hind' : LinearIndependent C (fun j : Fin (h - n') => E (bΓ (Fin.cast (by omega) (Fin.natAdd n' j)))) :=
      hind.comp _ hinj
    have := card_le_finrank_of_mem _ hind' S₂ (fun j => hmem₂ _ (by simp))
    simpa using this.trans hS₂
  omega

end Ws47.HTDIM

open Ws47.HTDIM in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G Γ : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) {n n' : ℕ}
    (hn : G.HasDimension n) (hn' : Γ.HasDimension n')
    (e : TateModule p (Γ.Points (PadicAlgCl p)) ≃ₗ[ℤ_[p]] TateModule p (G.Points (PadicAlgCl p)))
    (he : ∀ (τ : PadicAlgCl p ≃ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p) (x : TateModule p (Γ.Points (PadicAlgCl p))),
      e (Γ.tateModuleRep (PadicAlgCl p) τ x) = G.tateModuleRep (PadicAlgCl p) τ (e x)) :
    n = n' := by
  classical
  obtain ⟨hnh, bG, hbG⟩ :=
    PDivisibleGroup.exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers
      p K G hn
  obtain ⟨hn'h, bΓ, hbΓ⟩ :=
    PDivisibleGroup.exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers
      p K Γ hn'

  let L : K.fixingSubgroup → (PadicAlgCl p ≃ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p) := fun σ => PadicAlgCl.ringOfIntegers.galToAlgEquiv p K σ
  have hL : ∀ (σ : K.fixingSubgroup) (x : PadicAlgCl p), L σ x = (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x :=
    fun σ x => rfl

  let e₁ := LinearEquiv.baseChange ℤ_[p] ℚ_[p] _ _ e
  let E := LinearEquiv.baseChange ℚ_[p] ℂ_[p] _ _ e₁
  have he₁ : ∀ (τ : PadicAlgCl p ≃ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p) v,
      e₁ ((Γ.tateModuleRep (PadicAlgCl p) τ).baseChange ℚ_[p] v) = (G.tateModuleRep (PadicAlgCl p) τ).baseChange ℚ_[p] (e₁ v) :=
    fun τ v => baseChange_intertwine e _ _ (he τ) v
  refine core (S := K.fixingSubgroup) hnh hn'h bG bΓ
    (fun σ => (PadicComplex.galAlgHom p (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)).toRingHom)
    (fun σ => (algebraMap ℚ_[p] ℂ_[p] (((cyclotomicCharacter (PadicAlgCl p) p (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p).toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])))
    (fun σ => (TensorProduct.map (PadicComplex.galAlgHom p (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)).toLinearMap
      ((G.tateModuleRep (PadicAlgCl p) (L σ)).baseChange ℚ_[p])).toAddMonoidHom)
    (fun σ => (TensorProduct.map (PadicComplex.galAlgHom p (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)).toLinearMap
      ((Γ.tateModuleRep (PadicAlgCl p) (L σ)).baseChange ℚ_[p])).toAddMonoidHom)
    (fun σ c x => map_smul_left _ _ c x)
    (fun σ i => hbG _ (L σ) (hL σ) i)
    (fun σ j => hbΓ _ (L σ) (hL σ) j)
    E (fun σ w => map_baseChange_intertwine e₁ _ _ _ (he₁ (L σ)) w) ?_ ?_
  · intro c hc
    apply PadicComplex.eq_zero_of_forall_mem_fixingSubgroup_smul_eq_cyclotomicCharacter_zpow_mul p K 1 one_ne_zero c
    intro σ hσ
    have h := hc ⟨σ, hσ⟩
    rw [zpow_one]
    exact h
  · intro c hc
    apply PadicComplex.eq_zero_of_forall_mem_fixingSubgroup_smul_eq_cyclotomicCharacter_zpow_mul p K (-1) (by norm_num) c
    intro σ hσ
    have h := hc ⟨σ, hσ⟩
    have hu : (algebraMap ℚ_[p] ℂ_[p] (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) ≠ 0 := by
      have hz : (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
        simp [Units.ne_zero]
      exact fun h0 => hz ((map_eq_zero _).1 h0)
    rw [zpow_neg, zpow_one, eq_inv_mul_iff_mul_eq₀ hu, mul_comm]
    exact h

end S_PDivisibleGroup_eq_of_hasDimension_of_linearEquiv_tateModule_of_ringOfIntegers
end P2MW
export P2MW.S_PDivisibleGroup_eq_of_hasDimension_of_linearEquiv_tateModule_of_ringOfIntegers (solution)
