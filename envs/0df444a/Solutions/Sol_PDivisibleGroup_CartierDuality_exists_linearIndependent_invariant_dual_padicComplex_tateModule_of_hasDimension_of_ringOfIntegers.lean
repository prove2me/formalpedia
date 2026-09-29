-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.exists_linearIndependent_invariant_dual_padicComplex_tateModule_of_hasDimension_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/dd8150b6-89e8-5b81-8c4c-62845c410973

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PDivisibleGroup_CharacterDifferential
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Theorems.Thm_PadicComplex_forall_smul_eq_self_iff_mem_closure
import Theorems.Thm_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete
import Theorems.Thm_PDivisibleGroup_nonempty_basis_cotangentModule_of_hasDimension
import Theorems.Thm_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_padicComplex_smul_eq_and_norm_sub_le_of_ringOfIntegers
import Theorems.Thm_PDivisibleGroup_CartierDuality_linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_exists_linearIndependent_invariant_dual_padicComplex_tateModule_of_hasDimension_of_ringOfIntegers
p2m_attr_erase "instance" "PDivisibleGroup.CPoints.instDistribMulAction PrimaryTorsion.instSMul PrimaryTorsion.instModule"
p2m_attr_erase "simp" "PDivisibleGroup.cpointsProj_cpointsMap PDivisibleGroup.pointsMap_reduceModPow_cpointsProj_succ PDivisibleGroup.cpointsProj_toCPoints PDivisibleGroup.mapModPow_mk PDivisibleGroup.reduceModPow_mk PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

set_option autoImplicit false

open scoped TensorProduct

namespace PDivP11K

section Step7

variable {C : Type*} [Field C] {G : Type*} [Monoid G] [MulSemiringAction G C]
variable {Z : Type*} [AddCommGroup Z] [Module C Z]

theorem linearIndependent_of_invariant (f : G → Z →+ Z)
    (hf : ∀ (σ : G) (c : C) (z : Z), f σ (c • z) = (σ • c) • f σ z)
    {ι : Type*} (v : ι → Z) (hv : ∀ (σ : G) (i : ι), f σ (v i) = v i)
    (hK : ∀ (s : Finset ι) (g : ι → C), (∀ i ∈ s, ∀ σ : G, σ • g i = g i) →
      ∑ i ∈ s, g i • v i = 0 → ∀ i ∈ s, g i = 0) :
    LinearIndependent C v := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro g hsum
    by_contra hcon
    push Not at hcon
    obtain ⟨i₀, hi₀s, hgi₀⟩ := hcon

    set g' : ι → C := fun i => g i * (g i₀)⁻¹ with hg'
    have hg'i₀ : g' i₀ = 1 := by simp [hg', hgi₀]
    have hsum' : ∑ i ∈ s, g' i • v i = 0 := by
      have : ∑ i ∈ s, g' i • v i = (g i₀)⁻¹ • ∑ i ∈ s, g i • v i := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hg', smul_smul, mul_comm]
      rw [this, hsum, smul_zero]

    have hfix : ∀ i ∈ s, ∀ σ : G, σ • g' i = g' i := by
      intro i hi σ
      by_cases hii₀ : i = i₀
      · subst hii₀; rw [hg'i₀, smul_one]
      set coef : ι → C := fun i => σ • g' i - g' i with hcoef
      have hrel : ∑ i ∈ s, coef i • v i = 0 := by
        have h1 : ∑ i ∈ s, (σ • g' i) • v i = 0 := by
          have := congrArg (f σ) hsum'
          rw [map_sum, map_zero] at this
          rw [← this]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hf, hv]
        have : ∑ i ∈ s, coef i • v i =
            ∑ i ∈ s, (σ • g' i) • v i - ∑ i ∈ s, g' i • v i := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcoef, sub_smul]
        rw [this, h1, hsum', sub_zero]
      have hcoefi₀ : coef i₀ = 0 := by
        simp [hcoef, hg'i₀, smul_one]
      have hrel' : ∑ i ∈ s.erase i₀, coef i • v i = 0 := by
        rw [Finset.sum_erase _ (by rw [hcoefi₀, zero_smul]), hrel]
      have h0 := ih (s.erase i₀) (Finset.erase_ssubset hi₀s) coef hrel' i
        (Finset.mem_erase.mpr ⟨hii₀, hi⟩)
      rw [hcoef] at h0
      exact sub_eq_zero.mp h0

    have h0 := hK s g' hfix hsum' i₀ hi₀s
    rw [hg'i₀] at h0
    exact one_ne_zero h0

end Step7

section Functionals

variable (p : ℕ) [Fact p.Prime]
variable {Γ : Type*} [Group Γ] [MulSemiringAction Γ ℂ_[p]]
  (π : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (hπ : ∀ (σ : Γ) (c : ℂ_[p]), σ • c = π σ • c)

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

noncomputable def ρ (u : Γ →* Module.End ℚ_[p] V) (σ : Γ) :
    ℂ_[p] ⊗[ℚ_[p]] V →ₗ[ℚ_[p]] ℂ_[p] ⊗[ℚ_[p]] V :=
  TensorProduct.map (PadicComplex.galAlgHom p (π σ)).toLinearMap (u σ)

omit [MulSemiringAction Γ ℂ_[p]] in
theorem ρ_tmul (u : Γ →* Module.End ℚ_[p] V) (σ : Γ) (c : ℂ_[p]) (v : V) :
    ρ p π u σ (c ⊗ₜ[ℚ_[p]] v) = (π σ • c) ⊗ₜ[ℚ_[p]] u σ v := rfl

noncomputable def extC (g : V →ₗ[ℚ_[p]] ℂ_[p]) : ℂ_[p] ⊗[ℚ_[p]] V →ₗ[ℂ_[p]] ℂ_[p] :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.ringLmapEquivSelf ℂ_[p] ℂ_[p] (V →ₗ[ℚ_[p]] ℂ_[p])).symm g)

@[scoped simp] theorem extC_tmul (g : V →ₗ[ℚ_[p]] ℂ_[p]) (c : ℂ_[p]) (v : V) :
    extC p g (c ⊗ₜ[ℚ_[p]] v) = c * g v := by
  simp [extC, LinearMap.ringLmapEquivSelf_symm_apply]

include hπ in

theorem extC_ρ (u : Γ →* Module.End ℚ_[p] V) (g : V →ₗ[ℚ_[p]] ℂ_[p])
    (hg : ∀ (σ : Γ) (v : V), g (u σ v) = σ • g v) (σ : Γ) (x : ℂ_[p] ⊗[ℚ_[p]] V) :
    extC p g (ρ p π u σ x) = σ • extC p g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul c v => rw [ρ_tmul, extC_tmul, extC_tmul, hg, ← hπ, smul_mul']
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

noncomputable def res : (ℂ_[p] ⊗[ℚ_[p]] V →ₗ[ℂ_[p]] ℂ_[p]) →ₗ[ℂ_[p]] (V → ℂ_[p]) where
  toFun F := fun v => F (1 ⊗ₜ[ℚ_[p]] v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem res_extC (g : V →ₗ[ℚ_[p]] ℂ_[p]) : res p (extC p g) = (g : V → ℂ_[p]) := by
  funext v
  show extC p g (1 ⊗ₜ[ℚ_[p]] v) = g v
  rw [extC_tmul, one_mul]

noncomputable def fnAct (u : Γ →* Module.End ℚ_[p] V) (σ : Γ) : (V → ℂ_[p]) →+ (V → ℂ_[p]) where
  toFun F := fun v => σ • F (u σ⁻¹ v)
  map_zero' := by funext v; simp
  map_add' F F' := by funext v; simp [smul_add]

theorem fnAct_smul (u : Γ →* Module.End ℚ_[p] V) (σ : Γ) (c : ℂ_[p]) (F : V → ℂ_[p]) :
    fnAct p u σ (c • F) = (σ • c) • fnAct p u σ F := by
  funext v
  show σ • (c * F (u σ⁻¹ v)) = (σ • c) * (σ • F (u σ⁻¹ v))
  rw [smul_mul']

theorem fnAct_coe (u : Γ →* Module.End ℚ_[p] V) (g : V →ₗ[ℚ_[p]] ℂ_[p])
    (hg : ∀ (σ : Γ) (v : V), g (u σ v) = σ • g v) (σ : Γ) :
    fnAct p u σ (g : V → ℂ_[p]) = (g : V → ℂ_[p]) := by
  funext v
  show σ • g (u σ⁻¹ v) = g v
  rw [← hg, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

include hπ in

theorem exists_functionals
    (u : Γ →* Module.End ℚ_[p] V) {n : ℕ} (g : Fin n → V →ₗ[ℚ_[p]] ℂ_[p])
    (hgi : ∀ (s : Finset (Fin n)) (k : Fin n → ℂ_[p]), (∀ i ∈ s, ∀ σ : Γ, σ • k i = k i) →
      ∑ i ∈ s, k i • ((g i : V →ₗ[ℚ_[p]] ℂ_[p]) : V → ℂ_[p]) = 0 → ∀ i ∈ s, k i = 0)
    (hg : ∀ (σ : Γ) (j : Fin n) (v : V), g j (u σ v) = σ • g j v) :
    ∃ φ : Fin n → (ℂ_[p] ⊗[ℚ_[p]] V →ₗ[ℂ_[p]] ℂ_[p]),
      LinearIndependent ℂ_[p] φ ∧
      ∀ (σ : Γ) (j : Fin n) (x : ℂ_[p] ⊗[ℚ_[p]] V), φ j (ρ p π u σ x) = σ • φ j x := by
  refine ⟨fun j => extC p (g j), ?_, fun σ j x => extC_ρ p π hπ u (g j) (hg · j ·) σ x⟩

  apply LinearIndependent.of_comp (res p)
  have hres : (res p) ∘ (fun j => extC p (g j)) = fun j => ((g j : V →ₗ[ℚ_[p]] ℂ_[p]) : V → ℂ_[p]) := by
    funext j; exact res_extC p (g j)
  rw [hres]
  exact linearIndependent_of_invariant (fnAct p u) (fnAct_smul p u) _
    (fun σ j => fnAct_coe p u (g j) (hg · j ·) σ) hgi

end Functionals

section Instantiate

variable (p : ℕ) [Fact p.Prime]
variable {Γ : Type*} [Group Γ] [MulSemiringAction Γ ℂ_[p]]
  (π : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (hπ : ∀ (σ : Γ) (c : ℂ_[p]), σ • c = π σ • c)
variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)] (πO : Γ →* (PadicAlgCl p ≃ₐ[R] PadicAlgCl p))

noncomputable def uV {h : ℕ} (G' : PDivisibleGroup R p h) :
    Γ →* Module.End ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] TateModule p (G'.Points (PadicAlgCl p))) where
  toFun σ := (G'.tateModuleRep (PadicAlgCl p) (πO σ)).baseChange ℚ_[p]
  map_one' := by
    rw [map_one, map_one]
    exact LinearMap.baseChange_one _ _
  map_mul' σ τ := by
    rw [map_mul, map_mul]
    exact LinearMap.baseChange_mul _ _

omit [MulSemiringAction Γ ℂ_[p]] in
theorem uV_apply {h : ℕ} (G' : PDivisibleGroup R p h) (σ : Γ) :
    uV p πO G' σ = (G'.tateModuleRep (PadicAlgCl p) (πO σ)).baseChange ℚ_[p] := rfl

include hπ in

theorem target_of_core {h : ℕ} (G' : PDivisibleGroup R p h) {n : ℕ}
    (core : ∃ g : Fin n → (ℚ_[p] ⊗[ℤ_[p]] TateModule p (G'.Points (PadicAlgCl p))) →ₗ[ℚ_[p]] ℂ_[p],
      (∀ (s : Finset (Fin n)) (k : Fin n → ℂ_[p]), (∀ i ∈ s, ∀ σ : Γ, σ • k i = k i) →
        ∑ i ∈ s, k i • ((g i : _ →ₗ[ℚ_[p]] ℂ_[p]) : _ → ℂ_[p]) = 0 → ∀ i ∈ s, k i = 0) ∧
      ∀ (σ : Γ) (j : Fin n) (y : ℚ_[p] ⊗[ℤ_[p]] TateModule p (G'.Points (PadicAlgCl p))),
        g j ((G'.tateModuleRep (PadicAlgCl p) (πO σ)).baseChange ℚ_[p] y) = σ • g j y) :
    ∃ φ : Fin n →
        (ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] TateModule p (G'.Points (PadicAlgCl p))) →ₗ[ℂ_[p]] ℂ_[p]),
      LinearIndependent ℂ_[p] φ ∧
      ∀ (σ : Γ) (j : Fin n)
        (x : ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] TateModule p (G'.Points (PadicAlgCl p)))),
        φ j (TensorProduct.map (PadicComplex.galAlgHom p (π σ)).toLinearMap
            ((G'.tateModuleRep (PadicAlgCl p) (πO σ)).baseChange ℚ_[p]) x) =
          σ • φ j x := by
  obtain ⟨g, hgi, hg⟩ := core
  obtain ⟨φ, hφ, hφρ⟩ := exists_functionals p π hπ (uV p πO G') g hgi (fun σ j y => hg σ j y)
  exact ⟨φ, hφ, fun σ j x => hφρ σ j x⟩

end Instantiate

section Glue

variable (p : ℕ) [Fact p.Prime]

theorem uniformContinuousConstSMul_int : UniformContinuousConstSMul ℤ_[p] (PadicAlgCl p) :=
  ⟨fun a => by
    have h1 : (fun x : PadicAlgCl p => a • x) = fun x => (a : ℚ_[p]) • x := by
      funext x; exact (IsScalarTower.algebraMap_smul ℚ_[p] a x).symm
    rw [h1]
    exact uniformContinuous_const_smul (a : ℚ_[p])⟩

attribute [local instance] uniformContinuousConstSMul_int

noncomputable example : Module ℤ_[p] ℂ_[p] := inferInstance
example : IsScalarTower ℤ_[p] ℚ_[p] ℂ_[p] := inferInstance

theorem int_smul_eq (a : ℤ_[p]) (c : ℂ_[p]) : a • c = (a : ℚ_[p]) • c :=
  (IsScalarTower.algebraMap_smul ℚ_[p] a c).symm

variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)] {h : ℕ} (G' : PDivisibleGroup R p h)

noncomputable def bil (dα : TateModule p (G'.Points (PadicAlgCl p)) →+ ℂ_[p])
    (hsmul : ∀ (a : ℤ_[p]) (y : TateModule p (G'.Points (PadicAlgCl p))), dα (a • y) = (a : ℚ_[p]) • dα y) :
    ℚ_[p] →ₗ[ℤ_[p]] TateModule p (G'.Points (PadicAlgCl p)) →ₗ[ℤ_[p]] ℂ_[p] :=
  LinearMap.mk₂ ℤ_[p] (fun q y => q • dα y)
    (fun q q' y => add_smul q q' _)
    (fun a q y => by
      show (a • q) • dα y = a • (q • dα y)
      rw [Algebra.smul_def a q, mul_smul, int_smul_eq]
      rfl)
    (fun q y y' => by
      show q • dα (y + y') = q • dα y + q • dα y'
      rw [map_add, smul_add])
    (fun a q y => by
      show q • dα (a • y) = a • (q • dα y)
      rw [hsmul, smul_comm, int_smul_eq])

noncomputable def gExt (dα : TateModule p (G'.Points (PadicAlgCl p)) →+ ℂ_[p])
    (hsmul : ∀ (a : ℤ_[p]) (y : TateModule p (G'.Points (PadicAlgCl p))), dα (a • y) = (a : ℚ_[p]) • dα y) :
    ℚ_[p] ⊗[ℤ_[p]] TateModule p (G'.Points (PadicAlgCl p)) →ₗ[ℚ_[p]] ℂ_[p] where
  toFun := TensorProduct.lift (bil p G' dα hsmul)
  map_add' x y := map_add _ x y
  map_smul' q z := by
    rw [RingHom.id_apply]
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul q' y =>
        rw [TensorProduct.smul_tmul', TensorProduct.lift.tmul, TensorProduct.lift.tmul]
        change (q • q') • dα y = q • (q' • dα y)
        rw [smul_eq_mul, mul_smul]
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem gExt_tmul (dα : TateModule p (G'.Points (PadicAlgCl p)) →+ ℂ_[p])
    (hsmul : ∀ (a : ℤ_[p]) (y : TateModule p (G'.Points (PadicAlgCl p))), dα (a • y) = (a : ℚ_[p]) • dα y)
    (q : ℚ_[p]) (y : TateModule p (G'.Points (PadicAlgCl p))) :
    gExt p G' dα hsmul (q ⊗ₜ[ℤ_[p]] y) = q • dα y :=
  TensorProduct.lift.tmul _ _

variable {Γ : Type*} [Group Γ] [MulSemiringAction Γ ℂ_[p]] [SMulCommClass Γ ℚ_[p] ℂ_[p]]
  (πO : Γ →* (PadicAlgCl p ≃ₐ[R] PadicAlgCl p))

theorem core_of {n : ℕ} (dα : Fin n → (TateModule p (G'.Points (PadicAlgCl p)) →+ ℂ_[p]))
    (hsmul : ∀ (j : Fin n) (a : ℤ_[p]) (y : TateModule p (G'.Points (PadicAlgCl p))),
      dα j (a • y) = (a : ℚ_[p]) • dα j y)
    (hgal : ∀ (σ : Γ) (j : Fin n) (y : TateModule p (G'.Points (PadicAlgCl p))),
      dα j (G'.tateModuleRep (PadicAlgCl p) (πO σ) y) = σ • dα j y)
    (hind : ∀ (s : Finset (Fin n)) (k : Fin n → ℂ_[p]), (∀ i ∈ s, ∀ σ : Γ, σ • k i = k i) →
      ∑ i ∈ s, k i • (⇑(dα i) : TateModule p (G'.Points (PadicAlgCl p)) → ℂ_[p]) = 0 → ∀ i ∈ s, k i = 0) :
    ∃ g : Fin n → (ℚ_[p] ⊗[ℤ_[p]] TateModule p (G'.Points (PadicAlgCl p))) →ₗ[ℚ_[p]] ℂ_[p],
      (∀ (s : Finset (Fin n)) (k : Fin n → ℂ_[p]), (∀ i ∈ s, ∀ σ : Γ, σ • k i = k i) →
        ∑ i ∈ s, k i • ((g i : _ →ₗ[ℚ_[p]] ℂ_[p]) : _ → ℂ_[p]) = 0 → ∀ i ∈ s, k i = 0) ∧
      ∀ (σ : Γ) (j : Fin n) (y : ℚ_[p] ⊗[ℤ_[p]] TateModule p (G'.Points (PadicAlgCl p))),
        g j ((G'.tateModuleRep (PadicAlgCl p) (πO σ)).baseChange ℚ_[p] y) = σ • g j y := by
  refine ⟨fun j => gExt p G' (dα j) (hsmul j), ?_, ?_⟩
  ·
    intro s k hk hc
    refine hind s k hk ?_
    funext y
    have h1 := congrFun hc ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y)
    rw [Finset.sum_apply, Pi.zero_apply] at h1
    rw [Finset.sum_apply, Pi.zero_apply, ← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, gExt_tmul, one_smul]
  · intro σ j y
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, smul_zero]
    | tmul q t =>
        rw [LinearMap.baseChange_tmul, gExt_tmul, gExt_tmul, smul_comm]
        exact congrArg _ (hgal σ j t)
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]

end Glue

section Base

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

local notation "Γp" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
local notation "GK" => (K.fixingSubgroup : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))

theorem subgroup_smul_def (σ : GK) (c : ℂ_[p]) : σ • c = K.fixingSubgroup.subtype σ • c := rfl

noncomputable def κ (k : K) : ℂ_[p] := ((k : PadicAlgCl p) : ℂ_[p])

theorem smul_eq_κ_mul (k : K) (c : ℂ_[p]) : k • c = κ p K k * c :=
  Algebra.smul_def (k : PadicAlgCl p) c

theorem κ_zero : κ p K 0 = 0 := by
  simp [κ]

theorem exists_κ_eq_of_forall_smul_eq [FiniteDimensional ℚ_[p] K] (c : ℂ_[p])
    (hc : ∀ σ : GK, σ • c = c) : ∃ k : K, κ p K k = c := by
  have h := (PadicComplex.forall_smul_eq_self_iff_mem_closure p K c).1 (fun σ hσ => hc ⟨σ, hσ⟩)
  let L : K →ₗ[ℚ_[p]] ℂ_[p] :=
    ((Algebra.linearMap (PadicAlgCl p) ℂ_[p]).restrictScalars ℚ_[p]).comp K.val.toLinearMap
  have hrange : (Set.range fun k : K => ((k : PadicAlgCl p) : ℂ_[p])) = (LinearMap.range L : Set ℂ_[p]) := by
    ext z
    simp only [Set.mem_range, SetLike.mem_coe, LinearMap.mem_range]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
  rw [hrange, (LinearMap.range L).closed_of_finiteDimensional.closure_eq] at h
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk⟩

theorem indep_of_linearIndependent [FiniteDimensional ℚ_[p] K] {X : Type*} {n : ℕ} (F : Fin n → X → ℂ_[p])
    (hF : LinearIndependent K F) (s : Finset (Fin n)) (k : Fin n → ℂ_[p])
    (hk : ∀ i ∈ s, ∀ σ : GK, σ • k i = k i) (hsum : ∑ i ∈ s, k i • F i = 0) :
    ∀ i ∈ s, k i = 0 := by
  classical

  have hq : ∀ i, ∃ q : K, i ∈ s → κ p K q = k i := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨q, hq⟩ := exists_κ_eq_of_forall_smul_eq p K (k i) (hk i hi)
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose q hq using hq

  have hsumq : ∑ i ∈ s, q i • F i = 0 := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun i hi => ?_
    funext x
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_κ_mul, hq i hi, smul_eq_mul]
  intro i hi
  have h0 := (linearIndependent_iff'.mp hF) s q hsumq i hi
  rw [← hq i hi, h0, κ_zero]

theorem exists_eq_galToAlgEquiv (σ : Γp) (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p)
    (hτσ : ∀ x : PadicAlgCl p, τ x = σ x) :
    ∃ hσ : σ ∈ K.fixingSubgroup, τ = PadicAlgCl.ringOfIntegers.galToAlgEquiv p K ⟨σ, hσ⟩ := by
  have hσ : σ ∈ K.fixingSubgroup := by
    have hmem := PadicAlgCl.ringOfIntegers.restrictScalarsRat_mem_fixingSubgroup p K τ
    have heq : PadicAlgCl.ringOfIntegers.restrictScalarsRat p K τ = σ := AlgEquiv.ext hτσ
    rwa [heq] at hmem
  exact ⟨hσ, AlgEquiv.ext fun x => hτσ x⟩

theorem nonempty_basis [FiniteDimensional ℚ_[p] K] {h : ℕ}
    (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) {n : ℕ} (hn : G.HasDimension n) :
    Nonempty (Module.Basis (Fin n) (PadicAlgCl.ringOfIntegers p K) G.cotangentModule) := by
  obtain ⟨-, hdvr, hcomplete⟩ :=
    PadicAlgCl.ringOfIntegers.finite_and_isDiscreteValuationRing_and_isAdicComplete p K
  haveI := hdvr
  haveI := hcomplete
  have hp : ((p : ℕ) : PadicAlgCl.ringOfIntegers p K) ∈
      IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p K) :=
    (IsLocalRing.mem_maximalIdeal _).2 (PadicAlgCl.ringOfIntegers.not_isUnit_natCast p K)
  exact (PDivisibleGroup.nonempty_basis_cotangentModule_of_hasDimension
    (IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p K)) hp G hn).1

theorem exists_functionals_fixingSubgroup [FiniteDimensional ℚ_[p] K]
    {h : ℕ} {G G' : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h} (D : G.CartierDuality G')
    {n : ℕ} (hn : G.HasDimension n) :
    ∃ φ : Fin n →
        (ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] TateModule p (G'.Points (PadicAlgCl p))) →ₗ[ℂ_[p]] ℂ_[p]),
      LinearIndependent ℂ_[p] φ ∧
      ∀ (σ : GK) (j : Fin n)
        (x : ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] TateModule p (G'.Points (PadicAlgCl p)))),
        φ j (TensorProduct.map (PadicComplex.galAlgHom p (K.fixingSubgroup.subtype σ)).toLinearMap
            ((G'.tateModuleRep (PadicAlgCl p)
              (PadicAlgCl.ringOfIntegers.galToAlgEquiv p K σ)).baseChange ℚ_[p]) x) =
          σ • φ j x := by

  obtain ⟨b⟩ := nonempty_basis p K G hn

  obtain ⟨dα, hsmul, hgal, hpin⟩ :=
    PDivisibleGroup.CartierDuality.exists_addMonoidHom_tateModule_padicComplex_smul_eq_and_norm_sub_le_of_ringOfIntegers
      p K D hn b

  have hind :=
    PDivisibleGroup.CartierDuality.linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers
      p K D hn b dα hpin

  have hgal' : ∀ (σ : GK) (j : Fin n) (y : TateModule p (G'.Points (PadicAlgCl p))),
      dα j (G'.tateModuleRep (PadicAlgCl p) (PadicAlgCl.ringOfIntegers.galToAlgEquiv p K σ) y) = σ • dα j y :=
    fun σ j y => hgal (σ : Γp) (PadicAlgCl.ringOfIntegers.galToAlgEquiv p K σ) (fun _ => rfl) j y
  exact target_of_core p K.fixingSubgroup.subtype (subgroup_smul_def p K)
    (PadicAlgCl.ringOfIntegers.galToAlgEquiv p K) G'
    (core_of p G' (PadicAlgCl.ringOfIntegers.galToAlgEquiv p K) dα hsmul hgal'
      (indep_of_linearIndependent p K _ hind))

end Base

end PDivP11K
p2m_reactivate "P2MW.S_PDivisibleGroup_CartierDuality_exists_linearIndependent_invariant_dual_padicComplex_tateModule_of_hasDimension_of_ringOfIntegers.PDivP11K"

open PDivP11K in

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} {G G' : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h} (D : G.CartierDuality G')
    {n : ℕ} (hn : G.HasDimension n) :
    ∃ φ : Fin n →
        (ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] TateModule p (G'.Points (PadicAlgCl p))) →ₗ[ℂ_[p]] ℂ_[p]),
      LinearIndependent ℂ_[p] φ ∧
      ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ x : PadicAlgCl p, τ x = σ x) → ∀ (j : Fin n)
        (x : ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] TateModule p (G'.Points (PadicAlgCl p)))),
        φ j (TensorProduct.map (PadicComplex.galAlgHom p σ).toLinearMap
            ((G'.tateModuleRep (PadicAlgCl p) τ).baseChange ℚ_[p]) x) =
          σ • φ j x := by
  obtain ⟨φ, hφi, hφ⟩ := exists_functionals_fixingSubgroup p K D hn
  refine ⟨φ, hφi, fun σ τ hτσ j x => ?_⟩
  obtain ⟨hσ, rfl⟩ := exists_eq_galToAlgEquiv p K σ τ hτσ
  exact hφ ⟨σ, hσ⟩ j x

end S_PDivisibleGroup_CartierDuality_exists_linearIndependent_invariant_dual_padicComplex_tateModule_of_hasDimension_of_ringOfIntegers
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_exists_linearIndependent_invariant_dual_padicComplex_tateModule_of_hasDimension_of_ringOfIntegers (solution)
