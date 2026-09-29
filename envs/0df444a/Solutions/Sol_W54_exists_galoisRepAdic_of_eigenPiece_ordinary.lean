-- Prove2me | solution 1 for W54.exists_galoisRepAdic_of_eigenPiece_ordinary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/94f50f3d-e02e-5f37-b0c7-fd77465c1fc4

import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_LocalConditions
import Theorems.Thm_GaloisRepAdic_isOrdinaryAt_of_stableLine_baseChange
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_W54_exists_galoisRepAdic_of_eigenPiece_ordinary

set_option autoImplicit false

open Polynomial
open scoped TensorProduct

namespace OrdPtSol

namespace DCut

section Basic

variable {𝒪' : Type} [CommRing 𝒪'] (K : Type) [Field K] [Algebra 𝒪' K]
variable {M : Type} [AddCommGroup M] [Module 𝒪' M]

abbrev toK : M →ₗ[𝒪'] K ⊗[𝒪'] M := TensorProduct.mk 𝒪' K M 1

lemma toK_apply_end (f : Module.End 𝒪' M) (m : M) :
    toK K (f m) = f.baseChange K (toK K m) := by
  simp [LinearMap.baseChange_tmul]

def eigenLattice (W : Submodule K (K ⊗[𝒪'] M)) : Submodule 𝒪' M :=
  (W.restrictScalars 𝒪').comap (toK K)

variable (W : Submodule K (K ⊗[𝒪'] M))

lemma mem_eigenLattice {m : M} : m ∈ eigenLattice K W ↔ toK K m ∈ W := Iff.rfl

def toPlane : eigenLattice K W →ₗ[𝒪'] W where
  toFun m := ⟨toK K (m : M), m.2⟩
  map_add' x y := by
    apply Subtype.ext
    simp [TensorProduct.tmul_add]
  map_smul' c x := by
    apply Subtype.ext
    simp

@[scoped simp] lemma coe_toPlane (m : eigenLattice K W) : (toPlane K W m : K ⊗[𝒪'] M) = toK K (m : M) :=
  rfl

lemma map_mem_eigenLattice (f : Module.End 𝒪' M) (hf : ∀ w ∈ W, f.baseChange K w ∈ W)
    {m : M} (hm : m ∈ eigenLattice K W) : f m ∈ eigenLattice K W := by
  rw [mem_eigenLattice, toK_apply_end]
  exact hf _ hm

variable (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End 𝒪' M)
  (hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ W, (ρM σ).baseChange K w ∈ W)

noncomputable def restrictRep : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End 𝒪' (eigenLattice K W) where
  toFun σ := (ρM σ).restrict fun _ hm => map_mem_eigenLattice K W (ρM σ) (hW σ) hm
  map_one' := by
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    simp [LinearMap.restrict_apply]
  map_mul' σ τ := by
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    simp [LinearMap.restrict_apply]

@[scoped simp] lemma coe_restrictRep_apply (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (m : eigenLattice K W) : (restrictRep K W ρM hW σ m : M) = ρM σ (m : M) := rfl

lemma restrictRep_eq_one {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (h : ρM σ = 1) :
    restrictRep K W ρM hW σ = 1 := by
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  simp [h]

end Basic

section Lattice

variable {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] (K : Type) [Field K] [Algebra 𝒪' K]
  [IsFractionRing 𝒪' K]
variable {M : Type} [AddCommGroup M] [Module 𝒪' M] [Module.Free 𝒪' M]

lemma toK_injective : Function.Injective (toK (𝒪' := 𝒪') K (M := M)) := by
  intro x y hxy
  have h : toK (𝒪' := 𝒪') K (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨s, hs⟩ :=
    (IsLocalizedModule.eq_zero_iff (nonZeroDivisors 𝒪') (toK (𝒪' := 𝒪') K (M := M))).mp h
  rw [Submonoid.smul_def] at hs
  rcases smul_eq_zero.mp hs with h0 | h0
  · exact absurd h0 (nonZeroDivisors.coe_ne_zero s)
  · exact sub_eq_zero.mp h0

instance instAddCommGroupBaseChangePlane : AddCommGroup (K ⊗[𝒪'] M) := inferInstance

variable (W : Submodule K (K ⊗[𝒪'] M))

instance instModuleFreePlane : Module.Free K W := Module.Free.of_divisionRing K W

omit [IsDomain 𝒪'] [Module.Free 𝒪' M] in

lemma mem_eigenLattice_of_smul_mem {c : 𝒪'} (hc : c ≠ 0) {m : M}
    (hm : c • m ∈ eigenLattice K W) : m ∈ eigenLattice K W := by
  rw [mem_eigenLattice] at hm ⊢
  have hc' : algebraMap 𝒪' K c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝒪' K)).mpr hc
  have h1 : algebraMap 𝒪' K c • toK (𝒪' := 𝒪') K m ∈ W := by
    rw [algebraMap_smul, ← map_smul]
    exact hm
  have h2 := W.smul_mem (algebraMap 𝒪' K c)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at h2

scoped instance isLocalizedModule_toPlane : IsLocalizedModule (nonZeroDivisors 𝒪') (toPlane K W) where
  map_units s := (isLocalizedModule_id (nonZeroDivisors 𝒪') W K).map_units s
  surj y := by
    obtain ⟨⟨m, s⟩, h⟩ := IsLocalizedModule.surj (nonZeroDivisors 𝒪') (toK (𝒪' := 𝒪') K (M := M))
      (y : K ⊗[𝒪'] M)
    have hy : (s : 𝒪') • (y : K ⊗[𝒪'] M) = toK (𝒪' := 𝒪') K m := by
      simpa [Submonoid.smul_def] using h
    have hm : m ∈ eigenLattice K W := by
      rw [mem_eigenLattice, ← hy, ← algebraMap_smul K (s : 𝒪') (y : K ⊗[𝒪'] M)]
      exact W.smul_mem _ y.2
    refine ⟨(⟨m, hm⟩, s), ?_⟩
    apply Subtype.ext
    rw [Submonoid.smul_def, Submodule.coe_smul_of_tower, coe_toPlane, hy]
  exists_of_eq {x₁ x₂} h := ⟨1, by
    have h' : toK (𝒪' := 𝒪') K (x₁ : M) = toK (𝒪' := 𝒪') K (x₂ : M) := congrArg Subtype.val h
    rw [one_smul, one_smul]
    exact Subtype.ext (toK_injective K h')⟩

lemma isBaseChange_toPlane : IsBaseChange K (toPlane K W) :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors 𝒪') K (toPlane K W)).mp inferInstance

variable [IsDiscreteValuationRing 𝒪'] [Module.Finite 𝒪' M]

omit [IsFractionRing 𝒪' K] [Module.Free 𝒪' M] in
scoped instance finite_eigenLattice : Module.Finite 𝒪' (eigenLattice K W) := inferInstance

omit [IsFractionRing 𝒪' K] in
scoped instance free_eigenLattice : Module.Free 𝒪' (eigenLattice K W) :=
  Module.Free.of_basis (Submodule.basisOfPid (Module.Free.chooseBasis 𝒪' M) (eigenLattice K W)).2

omit [IsDiscreteValuationRing 𝒪'] [Module.Finite 𝒪' M] in

lemma finrank_eigenLattice : Module.finrank 𝒪' (eigenLattice K W) = Module.finrank K W := by
  haveI : FaithfulSMul 𝒪' K :=
    (faithfulSMul_iff_algebraMap_injective 𝒪' K).mpr (IsFractionRing.injective 𝒪' K)
  exact (isBaseChange_toPlane K W).finrank_eq.symm

variable (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End 𝒪' M)
  (hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ W, (ρM σ).baseChange K w ∈ W)

omit [Module.Free 𝒪' M] [Module.Finite 𝒪' M] in

lemma isAdicContinuous_restrictRep (hcont : GaloisActionIsAdicContinuous 𝒪' ρM) :
    GaloisActionIsAdicContinuous 𝒪' (restrictRep K W ρM hW) := by
  intro n
  obtain ⟨L, hL, h1⟩ := hcont n
  refine ⟨L, hL, fun σ hσ v => ?_⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪'
  have hmax : IsLocalRing.maximalIdeal 𝒪' = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have key : ∀ {X : Type} [AddCommGroup X] [Module 𝒪' X] (x : X),
      x ∈ (IsLocalRing.maximalIdeal 𝒪' ^ n) • (⊤ : Submodule 𝒪' X) ↔ ∃ y : X, ϖ ^ n • y = x := by
    intro X _ _ x
    rw [hmax, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp
  obtain ⟨y, hy⟩ := (key _).mp (h1 σ hσ (v : M))
  have hyΛ : y ∈ eigenLattice K W := by
    refine mem_eigenLattice_of_smul_mem K W (pow_ne_zero n hϖ.ne_zero) ?_
    rw [hy]
    exact (eigenLattice K W).sub_mem (map_mem_eigenLattice K W (ρM σ) (hW σ) v.2) v.2
  refine (key _).mpr ⟨⟨y, hyΛ⟩, ?_⟩
  apply Subtype.ext
  simpa using hy

end Lattice

section Charpoly

variable {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
variable (K : Type) [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
variable {M : Type} [AddCommGroup M] [Module 𝒪' M] [Module.Finite 𝒪' M] [Module.Free 𝒪' M]
variable (W : Submodule K (K ⊗[𝒪'] M))
variable (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End 𝒪' M)
  (hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ W, (ρM σ).baseChange K w ∈ W)

omit [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪'] [IsFractionRing 𝒪' K] [Module.Finite 𝒪' M]
  [Module.Free 𝒪' M] in

noncomputable abbrev planeEnd (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Module.End K W :=
  ((ρM σ).baseChange K).restrict (hW σ)

lemma charpoly_restrictRep_map (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (LinearMap.charpoly (restrictRep K W ρM hW σ)).map (algebraMap 𝒪' K) =
      LinearMap.charpoly (planeEnd K W ρM hW σ) := by
  set e := (isBaseChange_toPlane K W).equiv with he
  set φ := (restrictRep K W ρM hW σ).baseChange K with hφ
  set g : Module.End K W := planeEnd K W ρM hW σ with hg
  have hcomm : ∀ y, e (φ y) = g (e y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k v =>
        rw [hφ, LinearMap.baseChange_tmul, he, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul,
          map_smul]
        congr 1
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hconj : e.conj φ = g := by
    apply LinearMap.ext
    intro x
    rw [LinearEquiv.conj_apply_apply, hcomm, LinearEquiv.apply_symm_apply]
  rw [← LinearMap.charpoly_baseChange, ← hconj, LinearEquiv.charpoly_conj]

omit [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪'] [IsFractionRing 𝒪' K] in

lemma charpoly_eq_of_quadratic_of_trace {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hV : Module.finrank K V = 2) (g : V →ₗ[K] V) (a c : K)
    (hquad : g * g - a • g + c • (1 : V →ₗ[K] V) = 0) (htr : LinearMap.trace K V g = a) :
    g.charpoly = X ^ 2 - C a * X + C c := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  let b := Module.finBasisOfFinrankEq K V hV
  have hcp : g.charpoly = X ^ 2 - C (LinearMap.trace K V g) * X + C (LinearMap.det g) := by
    rw [← LinearMap.charpoly_toMatrix g b, Matrix.charpoly_fin_two,
      ← LinearMap.trace_eq_matrix_trace K b g, LinearMap.det_toMatrix b g]
  have hCH' : g * g - a • g + LinearMap.det g • (1 : V →ₗ[K] V) = 0 := by
    have h := LinearMap.aeval_self_charpoly g
    rw [hcp, htr] at h
    simpa only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, sq] using h
  have h0 : LinearMap.det g • (1 : V →ₗ[K] V) = c • (1 : V →ₗ[K] V) :=
    add_left_cancel (hCH'.trans hquad.symm)
  have h1 : (LinearMap.det g - c) • (1 : V →ₗ[K] V) = 0 := by
    rw [sub_smul, h0, sub_self]
  have hdet : LinearMap.det g = c := by
    rcases smul_eq_zero.mp h1 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h one_ne_zero
  rw [hcp, htr, hdet]

variable (N : ℕ) [NeZero N] (S : Set ℕ)
  (TM : ModularCurve.HeckeAlg →+* Module.End 𝒪' M)
  (χ : CuspForm.heckeAlgebra N 2 S →+* 𝒪')

omit [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪'] [IsFractionRing 𝒪' K] [Module.Finite 𝒪' M]
  [Module.Free 𝒪' M] in

lemma quadratic_on_plane
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S)
    (heig : ∀ w ∈ W, (TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K w =
      algebraMap 𝒪' K (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • w)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hquad : ∀ m : M, ρM σ (ρM σ m) - TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩) (ρM σ m)
      + (ℓ : 𝒪') • m = 0) :
    planeEnd K W ρM hW σ * planeEnd K W ρM hW σ
      - algebraMap 𝒪' K (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • planeEnd K W ρM hW σ
      + (algebraMap 𝒪' K (ℓ : 𝒪')) • (1 : Module.End K W) = 0 := by

  have hop : ∀ x : K ⊗[𝒪'] M,
      (ρM σ).baseChange K ((ρM σ).baseChange K x)
        - (TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K ((ρM σ).baseChange K x)
        + algebraMap 𝒪' K (ℓ : 𝒪') • x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul k m =>
        simp only [LinearMap.baseChange_tmul]
        rw [algebraMap_smul, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_sub,
          ← TensorProduct.tmul_add, hquad m, TensorProduct.tmul_zero]
    | add x y hx hy =>
        have h := congrArg₂ (· + ·) hx hy
        simp only [add_zero] at h
        rw [← h]
        simp only [map_add, smul_add]
        abel
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  have h1 := hop (w : K ⊗[𝒪'] M)
  rw [heig _ (hW σ _ w.2)] at h1
  simpa [planeEnd, LinearMap.restrict_apply, Submodule.coe_smul_of_tower] using h1

theorem charpoly_restrictRep
    (hW2 : Module.finrank K W = 2)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S)
    (heig : ∀ w ∈ W, (TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K w =
      algebraMap 𝒪' K (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • w)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (htr : LinearMap.trace K W (((ρM σ).baseChange K).restrict (hW σ)) =
      algebraMap 𝒪' K (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)))
    (hquad : ∀ m : M, ρM σ (ρM σ m) - TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩) (ρM σ m)
      + (ℓ : 𝒪') • m = 0) :
    LinearMap.charpoly (restrictRep K W ρM hW σ) =
      X ^ 2 - C (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C ((ℓ : 𝒪')) := by
  apply Polynomial.map_injective (algebraMap 𝒪' K) (IsFractionRing.injective 𝒪' K)
  rw [charpoly_restrictRep_map K W ρM hW σ,
    charpoly_eq_of_quadratic_of_trace K hW2 _ _ _
      (quadratic_on_plane K W ρM hW N S TM χ hℓ hℓN hℓS heig σ hquad) htr]
  simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

end Charpoly

section Assembly

variable {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
variable (K : Type) [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
variable {M : Type} [AddCommGroup M] [Module 𝒪' M] [Module.Finite 𝒪' M] [Module.Free 𝒪' M]

noncomputable def galoisRepOfEigenPiece
    (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End 𝒪' M)
    (W : Submodule K (K ⊗[𝒪'] M)) (hW2 : Module.finrank K W = 2)
    (hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ W, (ρM σ).baseChange K w ∈ W)
    (hcont : GaloisActionIsAdicContinuous 𝒪' ρM) : GaloisRepAdic 𝒪' where
  V := eigenLattice K W
  finrank_eq := by rw [finrank_eigenLattice, hW2]
  ρ := restrictRep K W ρM hW
  isAdicContinuous := isAdicContinuous_restrictRep K W ρM hW hcont

variable (p : ℕ) (N : ℕ) [NeZero N] (S : Set ℕ)
  (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End 𝒪' M)
  (TM : ModularCurve.HeckeAlg →+* Module.End 𝒪' M)
  (χ : CuspForm.heckeAlgebra N 2 S →+* 𝒪')
  (W : Submodule K (K ⊗[𝒪'] M)) (hW2 : Module.finrank K W = 2)
  (hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ W, (ρM σ).baseChange K w ∈ W)
  (hcont : GaloisActionIsAdicContinuous 𝒪' ρM)

@[scoped simp] lemma galoisRepOfEigenPiece_ρ :
    (galoisRepOfEigenPiece K ρM W hW2 hW hcont).ρ = restrictRep K W ρM hW := rfl

theorem galoisRepOfEigenPiece_charpoly
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), ∀ w ∈ W,
      (TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K w =
        algebraMap 𝒪' K (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • w)
    (htr : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace K W (((ρM σ).baseChange K).restrict (hW σ)) =
            algebraMap 𝒪' K (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)))
    (hquad : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (_hℓN : ¬ ℓ ∣ N) (_hℓS : ℓ ∉ S),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          ∀ m : M, ρM σ (ρM σ m) - TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩) (ρM σ m)
            + (ℓ : 𝒪') • m = 0)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) :
    LinearMap.charpoly ((galoisRepOfEigenPiece K ρM W hW2 hW hcont).ρ σ) =
      X ^ 2 - C (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C ((ℓ : 𝒪')) :=
  charpoly_restrictRep K W ρM hW N S TM χ hW2 hℓ hℓN hℓS (heig ℓ hℓ hℓN hℓS) σ
    (htr ℓ hℓ hℓN hℓS A hA σ hσ) (hquad ℓ hℓ hℓN hℓS A hA σ hσ)

omit [NeZero N] in
theorem galoisRepOfEigenPiece_isUnramifiedAt
    (hunr : ∀ q : ℕ, q.Prime → ¬ q ∣ N → q ≠ p →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρM σ = 1)
    (q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N) (hqp : q ≠ p) :
    (galoisRepOfEigenPiece K ρM W hW2 hW hcont).IsUnramifiedAt q :=
  fun P hP σ hσ => restrictRep_eq_one K W ρM hW (hunr q hq hqN hqp P hP σ hσ)

end Assembly

end DCut
p2m_reactivate "P2MW.S_W54_exists_galoisRepAdic_of_eigenPiece_ordinary.OrdPtSol.DCut"

namespace DCut

section Ordinary

variable {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
variable (K : Type) [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
variable {M : Type} [AddCommGroup M] [Module 𝒪' M] [Module.Finite 𝒪' M] [Module.Free 𝒪' M]
variable (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End 𝒪' M)
variable (W : Submodule K (K ⊗[𝒪'] M)) (hW2 : Module.finrank K W = 2)
  (hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ W, (ρM σ).baseChange K w ∈ W)
  (hcont : GaloisActionIsAdicContinuous 𝒪' ρM)

omit [IsDiscreteValuationRing 𝒪'] [Module.Finite 𝒪' M] in

lemma equiv_restrictRep_baseChange (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (y : K ⊗[𝒪'] eigenLattice K W) :
    (isBaseChange_toPlane K W).equiv ((restrictRep K W ρM hW σ).baseChange K y) =
      planeEnd K W ρM hW σ ((isBaseChange_toPlane K W).equiv y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul k v =>
      rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul, map_smul]
      congr 1
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem galoisRepOfEigenPiece_isOrdinaryAt (p : ℕ)
    (hordLine : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∃ L : Submodule K (K ⊗[𝒪'] M), L ≤ W ∧ Module.finrank K L = 1 ∧
        (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ w ∈ L, (ρM σ).baseChange K w ∈ L) ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w ∈ W, (ρM σ).baseChange K w - w ∈ L)) :
    (galoisRepOfEigenPiece K ρM W hW2 hW hcont).IsOrdinaryAt p := by
  refine GaloisRepAdic.isOrdinaryAt_of_stableLine_baseChange K _ p fun P hP => ?_
  obtain ⟨L, hLW, hL1, hLD, hLI⟩ := hordLine P hP

  let e : K ⊗[𝒪'] (galoisRepOfEigenPiece K ρM W hW2 hW hcont).V ≃ₗ[K] W :=
    (isBaseChange_toPlane K W).equiv

  have hecomm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (y : K ⊗[𝒪'] (galoisRepOfEigenPiece K ρM W hW2 hW hcont).V),
      e (((galoisRepOfEigenPiece K ρM W hW2 hW hcont).ρ σ).baseChange K y) =
        planeEnd K W ρM hW σ (e y) :=
    fun σ y => equiv_restrictRep_baseChange K ρM W hW σ y

  let LW : Submodule K W := L.comap W.subtype
  refine ⟨LW.comap (e : K ⊗[𝒪'] (galoisRepOfEigenPiece K ρM W hW2 hW hcont).V →ₗ[K] W),
    ?_, ?_, ?_⟩
  ·
    rw [Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
    exact (Submodule.comapSubtypeEquivOfLe hLW).finrank_eq.trans hL1
  ·
    intro σ hσ w hw
    rw [Submodule.mem_comap] at hw ⊢
    simp only [LinearEquiv.coe_coe] at hw ⊢
    rw [hecomm σ w]
    exact hLD σ hσ (e w : K ⊗[𝒪'] M) hw
  ·
    intro σ hσ w
    rw [Submodule.mem_comap, map_sub]
    simp only [LinearEquiv.coe_coe]
    rw [hecomm σ w]
    exact hLI σ hσ (e w : K ⊗[𝒪'] M) (e w).2

end Ordinary
p2m_reactivate "P2MW.S_W54_exists_galoisRepAdic_of_eigenPiece_ordinary.OrdPtSol.DCut"

end DCut
p2m_reactivate "P2MW.S_W54_exists_galoisRepAdic_of_eigenPiece_ordinary.OrdPtSol.DCut"

end OrdPtSol
p2m_reactivate "P2MW.S_W54_exists_galoisRepAdic_of_eigenPiece_ordinary.OrdPtSol.DCut P2MW.S_W54_exists_galoisRepAdic_of_eigenPiece_ordinary.OrdPtSol"

theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Set ℕ)
    {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪'] [Finite (IsLocalRing.ResidueField 𝒪')]
    [CharZero 𝒪'] (_hp𝒪' : (p : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪')
    (K : Type) [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
    {M : Type} [AddCommGroup M] [Module 𝒪' M] [Module.Finite 𝒪' M] [Module.Free 𝒪' M]
    (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End 𝒪' M)
    (TM : ModularCurve.HeckeAlg →+* Module.End 𝒪' M)
    (χ : CuspForm.heckeAlgebra N 2 S →+* 𝒪')
    (hES :
      ∃ W : Submodule K (K ⊗[𝒪'] M),
        Module.finrank K W = 2 ∧
        ∃ hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ W, (ρM σ).baseChange K w ∈ W,
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), ∀ w ∈ W,
            (TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K w =
              algebraMap 𝒪' K (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • w) ∧
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
            ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
              ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
                LinearMap.trace K W (((ρM σ).baseChange K).restrict (hW σ)) =
                  algebraMap 𝒪' K (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) ∧
          (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
            ∃ L : Submodule K (K ⊗[𝒪'] M), L ≤ W ∧ Module.finrank K L = 1 ∧
              (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ w ∈ L, (ρM σ).baseChange K w ∈ L) ∧
              (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w ∈ W, (ρM σ).baseChange K w - w ∈ L)))
    (hquad : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (_hℓN : ¬ ℓ ∣ N) (_hℓS : ℓ ∉ S),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          ∀ m : M, ρM σ (ρM σ m) - TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩) (ρM σ m)
            + (ℓ : 𝒪') • m = 0)
    (hunr : ∀ q : ℕ, q.Prime → ¬ q ∣ N → q ≠ p →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρM σ = 1)
    (hcont : GaloisActionIsAdicContinuous 𝒪' ρM) :
    ∃ ρ : GaloisRepAdic 𝒪',
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρ.ρ σ) =
              X ^ 2 - C (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C ((ℓ : 𝒪'))) ∧
      (∀ q : ℕ, q.Prime → ¬ q ∣ N → q ≠ p → ρ.IsUnramifiedAt q) ∧
      ρ.IsOrdinaryAt p := by
  obtain ⟨W, hW2, hW, heig, htr, hordLine⟩ := hES
  exact ⟨OrdPtSol.DCut.galoisRepOfEigenPiece K ρM W hW2 hW hcont,
    OrdPtSol.DCut.galoisRepOfEigenPiece_charpoly K N S ρM TM χ W hW2 hW hcont heig htr hquad,
    OrdPtSol.DCut.galoisRepOfEigenPiece_isUnramifiedAt K p N ρM W hW2 hW hcont hunr,
    OrdPtSol.DCut.galoisRepOfEigenPiece_isOrdinaryAt K ρM W hW2 hW hcont p hordLine⟩

end S_W54_exists_galoisRepAdic_of_eigenPiece_ordinary
end P2MW
export P2MW.S_W54_exists_galoisRepAdic_of_eigenPiece_ordinary (solution)
