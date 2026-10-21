-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P23.finite_bicommutant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:22:59.868845+00:00
-- url     : https://prove2.me/submissions/7deb4609-9d16-4eee-8040-1754f33087f5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23

namespace G64BC

open scoped Matrix

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def rh (A : StarSubalgebra ℂ (Matrix I I ℂ)) :
    A →+* Module.End ℂ (EuclideanSpace ℂ I) :=
  (ContinuousLinearMap.toLinearMapRingHom).comp
    (((Matrix.toEuclideanCLM : Matrix I I ℂ ≃⋆ₐ[ℂ] _) : Matrix I I ℂ →+* _).comp
      (A.subtype : A →+* Matrix I I ℂ))

noncomputable instance modA (A : StarSubalgebra ℂ (Matrix I I ℂ)) :
    Module A (EuclideanSpace ℂ I) := Module.compHom _ (rh A)

theorem smul_def (A : StarSubalgebra ℂ (Matrix I I ℂ)) (a : A) (v : EuclideanSpace ℂ I) :
    a • v = Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (a : Matrix I I ℂ) v := rfl

theorem semisimple (A : StarSubalgebra ℂ (Matrix I I ℂ)) :
    IsSemisimpleModule A (EuclideanSpace ℂ I) := by
  refine { toComplementedLattice := ⟨fun N => ?_⟩ }
  let Nc : Submodule ℂ (EuclideanSpace ℂ I) :=
    { carrier := N
      add_mem' := N.add_mem
      zero_mem' := N.zero_mem
      smul_mem' := fun c v hv => by
        have := N.smul_mem (algebraMap ℂ A c) hv
        convert this using 1
        change _ ↔ (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
          ((algebraMap ℂ A c : A) : Matrix I I ℂ) v) ∈ N
        simp [Algebra.algebraMap_eq_smul_one] }
  let N' : Submodule A (EuclideanSpace ℂ I) :=
    { carrier := Ncᗮ
      add_mem' := Ncᗮ.add_mem
      zero_mem' := Ncᗮ.zero_mem
      smul_mem' := fun a v hv => by
        simp only [SetLike.mem_coe] at hv ⊢
        rw [Submodule.mem_orthogonal] at hv ⊢
        intro w hw
        change inner ℂ w (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (a : Matrix I I ℂ) v) = 0
        rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
        exact hv _ (N.smul_mem (star a) hw) }
  have h := Nc.isCompl_orthogonal
  refine ⟨N', ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    exact (Submodule.disjoint_def.mp h.disjoint) v hv hv'
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : v ∈ Nc ⊔ Ncᗮ := by rw [h.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
    exact Submodule.mem_sup.mpr ⟨y, hy, z, hz, rfl⟩

theorem comm_star (S : Set (Matrix I I ℂ)) (hstar : ∀ A ∈ S, Aᴴ ∈ S) (C : Matrix I I ℂ)
    (hC : ∀ B ∈ S, C * B = B * C) : ∀ B ∈ S, Cᴴ * B = B * Cᴴ := by
  intro B hB
  have h := hC Bᴴ (hstar B hB)
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h2
  exact h2.symm

theorem dc (S : Set (Matrix I I ℂ)) (x : Matrix I I ℂ)
    (hx : ∀ G : Matrix I I ℂ, (∀ B ∈ S, G * B = B * G) → x * G = G * x) :
    x ∈ StarAlgebra.adjoin ℂ S := by
  set A := StarAlgebra.adjoin ℂ S
  haveI := semisimple A
  let T := (Matrix.toEuclideanCLM : Matrix I I ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I))
  have hcomm : ∀ (g : Module.End A (EuclideanSpace ℂ I)) (v : EuclideanSpace ℂ I),
      T x (g v) = g (T x v) := by
    intro g v
    let gl : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I :=
      { toFun := g
        map_add' := g.map_add
        map_smul' := fun c w => by
          have h1 : ∀ w : EuclideanSpace ℂ I, c • w = (algebraMap ℂ A c) • w := by
            intro w
            change _ = T ((algebraMap ℂ A c : A) : Matrix I I ℂ) w
            simp [T, Algebra.algebraMap_eq_smul_one]
          rw [h1 w]
          exact (g.map_smul _ w).trans (h1 (g w)).symm }
    let G : Matrix I I ℂ := T.symm (LinearMap.toContinuousLinearMap gl)
    have hTG : ∀ w, T G w = g w := by
      intro w; simp [G]; rfl
    have hG : ∀ B ∈ S, G * B = B * G := by
      intro B hB
      apply T.injective
      rw [map_mul, map_mul]
      ext1 w
      have := g.map_smul (⟨B, StarAlgebra.subset_adjoin ℂ S hB⟩ : A) w
      change g (T B w) = T B (g w) at this
      show T G (T B w) = T B (T G w)
      rw [hTG, hTG]; exact this
    have := congrArg (fun M => T M v) (hx G hG)
    simp only [map_mul] at this
    change T x (T G v) = T G (T x v) at this
    rw [hTG, hTG] at this
    exact this
  let f : Module.End (Module.End A (EuclideanSpace ℂ I)) (EuclideanSpace ℂ I) :=
    { toFun := fun v => T x v
      map_add' := fun v w => by simp
      map_smul' := fun g v => hcomm g v }
  obtain ⟨r, hr⟩ := jacobson_density f (Finset.univ.image (fun i => EuclideanSpace.single i (1 : ℂ)))
  have hxr : x = (r : Matrix I I ℂ) := by
    apply T.injective
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun I ℂ).toBasis.ext
    intro i
    have := hr (EuclideanSpace.single i 1) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    exact this
  rw [hxr]; exact r.2

end G64BC
noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

open QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
theorem solution (S : Set (Mat I)) (hunital : 1 ∈ S)
    (hstar : ∀ A ∈ S, Aᴴ ∈ S) :
    matrixCommutant (matrixCommutant S) = (StarAlgebra.adjoin ℂ S : Set (Mat I)) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact G64BC.dc S x (fun G hG => hx G hG)
  · let B : StarSubalgebra ℂ (Mat I) :=
      { carrier := matrixCommutant (matrixCommutant S)
        mul_mem' := fun {a b} ha hb C hC => by
          rw [Matrix.mul_assoc, hb C hC, ← Matrix.mul_assoc, ha C hC, Matrix.mul_assoc]
        add_mem' := fun {a b} ha hb C hC => by
          rw [Matrix.add_mul, Matrix.mul_add, ha C hC, hb C hC]
        algebraMap_mem' := fun c C _ => Algebra.commutes c C
        star_mem' := fun {a} ha C hC => by
          have h := ha Cᴴ (G64BC.comm_star S hstar C hC)
          have h2 := congrArg Matrix.conjTranspose h
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h2
          rw [Matrix.star_eq_conjTranspose]
          exact h2.symm }
    have : StarAlgebra.adjoin ℂ S ≤ B := StarAlgebra.adjoin_le (fun s hs C hC => (hC s hs).symm)
    exact this

end
