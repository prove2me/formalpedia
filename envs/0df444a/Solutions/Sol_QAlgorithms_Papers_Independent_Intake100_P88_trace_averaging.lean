-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P88.trace_averaging
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-20T09:03:37.540309+00:00
-- url     : https://prove2.me/submissions/ee579ff0-d3df-4c75-8cd6-79ba3aa83121

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88
noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

theorem AuxTA_expL {F A I : Type*} [Field F] [Ring A] [Algebra F A] [Fintype I] [DecidableEq I]
    (t : A →ₗ[F] F) (b c : Module.Basis I F A) (h : IsTraceDualBasis t b c) (x : A) :
    x = ∑ i, t (x * c i) • b i := by
  conv_lhs => rw [← b.sum_repr x]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hx := b.sum_repr x
  generalize b.repr x = r at hx ⊢
  subst hx
  simp [Finset.sum_mul, map_sum, smul_mul_assoc, show ∀ k j, t (b k * c j) = if k = j then 1 else 0 from h]

theorem AuxTA_expR {F A I : Type*} [Field F] [Ring A] [Algebra F A] [Fintype I] [DecidableEq I]
    (t : A →ₗ[F] F) (b c : Module.Basis I F A) (h : IsTraceDualBasis t b c) (x : A) :
    x = ∑ i, t (b i * x) • c i := by
  conv_lhs => rw [← c.sum_repr x]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hx := c.sum_repr x
  generalize c.repr x = r at hx ⊢
  subst hx
  simp [Finset.mul_sum, map_sum, mul_smul_comm, show ∀ k j, t (b k * c j) = if k = j then 1 else 0 from h]

theorem AuxTA_indep {F A I J X : Type*} [Field F] [Ring A] [Algebra F A] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [AddCommGroup X] [Module F X]
    (t : A →ₗ[F] F) (b c : Module.Basis I F A) (h : IsTraceDualBasis t b c)
    (d f : Module.Basis J F A) (h' : IsTraceDualBasis t d f) (β : A →ₗ[F] A →ₗ[F] X) :
    ∑ i, β (b i) (c i) = ∑ j, β (d j) (f j) := by
  calc ∑ i, β (b i) (c i) = ∑ i, β (∑ j, t (b i * f j) • d j) (c i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← AuxTA_expL t d f h' (b i)]
    _ = ∑ j, β (d j) (∑ i, t (b i * f j) • c i) := by
        simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
        exact Finset.sum_comm
    _ = ∑ j, β (d j) (f j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← AuxTA_expR t b c h (f j)]

theorem AuxTA_central {F A I X : Type*} [Field F] [Ring A] [Algebra F A] [Fintype I] [DecidableEq I]
    [AddCommGroup X] [Module F X]
    (t : A →ₗ[F] F) (htr : ∀ a b : A, t (a * b) = t (b * a))
    (b c : Module.Basis I F A) (h : IsTraceDualBasis t b c) (β : A →ₗ[F] A →ₗ[F] X) (z : A) :
    ∑ i, β (z * b i) (c i) = ∑ i, β (b i) (c i * z) := by
  calc ∑ i, β (z * b i) (c i) = ∑ i, β (∑ j, t (z * b i * c j) • b j) (c i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← AuxTA_expL t b c h (z * b i)]
    _ = ∑ j, β (b j) (∑ i, t (b i * (c j * z)) • c i) := by
        simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, htr z, ← mul_assoc, mul_assoc]
    _ = ∑ i, β (b i) (c i * z) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← AuxTA_expR t b c h (c j * z)]

def AuxTA_alg {F A : Type*} [Field F] [Ring A] [Algebra F A] (a : A) : A →ₗ[F] A →ₗ[F] A :=
  LinearMap.mk₂ F (fun x y => x * a * y) (fun x y z => by simp [add_mul])
    (fun r x y => by simp [smul_mul_assoc]) (fun x y z => by simp [mul_add])
    (fun r x y => by simp [mul_smul_comm])

def AuxTA_mod {F A M N : Type*} [Field F] [Ring A] [Algebra F A]
    [AddCommGroup M] [AddCommGroup N] [Module F M] [Module F N]
    [Module A M] [Module A N] [IsScalarTower F A M] [IsScalarTower F A N]
    (phi : M →ₗ[F] N) (m : M) : A →ₗ[F] A →ₗ[F] N :=
  LinearMap.mk₂ F (fun x y => x • phi (y • m)) (fun x y z => by simp [add_smul])
    (fun r x y => by simp [smul_assoc]) (fun x y z => by simp [add_smul])
    (fun r x y => by rw [smul_assoc, map_smul, smul_comm])

theorem _root_.solution (F A M N I : Type*) [Field F] [IsAlgClosed F]
    [Ring A] [Algebra F A] [FiniteDimensional F A] [Fintype I] [DecidableEq I]
    [AddCommGroup M] [AddCommGroup N] [Module F M] [Module F N]
    [Module A M] [Module A N] [IsScalarTower F A M] [IsScalarTower F A N]
    (t : A →ₗ[F] F) (_htrace : ∀ a b : A, t (a * b) = t (b * a))
    (_hnd : TraceNondegenerate (fun a => t a))
    (b c : Module.Basis I F A) (_hdual : IsTraceDualBasis t b c) (phi : M →ₗ[F] N) :
    (∀ a z : A, z * algebraAverage b c a = algebraAverage b c a * z) ∧
    (∀ (J : Type*) [Fintype J] [DecidableEq J] (d f : Module.Basis J F A),
      IsTraceDualBasis t d f → ∀ a : A, algebraAverage b c a = algebraAverage d f a) ∧
    (∃ f : M →ₗ[A] N, ∀ m : M, f m = moduleAverage b c phi m) ∧
    (∀ (J : Type*) [Fintype J] [DecidableEq J] (d f : Module.Basis J F A),
      IsTraceDualBasis t d f → ∀ m : M, moduleAverage b c phi m = moduleAverage d f phi m) := by
  refine ⟨fun a z => ?_, fun J _ _ d f hdf a => ?_, ?_, fun J _ _ d f hdf m => ?_⟩
  · have := AuxTA_central t _htrace b c _hdual (AuxTA_alg (F := F) a) z
    simp only [AuxTA_alg, LinearMap.mk₂_apply] at this
    simp only [algebraAverage, Finset.mul_sum, Finset.sum_mul]
    simpa [mul_assoc] using this
  · have := AuxTA_indep t b c _hdual d f hdf (AuxTA_alg (F := F) a)
    simpa [AuxTA_alg, algebraAverage] using this
  · refine ⟨{ toFun := moduleAverage b c phi
              map_add' := fun x y => by simp [moduleAverage, smul_add, Finset.sum_add_distrib]
              map_smul' := fun z m => ?_ }, fun m => rfl⟩
    have := AuxTA_central t _htrace b c _hdual (AuxTA_mod phi m) z
    simp only [AuxTA_mod, LinearMap.mk₂_apply] at this
    simp only [moduleAverage, RingHom.id_apply, Finset.smul_sum]
    simp only [mul_smul] at this
    exact this.symm
  · have := AuxTA_indep t b c _hdual d f hdf (AuxTA_mod phi m)
    simpa [AuxTA_mod, moduleAverage] using this

end QAlgorithms.Papers.Independent.Intake100.P88
