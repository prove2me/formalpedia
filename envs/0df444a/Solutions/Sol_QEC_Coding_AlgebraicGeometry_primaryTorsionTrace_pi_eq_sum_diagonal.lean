-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_pi_eq_sum_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:19:48.797557+00:00
-- url     : https://prove2.me/submissions/17349224-4c91-4f01-b528-89a76fb298ea

import Mathlib.LinearAlgebra.Pi
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceFunctorial
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PiTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_sum
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_comp_comm

section
namespace QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type w}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
private theorem piEndomorphism_eq_sum_components
    (f : (∀ i, M i) →ₗ[R] ∀ i, M i) :
    f = ∑ i, (f.comp (LinearMap.single R M i)).comp
      (LinearMap.proj i) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.single_apply]
  change f x = ∑ i, f (Pi.single i (x i))
  rw [← map_sum, LinearMap.sum_single_apply]
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type w}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [IsNoetherianRing R] [∀ i, Module.Finite R (M i)]
    [Module.Finite R (∀ i, M i)]
    (p : Ideal R) [p.IsMaximal]
    (f : (∀ i, M i) →ₗ[R] ∀ i, M i) (n : ℕ) :
    primaryTorsionTrace (M := ∀ i, M i) p f n =
      ∑ i, primaryTorsionTrace (M := M i) p
        (piDiagonalBlock f i) n := by
  let component : ι → ((∀ i, M i) →ₗ[R] ∀ i, M i) := fun i =>
    (f.comp (LinearMap.single R M i)).comp (LinearMap.proj i)
  have hdecomp : f = ∑ i, component i :=
    piEndomorphism_eq_sum_components f
  calc
    _ = primaryTorsionTrace (M := ∀ i, M i) p
        (∑ i, component i) n :=
      congrArg (fun g => primaryTorsionTrace p g n) hdecomp
    _ = ∑ i, primaryTorsionTrace (M := ∀ i, M i) p
        (component i) n := by
      simpa only using
        (primaryTorsionTrace_sum p Finset.univ component n)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      change primaryTorsionTrace (M := ∀ j, M j) p
          ((f.comp (LinearMap.single R M i)).comp
            (LinearMap.proj i)) n =
        primaryTorsionTrace (M := M i) p
          ((LinearMap.proj i).comp
            (f.comp (LinearMap.single R M i))) n
      exact primaryTorsionTrace_comp_comm
        (M := ∀ j, M j) (N := M i) p
        (LinearMap.proj i) (f.comp (LinearMap.single R M i)) n
end QEC.Coding.AlgebraicGeometry
