-- Prove2me | solution 1 for SupportVectorMachines.Kernels.theorem_4_16_symmetric_pd_iff_kernel_v2
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:22:21.749746+00:00
-- url     : https://prove2.me/submissions/4062d889-ea04-4867-b0f3-0148f5afe172

/-
Steinwart–Christmann, Theorem 4.16: a function `k : X → X → ℝ` on a nonempty set is a kernel iff it
is symmetric and positive definite.

(⇒) Symmetry is symmetry of the inner product; positive definiteness is
`∑ᵢ∑ⱼ αᵢαⱼ⟪Φ xⱼ, Φ xᵢ⟫ = ‖∑ αᵢ Φ xᵢ‖² ≥ 0`.
(⇐) On the finitely supported functions `X →₀ ℝ` the form `⟪f, g⟫ = ∑ f(y) g(x) k(x, y)` is a
positive semidefinite symmetric bilinear form; the completion of the associated seminormed space
is a real Hilbert space in the universe of `X`, and `x ↦ [δₓ]` is a feature map.
-/
import Mathlib
import Definitions.Def_SupportVectorMachines_Kernels_IsKernel_v2
import Definitions.Def_SupportVectorMachines_Kernels_PositiveDefinite

set_option autoImplicit false

universe u

namespace PdKernelProof

open SupportVectorMachines.Kernels

variable {X : Type u}

/-- Positive definiteness gives nonnegativity of the quadratic form on finitely supported
functions. -/
theorem pd_finsupp {k : X → X → ℝ} (hp : PositiveDefinite k) (f : X →₀ ℝ) :
    0 ≤ f.sum fun y a => f.sum fun x b => a * b * k x y := by
  classical
  have h := hp f.support.card (fun i => f ((f.support.equivFin.symm i : f.support) : X))
    (fun i => ((f.support.equivFin.symm i : f.support) : X))
  have key : ∀ g : X → ℝ, ∑ i : Fin f.support.card, g ((f.support.equivFin.symm i : f.support) : X)
      = ∑ y ∈ f.support, g y := by
    intro g
    rw [← Finset.sum_coe_sort f.support g]
    exact Equiv.sum_comp f.support.equivFin.symm (fun s : f.support => g (s : X))
  simp only [Finsupp.sum]
  calc (0 : ℝ) ≤ _ := h
    _ = _ := by
      rw [key (fun y => ∑ j : Fin f.support.card, f y * f ((f.support.equivFin.symm j : f.support) : X)
        * k ((f.support.equivFin.symm j : f.support) : X) y)]
      refine Finset.sum_congr rfl fun y _ => ?_
      exact key (fun x => f y * f x * k x y)

/-- A kernel is symmetric and positive definite. -/
theorem kernel_imp {k : X → X → ℝ} (hk : IsKernel k) : Symmetric k ∧ PositiveDefinite k := by
  obtain ⟨H, _, _, _, Φ, h⟩ := hk
  refine ⟨fun x x' => ?_, fun n α x => ?_⟩
  · rw [h, h]; exact real_inner_comm _ _
  · have hq : 0 ≤ inner ℝ (∑ i, α i • Φ (x i)) (∑ i, α i • Φ (x i)) := real_inner_self_nonneg
    rw [sum_inner] at hq
    refine hq.trans_eq (Finset.sum_congr rfl fun i _ => ?_)
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right, h, ← mul_assoc, real_inner_comm]

noncomputable section Construction

/-- Finitely supported functions on `X`, carrying the semi-inner product defined by `k`. -/
abbrev Aux (X : Type u) (_k : X → X → ℝ) : Type u := X →₀ ℝ

variable {k : X → X → ℝ}

instance auxCore [hs : Fact (Symmetric k)] [hp : Fact (PositiveDefinite k)] :
    PreInnerProductSpace.Core ℝ (Aux X k) where
  inner f g := f.sum fun y a => g.sum fun x b => a * b * k x y
  conj_inner_symm f g := by
    simp only [conj_trivial]
    rw [Finsupp.sum_comm]
    refine Finsupp.sum_congr fun y _ => Finsupp.sum_congr fun x _ => ?_
    rw [hs.out x y]
    ring
  add_left f f' g := by
    rw [Finsupp.sum_add_index'] <;> simp [← Finsupp.sum_add, add_mul]
  smul_left f g r := by
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.mul_sum, ← mul_assoc]
  re_inner_nonneg f := pd_finsupp hp.out f

instance auxNormed [Fact (Symmetric k)] [Fact (PositiveDefinite k)] :
    SeminormedAddCommGroup (Aux X k) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

instance auxInner [Fact (Symmetric k)] [Fact (PositiveDefinite k)] :
    InnerProductSpace ℝ (Aux X k) := .ofCore _

theorem aux_inner_def [Fact (Symmetric k)] [Fact (PositiveDefinite k)] (f g : Aux X k) :
    inner ℝ f g = f.sum fun y a => g.sum fun x b => a * b * k x y := rfl

end Construction

/-- A symmetric positive definite function is a kernel: the feature space is the completion of
the finitely supported functions with the inner product defined by `k`. -/
theorem kernel_of {k : X → X → ℝ} (hs : Symmetric k) (hp : PositiveDefinite k) : IsKernel k := by
  have : Fact (Symmetric k) := ⟨hs⟩
  have : Fact (PositiveDefinite k) := ⟨hp⟩
  refine ⟨UniformSpace.Completion (Aux X k), inferInstance, inferInstance, inferInstance,
    fun x => ((Finsupp.single x (1 : ℝ) : Aux X k) : UniformSpace.Completion (Aux X k)), ?_⟩
  intro x x'
  rw [UniformSpace.Completion.inner_coe, aux_inner_def]
  simp [Finsupp.sum_single_index, hs x x']

end PdKernelProof

open SupportVectorMachines.Kernels in
theorem solution {X : Type u} [Nonempty X] (k : X → X → ℝ) :
    IsKernel k ↔ Symmetric k ∧ PositiveDefinite k :=
  ⟨PdKernelProof.kernel_imp, fun h => PdKernelProof.kernel_of h.1 h.2⟩
