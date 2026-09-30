-- Prove2me | solution 1 for UnderstandingML.kernel_iff_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T19:05:19.324806+00:00
-- url     : https://prove2.me/submissions/a5b4052b-7720-4185-8c19-af1ffb778251

import Definitions.Def_UnderstandingML_Kernel
import Mathlib.Analysis.InnerProductSpace.Completion

open MeasureTheory
open scoped InnerProductSpace

universe u

open UnderstandingML

namespace KernelIffPosSemidefAux

/-- The bilinear form `⟨a, b⟩_K = ∑ᵢ ∑ⱼ aᵢ bⱼ K(i, j)` on finitely supported coefficient vectors. -/
noncomputable def kerInner {X : Type u} (K : X → X → ℝ) (a b : X →₀ ℝ) : ℝ :=
  a.sum fun i ai => b.sum fun j bj => ai * bj * K i j

lemma kerInner_add_left {X : Type u} (K : X → X → ℝ) (a a' b : X →₀ ℝ) :
    kerInner K (a + a') b = kerInner K a b + kerInner K a' b := by
  unfold kerInner
  refine Finsupp.sum_add_index' (fun i => by simp) (fun i r s => ?_)
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun j _ => ?_
  ring

lemma kerInner_smul_left {X : Type u} (K : X → X → ℝ) (r : ℝ) (a b : X →₀ ℝ) :
    kerInner K (r • a) b = r * kerInner K a b := by
  unfold kerInner
  rw [Finsupp.sum_smul_index' (fun i => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun i _ => ?_
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun j _ => ?_
  simp only [smul_eq_mul]
  ring

lemma kerInner_comm {X : Type u} (K : X → X → ℝ) (hsymm : ∀ x x', K x x' = K x' x)
    (a b : X →₀ ℝ) : kerInner K a b = kerInner K b a := by
  unfold kerInner
  rw [Finsupp.sum_comm]
  refine Finsupp.sum_congr fun i _ => Finsupp.sum_congr fun j _ => ?_
  rw [hsymm]
  ring

lemma kerInner_self_nonneg {X : Type u} (K : X → X → ℝ)
    (hpsd : ∀ (m : ℕ) (x : Fin m → X), (gramMatrix K x).PosSemidef) (a : X →₀ ℝ) :
    0 ≤ kerInner K a a := by
  classical
  set s := a.support
  let e : Fin s.card → X := fun k => (s.equivFin.symm k : X)
  have key : ∀ g : X → ℝ, ∑ i ∈ s, g i = ∑ k, g (e k) := by
    intro g
    rw [← Finset.sum_coe_sort s g]
    exact (Equiv.sum_comp s.equivFin.symm (fun i : s => g i)).symm
  have h0 := (hpsd s.card e).dotProduct_mulVec_nonneg (fun k => a (e k))
  have h : 0 ≤ ∑ k, star (a (e k)) * ∑ l, gramMatrix K e k l * a (e l) := h0
  have hK : kerInner K a a = ∑ k, ∑ l, a (e k) * a (e l) * K (e k) (e l) := by
    unfold kerInner
    rw [Finsupp.sum, key]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finsupp.sum, key]
  rw [hK]
  simp only [gramMatrix, Matrix.of_apply, star_trivial, Finset.mul_sum] at h
  convert h using 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end KernelIffPosSemidefAux

open KernelIffPosSemidefAux in
theorem solution {X : Type u} (K : X → X → ℝ) (hsymm : ∀ x x', K x x' = K x' x) :
    IsKernel K ↔ ∀ (m : ℕ) (x : Fin m → X), (gramMatrix K x).PosSemidef := by
  constructor
  · rintro ⟨F, _, _, _, ψ, hψ⟩ m x
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
    · ext i j
      simp [gramMatrix, Matrix.conjTranspose_apply, hsymm]
    · have hw : dotProduct (star v) (Matrix.mulVec (gramMatrix K x) v) =
          ⟪∑ i, v i • ψ (x i), ∑ j, v j • ψ (x j)⟫_ℝ := by
        change ∑ i, star (v i) * ∑ j, gramMatrix K x i j * v j = _
        simp only [gramMatrix, Matrix.of_apply, star_trivial, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
          Finset.mul_sum, hψ]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [real_inner_comm (ψ (x j))]
        ring
      rw [hw]
      exact real_inner_self_nonneg
  · intro hpsd
    let core : PreInnerProductSpace.Core ℝ (X →₀ ℝ) :=
      { inner := kerInner K
        conj_inner_symm := fun a b => by
          simp only [starRingEnd_apply, star_trivial]
          exact kerInner_comm K hsymm b a
        re_inner_nonneg := fun a => by
          simpa using kerInner_self_nonneg K hpsd a
        add_left := kerInner_add_left K
        smul_left := fun a b r => by
          simp only [starRingEnd_apply, star_trivial]
          exact kerInner_smul_left K r a b }
    letI : SeminormedAddCommGroup (X →₀ ℝ) :=
      @InnerProductSpace.Core.toSeminormedAddCommGroup ℝ (X →₀ ℝ) _ _ _ core
    letI : InnerProductSpace ℝ (X →₀ ℝ) := InnerProductSpace.ofCore core
    refine ⟨UniformSpace.Completion (X →₀ ℝ), inferInstance, inferInstance, inferInstance,
      fun x => ((Finsupp.single x 1 : X →₀ ℝ) : UniformSpace.Completion (X →₀ ℝ)),
      fun x x' => ?_⟩
    rw [UniformSpace.Completion.inner_coe]
    show K x x' = kerInner K (Finsupp.single x 1) (Finsupp.single x' 1)
    simp [kerInner]
