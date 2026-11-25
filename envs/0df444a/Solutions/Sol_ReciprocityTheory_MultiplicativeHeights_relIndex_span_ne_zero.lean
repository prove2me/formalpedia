-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.relIndex_span_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:06:07.68656+00:00
-- url     : https://prove2.me/submissions/44fbd85c-1d61-4453-8089-c0693ca337a3

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_relIndex_span_comb
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_comb_diagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (hb : LinearIndependent K b) (B : Submodule (𝓞 K) (Fin r → K))
    (hbB : ∀ i, b i ∈ B) (D : 𝓞 K) (hD : D ≠ 0)
    (hDB : ∀ x ∈ B, D • x ∈ Submodule.span (𝓞 K) (Set.range b)) :
    (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 := by
  set P := Submodule.span (𝓞 K) (Set.range b) with hP
  let φ : (Fin r → K) →ₗ[𝓞 K] (Fin r → K) := D • LinearMap.id
  have hD' : algebraMap (𝓞 K) K D ≠ 0 := by
    rw [← map_zero (algebraMap (𝓞 K) K)]
    exact (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hD
  have hφ : Function.Injective φ := by
    intro x y hxy
    funext i
    have := congrFun hxy i
    simp only [φ, Algebra.smul_def] at this
    exact mul_left_cancel₀ hD' this
  have hPB : P ≤ B := Submodule.span_le.mpr (Set.range_subset_iff.mpr hbB)
  have hmapP : Submodule.map φ P = Submodule.span (𝓞 K)
      (Set.range (fun j => ∑ i, Matrix.diagonal (fun _ : Fin k => D) i j • b i)) := by
    rw [comb_diagonal, hP, Submodule.map_span, ← Set.range_comp]
    rfl
  have h1 : (Submodule.map φ P).toAddSubgroup ≤ (Submodule.map φ B).toAddSubgroup :=
    Submodule.map_mono hPB
  have h2 : (Submodule.map φ B).toAddSubgroup ≤ P.toAddSubgroup := by
    rintro _ ⟨x, hx, rfl⟩
    exact hDB x hx
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2
  have hdet : (Matrix.diagonal fun _ : Fin k => D).det ≠ 0 := by
    simp [Matrix.det_diagonal, hD]
  have hidx := relIndex_span_comb b hb (Matrix.diagonal fun _ => D) hdet
  rw [← hmapP] at hidx
  have hne : (Submodule.map φ P).toAddSubgroup.relIndex P.toAddSubgroup ≠ 0 := by
    intro h0
    rw [h0] at hidx
    have hn : Algebra.norm ℤ (Matrix.diagonal fun _ : Fin k => D).det ≠ 0 :=
      Algebra.norm_ne_zero_iff.mpr hdet
    simp only [Nat.cast_zero] at hidx
    exact hn (abs_eq_zero.mp hidx.symm)
  have heq : (Submodule.map φ P).toAddSubgroup.relIndex (Submodule.map φ B).toAddSubgroup =
      P.toAddSubgroup.relIndex B.toAddSubgroup := by
    rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hφ
  rw [← heq]
  intro h0
  rw [h0, zero_mul] at hmul
  exact hne hmul.symm
end ReciprocityTheory.MultiplicativeHeights
