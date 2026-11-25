-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.rhs_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:28:03.266306+00:00
-- url     : https://prove2.me/submissions/3193f0c4-2a36-46ac-a8bd-6258506d56a8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCHeights
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlockC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlock
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_append_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
private theorem iteratedFDeriv_comp_equiv_eq_of_contDiffOn (hS : IterSymm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ψ : V → ℂ) (Ω : Set V) (hΩ : IsOpen Ω) (hψ : ContDiffOn ℂ ∞ ψ Ω) (c : V) (hc : c ∈ Ω)
    {k m p : ℕ} (e1 : Fin k ≃ Fin p) (e2 : Fin m ≃ Fin p) (v : Fin p → V) :
    iteratedFDeriv ℂ k ψ c (v ∘ e1) = iteratedFDeriv ℂ m ψ c (v ∘ e2) := by
  obtain rfl : k = m := Fin.equiv_iff_eq.mp ⟨e1.trans e2.symm⟩
  rw [← hS V ψ Ω hΩ hψ c hc k (v ∘ e2) (e1.trans e2.symm)]
  congr 1
  funext i
  simp
private theorem iteratedFDeriv_sum_mul_eq_sum_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type} (u : Finset ι)
    (f : ι → E → ℂ) (a : ι → ℂ) (x : E) (k : ℕ) (h : ∀ i ∈ u, ContDiffAt ℂ k (f i) x) :
    iteratedFDeriv ℂ k (fun y => ∑ i ∈ u, a i * f i y) x = ∑ i ∈ u, a i • iteratedFDeriv ℂ k (f i) x := by
  have h1 : (fun y => ∑ i ∈ u, a i * f i y) = ∑ i ∈ u, (fun y => a i • f i y) := by
    funext y
    simp [Finset.sum_apply]
  rw [h1, ← iteratedFDerivWithin_univ, iteratedFDerivWithin_sum_apply uniqueDiffOn_univ (Set.mem_univ _)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [iteratedFDerivWithin_univ]
    exact iteratedFDeriv_const_smul_apply' (h i hi)
  · intro i hi
    exact ((h i hi).const_smul (a i)).contDiffWithinAt
end PositivityTheory.Rg.Sw.LVs.TC
end
end

set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution (hA : IterAffine) (hS : IterSymm) (hN : IterNested) (j : ℕ) (ψ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (Ω : Set (Matrix (Fin n) (Fin n) ℂ)) (hΩ : IsOpen Ω) (h0 : 0 ∈ Ω) (hψ : ContDiffOn ℂ ∞ ψ Ω) :
    detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      ψ (embOn (blkA j) T + embOn (blkB j) S))) =
    ∑ σA : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
      (Equiv.Perm.sign σA : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (Fin n)) ψ 0 (vv (piP j σA τ) ∘ (Fintype.equivFin (Fin n)).symm) := by
  classical
  have hψ0 : ContDiffAt ℂ ∞ ψ 0 := hψ.contDiffAt (hΩ.mem_nhds h0)
  have hG : ∀ w : Fin (Fintype.card (blkB (n := n) j)) → Matrix (blkB (n := n) j) (blkB (n := n) j) ℂ,
      ContDiffAt ℂ (Fintype.card (blkA (n := n) j)) (fun T : Matrix (blkA (n := n) j) (blkA (n := n) j) ℂ =>
        iteratedFDeriv ℂ (Fintype.card (blkB (n := n) j))
          (fun S : Matrix (blkB (n := n) j) (blkB (n := n) j) ℂ => ψ (embOn (blkA j) T + embOn (blkB j) S)) 0 w) 0 := by
    intro w
    have hmem : ∀ᶠ T in 𝓝 (0 : Matrix (blkA (n := n) j) (blkA (n := n) j) ℂ), embL (blkA (n := n) j) T ∈ Ω := by
      apply (embL (blkA (n := n) j)).continuous.continuousAt.preimage_mem_nhds
      simpa using hΩ.mem_nhds h0
    have hev : (fun T : Matrix (blkA (n := n) j) (blkA (n := n) j) ℂ =>
        iteratedFDeriv ℂ (Fintype.card (blkB (n := n) j))
          (fun S : Matrix (blkB (n := n) j) (blkB (n := n) j) ℂ => ψ (embOn (blkA j) T + embOn (blkB j) S)) 0 w)
        =ᶠ[𝓝 0] fun T => iteratedFDeriv ℂ (Fintype.card (blkB (n := n) j)) ψ (embL (blkA (n := n) j) T)
          (fun i => embL (blkB (n := n) j) (w i)) := by
      filter_upwards [hmem] with T hT
      have := hA (Matrix (Fin n) (Fin n) ℂ) (Matrix (blkB (n := n) j) (blkB (n := n) j) ℂ) ψ Ω hΩ hψ
        (embL (blkA (n := n) j) T) hT (embL (blkB (n := n) j)) (Fintype.card (blkB (n := n) j))
      exact congrArg (fun M => M w) this
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have h1 : ContDiffAt ℂ (Fintype.card (blkA (n := n) j))
        (iteratedFDeriv ℂ (Fintype.card (blkB (n := n) j)) ψ) (embL (blkA (n := n) j) 0) := by
      rw [map_zero]
      exact hψ0.iteratedFDeriv_right (by first | exact_mod_cast le_top | (norm_cast; exact le_top) | (exact WithTop.coe_le_coe.mpr le_top) | simp [← Nat.cast_add]; exact_mod_cast le_top)
    have h2 := h1.comp (0 : Matrix (blkA (n := n) j) (blkA (n := n) j) ℂ) (embL (blkA (n := n) j)).contDiff.contDiffAt
    exact (ContinuousMultilinearMap.apply ℂ _ ℂ (fun i => embL (blkB (n := n) j) (w i))).contDiff.contDiffAt.comp _ h2
  unfold detD
  refine Finset.sum_congr rfl fun σA _ => ?_
  rw [iteratedFDeriv_sum_mul_eq_sum_smul _ _ _ _ _ (fun τ _ => hG _), ContinuousMultilinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  have hN' := hN (Matrix (Fin n) (Fin n) ℂ) (Matrix (blkA (n := n) j) (blkA (n := n) j) ℂ)
    (Matrix (blkB (n := n) j) (blkB (n := n) j) ℂ) ψ Ω hΩ hψ 0 h0 (embL (blkA (n := n) j)) (embL (blkB (n := n) j))
    (Fintype.card (blkA (n := n) j)) (Fintype.card (blkB (n := n) j))
    (fun i => single ((Fintype.equivFin (blkA (n := n) j)).symm i) (σA ((Fintype.equivFin (blkA (n := n) j)).symm i)) (1 : ℂ))
    (fun i => single ((Fintype.equivFin (blkB (n := n) j)).symm i) (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) (1 : ℂ))
  simp only [zero_add] at hN'
  erw [hN', append_eq j σA τ, iteratedFDeriv_comp_equiv_eq_of_contDiffOn hS ψ Ω hΩ hψ 0 h0 (epsE j) (Fintype.equivFin (Fin n)).symm (vv (piP j σA τ))]
  ring
end PositivityTheory.Rg.Sw.LVs.TC
