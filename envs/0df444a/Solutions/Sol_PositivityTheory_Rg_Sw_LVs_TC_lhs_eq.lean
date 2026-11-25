-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.lhs_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:51.652413+00:00
-- url     : https://prove2.me/submissions/ba1b6f49-704b-495b-b35c-549b9ca15c77

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCHeights
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlockC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlock
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_prod_coef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution (hA : IterAffine) (j : ℕ) (c c' : ℂ) (ψ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (Ω : Set (Matrix (Fin n) (Fin n) ℂ)) (hΩ : IsOpen Ω) (h0 : 0 ∈ Ω) (hψ : ContDiffOn ℂ ∞ ψ Ω) :
    detD (fun t => ψ (bdiag j c c' t)) =
      c ^ (blkA (n := n) j).card * c' ^ (blkB (n := n) j).card *
        ∑ σ : Equiv.Perm (Fin n), if (∀ r, r ∈ blkA (n := n) j ↔ σ r ∈ blkA (n := n) j) then
          (Equiv.Perm.sign σ : ℂ) * iteratedFDeriv ℂ (Fintype.card (Fin n)) ψ 0 (vv σ ∘ (Fintype.equivFin (Fin n)).symm)
          else 0 := by
  classical
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := bdiag j c c'
        map_add' := fun x y => by
          ext a b; simp only [bdiag, Matrix.add_apply]; split_ifs <;> ring
        map_smul' := fun m x => by
          ext a b; simp only [bdiag, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring }
  have hL : ∀ t, L t = bdiag j c c' t := fun t => rfl
  have hfun : (fun t => ψ (bdiag j c c' t)) = fun w => ψ (0 + L w) := by
    funext w; rw [zero_add, hL]
  have hκ : ∀ (σ : Equiv.Perm (Fin n)) (r : Fin n), L (vv σ r) =
      (if r ∈ blkA (n := n) j ∧ σ r ∈ blkA (n := n) j then c
        else if r ∈ blkB (n := n) j ∧ σ r ∈ blkB (n := n) j then c' else 0) • vv σ r := by
    intro σ r
    ext a b
    rw [hL]
    simp only [bdiag, vv, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases hab : r = a ∧ σ r = b
    · obtain ⟨rfl, rfl⟩ := hab; simp
    · simp [hab]
  have hD := hA (Matrix (Fin n) (Fin n) ℂ) (Matrix (Fin n) (Fin n) ℂ) ψ Ω hΩ hψ 0 h0 L (Fintype.card (Fin n))
  unfold detD
  rw [hfun]
  erw [hD]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  erw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hv : (fun i => L (single ((Fintype.equivFin (Fin n)).symm i) (σ ((Fintype.equivFin (Fin n)).symm i)) 1))
      = fun i => (fun r => if r ∈ blkA (n := n) j ∧ σ r ∈ blkA (n := n) j then c
        else if r ∈ blkB (n := n) j ∧ σ r ∈ blkB (n := n) j then c' else 0) ((Fintype.equivFin (Fin n)).symm i) •
          (vv σ ∘ (Fintype.equivFin (Fin n)).symm) i := by
    funext i
    exact hκ σ _
  erw [hv, ContinuousMultilinearMap.map_smul_univ,
    Equiv.prod_comp (Fintype.equivFin (Fin n)).symm (fun r => if r ∈ blkA (n := n) j ∧ σ r ∈ blkA (n := n) j then c
        else if r ∈ blkB (n := n) j ∧ σ r ∈ blkB (n := n) j then c' else 0)]
  split_ifs with hp
  · have hprod : (∏ r : Fin n, if r ∈ blkA (n := n) j ∧ σ r ∈ blkA (n := n) j then c
        else if r ∈ blkB (n := n) j ∧ σ r ∈ blkB (n := n) j then c' else 0)
        = ∏ r : Fin n, if r ∈ blkA (n := n) j then c else c' := by
      refine Finset.prod_congr rfl fun r _ => ?_
      by_cases hr : r ∈ blkA (n := n) j
      · simp [hr, (hp r).mp hr]
      · have hr' : σ r ∉ blkA (n := n) j := fun h => hr ((hp r).mpr h)
        simp [hr, hr', blkB]
    rw [hprod, prod_coef, smul_eq_mul]
    ring
  · push_neg at hp
    obtain ⟨r, hr⟩ := hp
    have hz : (∏ r : Fin n, if r ∈ blkA (n := n) j ∧ σ r ∈ blkA (n := n) j then c
        else if r ∈ blkB (n := n) j ∧ σ r ∈ blkB (n := n) j then c' else 0) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ r) ?_
      rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [h1, h2, blkB]
      · simp [h1, h2, blkB]
    rw [hz, zero_smul, mul_zero, mul_zero]
end PositivityTheory.Rg.Sw.LVs.TC
