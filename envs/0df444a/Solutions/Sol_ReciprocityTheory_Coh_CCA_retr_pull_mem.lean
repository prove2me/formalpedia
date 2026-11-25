-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.retr_pull_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:46:25.944824+00:00
-- url     : https://prove2.me/submissions/238e2571-9909-445d-aa8b-c3dd42e47584

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
namespace ReciprocityTheory.Coh.CCA
theorem _root_.solution (hU : IsOpen (U : Set G)) {M : TRep R G} (n : ℕ) (F : (Fin (n + 1) → U) → M.V)
    (hF : F ∈ hcoch (M.resSub U) U n) :
    (fun x : Fin (n + 1) → G => F fun i => retr U (x i)) ∈ hcoch (M.resSub U) G n := by
  simp only [hcoch] at hF ⊢
  unfold retr rep
  have hcont : Continuous (fun y : G => (⟦y⟧ : Quotient (QuotientGroup.rightRel U)).out) := by
    refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun y => y * x⁻¹) ⁻¹' (U : Set G), hU.preimage (continuous_mul_right _), by simp,
      fun y hy => ?_⟩
    congr 1
    exact (Quotient.sound (QuotientGroup.rightRel_apply.mpr hy)).symm
  refine ⟨?_, fun g x => ?_⟩
  · refine hF.1.comp (continuous_pi fun i => ?_)
    exact ((continuous_apply i).mul ((hcont.comp (continuous_apply i)).inv)).subtype_mk _
  · have hq : ∀ i, (⟦(g : G) * x i⟧ : Quotient (QuotientGroup.rightRel U)) = ⟦x i⟧ := fun i =>
      Quotient.sound (QuotientGroup.rightRel_apply.mpr (by simp))
    dsimp only
    rw [← hF.2]
    congr 1
    funext i
    apply Subtype.ext
    simp [hq i, Subgroup.smul_def, smul_eq_mul, mul_assoc]
end ReciprocityTheory.Coh.CCA
