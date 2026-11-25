-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointIntegral_proof_11cfe16df696
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:54:35.08368+00:00
-- url     : https://prove2.me/submissions/621e100f-d28d-4478-8447-8de216c519f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPointIntegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointIntegral_zeroSet_ker_eval_4be2b8aa0b5c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointIntegral_isFiniteProjection_f9667751e3c9
import Theorems.Thm_ReciprocityTheory_AnForm_mdisc_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.PointIntegral
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.PointIntegral
theorem _root_.solution : PointIntegral.Statement := by
  intro n p f φ
  set J := RingHom.ker (MvPolynomial.eval p)
  have hZ : zeroSet J = {p} := zeroSet_ker_eval p
  have hex : ∃ A : Matrix (Fin 0) (Fin n) ℂ, IsFiniteProjection J A :=
    ⟨0, isFiniteProjection p 0⟩
  rw [varInt, dif_pos hex]
  set A := hex.choose
  have hsheet : IsSheetAt J A p (fun _ => p) := by
    refine ⟨Set.univ, isOpen_univ, trivial, differentiableOn_const _, rfl, ?_, Set.univ,
      Filter.univ_mem, ?_⟩
    · intro y _
      exact ⟨Subsingleton.elim _ _, by rw [hZ]; rfl⟩
    · intro x hx _
      rw [hZ] at hx
      exact hx.1
  have hfib : ∀ y, fibre J A y = {p} := by
    intro y
    ext x
    simp only [fibre, Set.mem_ofPred_eq, hZ, Set.mem_singleton_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, Subsingleton.elim _ _⟩⟩
  have hdens : ∀ y, chartDens J A f φ y = f p := by
    intro y
    rw [chartDens, sheetSum, hfib y, finsum_mem_singleton]
    have hs : ∃ s, IsSheetAt J A p s := ⟨_, hsheet⟩
    rw [dif_pos hs]
    simp [ReciprocityTheory.AnForm.maDens, ReciprocityTheory.AnForm.mdisc_zero]
  rw [chartInt]
  simp_rw [hdens]
  simp [Measure.real, MeasureTheory.volume_pi]
end GroundTheory.Heights₂.Heights.PointIntegral
