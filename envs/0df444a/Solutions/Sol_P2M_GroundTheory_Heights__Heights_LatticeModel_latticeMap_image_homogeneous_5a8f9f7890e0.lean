-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_latticeMap_image_homogeneous_5a8f9f7890e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:10:15.023252+00:00
-- url     : https://prove2.me/submissions/f49dd4fd-c959-4052-973d-c3f33c37fac5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_smul_mem_dual_ae798d31fc1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeMap_mem_prodSpan_41a267a716ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_prod_mem_latticeMap_image_bdcb5725007a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_isWeightedHomogeneous_coordDeg_iff_c2022d0310d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_smul_09ba6711cb9c


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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}
variable {φ : Fin (N + 1) → Fin m → K}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (hφ : IsDualBasis L φ) {d : ℕ} (hd : 1 ≤ d) :
    latticeMap φ '' {f | IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ N) f (fun _ ↦ d)} =
      (prodSpan L d : Set (MvPolynomial (Fin m) K)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨f, hf, rfl⟩
    exact latticeMap_mem_prodSpan hφ ((isWeightedHomogeneous_coordDeg_iff f _).mp hf)
  · intro p hp
    set Img := latticeMap φ '' {f | IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ N) f (fun _ ↦ d)}
    have hadd : ∀ x ∈ Img, ∀ y ∈ Img, x + y ∈ Img := by
      rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
      exact ⟨f + g, hf.add hg, map_add _ _ _⟩
    have hprod : ∀ u : Fin d → Fin m → K, (∀ i, u i ∈ latticeDual L) → ∏ i, latticeForm (u i) ∈ Img := by
      intro u hu
      obtain ⟨f, hf, hfu⟩ := prod_mem_latticeMap_image hφ u hu
      exact ⟨f, (isWeightedHomogeneous_coordDeg_iff f _).mpr hf, hfu⟩
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    have key : ∀ x ∈ prodSpan L (k + 1), ∀ c : 𝓞 K, C (algebraMap (𝓞 K) K c) * x ∈ Img := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨u, hu, rfl⟩ := hx
        intro c
        have hc : C (algebraMap (𝓞 K) K c) * ∏ i, latticeForm (u i) =
            ∏ i, latticeForm ((Fin.cons (algebraMap (𝓞 K) K c • u 0) (Fin.tail u) : Fin (k + 1) → Fin m → K) i) := by
          rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.cons_zero, ← mul_assoc, latticeForm_smul]
          rfl
        rw [hc]
        refine hprod _ fun i ↦ Fin.cases ?_ (fun j ↦ ?_) i
        · rw [Fin.cons_zero]; exact smul_mem_dual c (hu 0)
        · rw [Fin.cons_succ]; exact hu j.succ
      | zero =>
        intro c
        exact ⟨0, isWeightedHomogeneous_zero _ _ _, by rw [mul_zero, map_zero]⟩
      | add x y _ _ hx hy =>
        intro c
        rw [mul_add]
        exact hadd _ (hx c) _ (hy c)
      | smul a x _ hx =>
        intro c
        rw [← algebraMap_smul K a x, smul_eq_C_mul, ← mul_assoc, ← map_mul, ← map_mul]
        exact hx (c * a)
    simpa using key p hp 1
end GroundTheory.Heights₂.Heights.LatticeModel
