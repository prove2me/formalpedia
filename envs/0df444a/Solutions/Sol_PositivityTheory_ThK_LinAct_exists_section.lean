-- Prove2me | solution 1 for PositivityTheory.ThK.LinAct.exists_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:52.397573+00:00
-- url     : https://prove2.me/submissions/b0ac16cb-a436-4366-9650-7939cd6a9591

import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_LinearActInt
import Theorems.Thm_PositivityTheory_ThKH_Evl_mem_of_orth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM MeasureTheory ValuativeRel Topology Filter PositivityTheory.ThKH.Evl
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.LinAct
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ ι : Type} [Fintype κ] [Fintype ι] {ψ : AddChar k ℂ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
namespace PositivityTheory.ThK.LinAct
theorem _root_.solution (large₂ : Submodule k ((κ → k) × (κ → k)))
    (hiso : ∀ w ∈ large₂, ∀ w' ∈ large₂, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (hdim : Module.finrank k large₂ = Fintype.card κ)
    (X : (ι → k) →ₗ[k] (κ → k) × (κ → k)) (hXL : ∀ x, X x ∈ large₂ → x = 0) :
    ∃ S : (ι → k) →ₗ[k] (κ → k) × (κ → k), (∀ y, S y ∈ large₂) ∧
      ∀ x y, (X x).1 ⬝ᵥ (S y).2 - (S y).1 ⬝ᵥ (X x).2 = x ⬝ᵥ y := by
  classical
  let B : (ι → k) →ₗ[k] large₂ →ₗ[k] k :=
    LinearMap.mk₂ k (fun x a => (X x).1 ⬝ᵥ a.1.2 - a.1.1 ⬝ᵥ (X x).2)
      (fun a b c => by simp only [map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (fun a b c => by
        simp only [map_smul, Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
      (fun a b c => by simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (fun a b c => by
        simp only [Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
  have hinj : Function.Injective B := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine hXL x (mem_of_orth large₂ hiso hdim _ fun w hw => ?_)
    exact (sub_eq_zero.1 (LinearMap.congr_fun hx ⟨w, hw⟩)).symm
  have hs : Function.Surjective B.flip := LinearMap.flip_surjective_iff₁.2 hinj
  obtain ⟨s, hs'⟩ := B.flip.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hs)
  refine ⟨large₂.subtype ∘ₗ s ∘ₗ (dotProductBilin k k), fun y => (s _).2, fun x y => ?_⟩
  have := LinearMap.congr_fun (LinearMap.congr_fun hs' (dotProductBilin k k y)) x
  rw [dotProduct_comm x y]
  exact this
end PositivityTheory.ThK.LinAct
