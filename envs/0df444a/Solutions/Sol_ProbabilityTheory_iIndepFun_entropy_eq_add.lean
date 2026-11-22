-- Prove2me | solution 1 for ProbabilityTheory.iIndepFun.entropy_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:14:14.626786+00:00
-- url     : https://prove2.me/submissions/33a7a8a5-62b4-4ff7-936c-eb6e828e9c44

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
public import Theorems.Thm_P2M_ProbabilityTheory_iIndepFun_finsets_comp__3666e794ddd7
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_compProd_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_const
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prod
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkLeft
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkRight
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_kernel
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_measure
public import Theorems.Thm_ProbabilityTheory_Kernel_iIndepFun_finsets_comp
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteMiddle_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteRight_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_snd_reverse
public import Theorems.Thm_ProbabilityTheory_iIndepFun_finsets_comp
public import Theorems.Thm_ProbabilityTheory_identDistrib_id
public import Theorems.Thm_ProbabilityTheory_indepFun_zero_measure
public import Theorems.Thm_prod_eq
attribute [local simp] MeasureTheory.Measure.pi_eval_preimage
attribute [local simp] MeasureTheory.Measure.pi_pi_set
attribute [local simp] P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
attribute [local simp] ProbabilityTheory.Kernel.entropy_compProd_deterministic
attribute [local simp] ProbabilityTheory.Kernel.entropy_const
attribute [local simp] ProbabilityTheory.Kernel.entropy_deterministic
attribute [local simp] ProbabilityTheory.Kernel.entropy_prod
attribute [local simp] ProbabilityTheory.Kernel.entropy_prodMkLeft
attribute [local simp] ProbabilityTheory.Kernel.entropy_prodMkRight
attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_kernel
attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_measure
attribute [local simp] ProbabilityTheory.Kernel.swapRight_deleteMiddle_reverse
attribute [local simp] ProbabilityTheory.Kernel.swapRight_deleteRight_reverse
attribute [local simp] ProbabilityTheory.Kernel.swapRight_snd_reverse
attribute [local simp] ProbabilityTheory.identDistrib_id
attribute [local simp] ProbabilityTheory.indepFun_zero_measure
attribute [local simp] prod_eq



set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
open ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
variable [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory.iIndepFun
theorem _root_.solution {Ω S : Type*} [hΩ:
  MeasureSpace Ω] [IsProbabilityMeasure hΩ.volume]
    {m : ℕ} [MeasurableSpace S] [MeasurableSingletonClass S] [Finite S]
    {X : Fin m → Ω → S} (hX : ∀ i, Measurable (X i)) (h_indep : iIndepFun X) :
    H[(fun ω i ↦ X i ω)] = ∑ i, H[X i] := by
  cases nonempty_fintype S
  induction m with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    convert entropy_const Fin.elim0 <;> infer_instance
  | succ m hm =>
  calc
    _ = H[ ⟨(fun ω (i:Fin m) ↦ X i.castSucc ω), X (.last _)⟩ ] := by
      let f : (Fin (m + 1) → S) → (Fin m → S) × S := fun x ↦ (fun i ↦ x i.castSucc,
        x (.last m))
      have hf_inj : Function.Injective f := by
        intro x y hxy
        simp only [Prod.mk.injEq, f] at hxy
        ext i; rcases Fin.eq_castSucc_or_eq_last i with h | rfl
        · obtain ⟨j, rfl⟩ := h; replace hxy := hxy.1; exact congr($hxy j)
        tauto
      have hcomp : (f ∘ fun ω i ↦ X i ω) =
          ⟨(fun ω (i : Fin m) ↦ X i.castSucc ω), X (.last _)⟩ := rfl
      rw [← hcomp]
      exact (entropy_comp_of_injective _ (by fun_prop) f hf_inj).symm
    _ = H[fun ω (i:Fin m) ↦ X i.castSucc ω] + H[X (.last m)] := by
      apply (entropy_pair_eq_add _ _).mpr _ <;> try fun_prop
      let T : Finset (Fin (m + 1)) := {.last m}ᶜ
      let T' : Finset (Fin (m + 1)) := {.last m}
      let φ : (T → S) → (Fin m → S) := fun f j ↦ f ⟨ j.castSucc, by simp [T] ⟩
      let φ' : (T' → S) → S := fun f ↦ f ⟨ .last m, by simp [T'] ⟩
      exact iIndepFun.finsets_comp' (by simp [T', T]) h_indep hX (show Measurable φ by fun_prop)
        (show Measurable φ' by fun_prop)
    _ = ∑ i:Fin m, H[X i.castSucc] + H[X (.last m)] := by
      congr; apply hm _ _
      · intro i; fun_prop
      let T : Fin m → Finset (Fin (m + 1)) := fun i ↦ {i.castSucc}
      let φ : (i:Fin m) → ((_: T i) → S) → S := fun i x ↦ x ⟨ i.castSucc, by simp [T] ⟩
      convert iIndepFun.finsets_comp T _ h_indep hX φ (by fun_prop)
      rw [Finset.pairwiseDisjoint_iff]; rintro ⟨ _, _ ⟩ _ ⟨ _, _ ⟩ _ ⟨ ⟨ _, _ ⟩,
        hij ⟩
      simp [T] at hij ⊢
      grind
    _ = _ := by rw [Fin.sum_univ_castSucc]
end _root_.ProbabilityTheory.iIndepFun
end ProbabilityTheory
