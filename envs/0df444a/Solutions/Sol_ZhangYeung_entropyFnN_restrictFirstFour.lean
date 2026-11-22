-- Prove2me | solution 1 for ZhangYeung.entropyFnN_restrictFirstFour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:08:08.280287+00:00
-- url     : https://prove2.me/submissions/651f47ef-e253-4ef7-bbe3-95d0251ea5b7

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_compProd_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_const
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prod
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkLeft
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkRight
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_kernel
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_measure
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteMiddle_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteRight_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_snd_reverse
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
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped Topology
universe u
namespace ZhangYeung
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {S : Fin n → Type u}
    [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
    [∀ i, MeasurableSingletonClass (S i)]
    {X : ∀ i : Fin n, Ω → S i} (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) (hn : 4 ≤ n) :
    restrictFirstFour hn (entropyFnN X μ) =
      entropyFnN (fun i : Fin 4 => X (Fin.castLE hn i)) μ := by
  let : ∀ i, Fintype (S i) := fun i => Fintype.ofFinite (S i)
  ext α
  let e : Fin 4 ↪ Fin n := Fin.castLEEmb hn
  let π : (∀ j : α.map e, S j.1) → (∀ i : α, S (e i.1)) :=
    fun g i => g ⟨e i.1, (Finset.mem_map' e).2 i.2⟩
  have hπ : Function.Injective π := by
    intro g₁ g₂ hMapEq
    funext j
    obtain ⟨i, hi, hij⟩ := Finset.mem_map.mp j.2
    have hValueEq : g₁ ⟨e i, by simpa using (Finset.mem_map' e).2 hi⟩ =
        g₂ ⟨e i, by simpa using (Finset.mem_map' e).2 hi⟩ :=
      congrFun hMapEq ⟨i, hi⟩
    have hj : j = ⟨e i, by simpa using (Finset.mem_map' e).2 hi⟩ := Subtype.ext hij.symm
    cases hj
    simpa using hValueEq
  have h_meas : Measurable (fun ω : Ω => fun j : α.map e => X j.1 ω) :=
    measurable_pi_lambda _ (fun j => hX j.1)
  change H[(fun ω : Ω => fun j : α.map e => X j.1 ω); μ] =
    H[(fun ω : Ω => fun i : α => X (e i.1) ω); μ]
  simpa [π, Function.comp_def] using (entropy_comp_of_injective μ h_meas π hπ).symm
end ZhangYeung
