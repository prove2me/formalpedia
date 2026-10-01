-- Prove2me | solution 1 for TierneyMH.Peskun.reversible_selfAdjoint_contraction
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:33:53.613817+00:00
-- url     : https://prove2.me/submissions/352c1ec4-c9e3-4eea-926f-f4e4a2ec8fb9

import Definitions.Def_TierneyMH_Shared_mhKernel
import Mathlib.Tactic
import Definitions.Def_TierneyMH_Shared_OffDiagDominates
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open TierneyMH.Shared

namespace PeskunProof
variable {E : Type*} [MeasurableSpace E]

theorem fst_preserving (π : Measure E) [IsProbabilityMeasure π]
    (P : Kernel E E) [IsMarkovKernel P] : MeasurePreserving Prod.fst (π ⊗ₘ P) π :=
  ⟨measurable_fst, Measure.fst_compProd π P⟩

theorem snd_preserving (π : Measure E) [IsProbabilityMeasure π]
    (P : Kernel E E) [IsMarkovKernel P] (hi : Kernel.Invariant P π) :
    MeasurePreserving Prod.snd (π ⊗ₘ P) π :=
  ⟨measurable_snd, (Measure.snd_compProd π P).trans hi⟩

theorem integral_preserving {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) (T : A → B) (hT : MeasurePreserving T μ ν)
    (g : B → ℝ) (hg : Measurable g) : ∫ x, g (T x) ∂μ = ∫ y, g y ∂ν := by
  calc
    ∫ x, g (T x) ∂μ = ∫ y, g y ∂μ.map T :=
      (integral_map hT.measurable.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ y, g y ∂ν := by rw [hT.map_eq]

theorem joint_memLp (π : Measure E) [IsProbabilityMeasure π]
    (P : Kernel E E) [IsMarkovKernel P] (hi : Kernel.Invariant P π)
    (f : E → ℝ) (hf : MemLp f 2 π) :
    MemLp (fun p : E × E => f p.1) 2 (π ⊗ₘ P) ∧
      MemLp (fun p : E × E => f p.2) 2 (π ⊗ₘ P) :=
  ⟨hf.comp_measurePreserving (fst_preserving π P),hf.comp_measurePreserving (snd_preserving π P hi)⟩

theorem energy_integrable (π : Measure E) [IsProbabilityMeasure π]
    (P : Kernel E E) [IsMarkovKernel P] (hi : Kernel.Invariant P π)
    (f : E → ℝ) (hf : MemLp f 2 π) :
    Integrable (fun p : E × E => (f p.1-f p.2)^2) (π ⊗ₘ P) := by
  obtain ⟨h1,h2⟩ := joint_memLp π P hi f hf
  exact (h1.sub h2).integrable_sq

theorem energy_identity (π : Measure E) [IsProbabilityMeasure π]
    (P : Kernel E E) [IsMarkovKernel P] (hi : Kernel.Invariant P π)
    (f : E → ℝ) (hm : Measurable f) (hf : MemLp f 2 π) :
    (∫ p, (f p.1-f p.2)^2 ∂π ⊗ₘ P) =
      2*(∫ x, f x^2 ∂π)-2*(∫ p, f p.1*f p.2 ∂π ⊗ₘ P) := by
  obtain ⟨h1,h2⟩ := joint_memLp π P hi f hf
  have hp : (fun p : E × E => (f p.1-f p.2)^2) =
      (fun p => f p.1^2+f p.2^2-2*(f p.1*f p.2)) := by funext p; ring
  have hs := integral_sub (h1.integrable_sq.add h2.integrable_sq) ((h1.integrable_mul h2).const_mul 2)
  have ha := integral_add h1.integrable_sq h2.integrable_sq
  simp only [Pi.add_apply,Pi.mul_apply] at hs ha
  rw [hp, hs, ha, integral_const_mul]
  rw [integral_preserving _ _ _ (fst_preserving π P) (fun x => f x^2) (hm.pow_const 2),
    integral_preserving _ _ _ (snd_preserving π P hi) (fun x => f x^2) (hm.pow_const 2)]
  ring

theorem remove_diagonal [MeasurableSingletonClass E] (μ : Measure E) (f : E → ℝ) (x : E) :
    (∫ y in ({x} : Set E)ᶜ, (f x-f y)^2 ∂μ) = ∫ y, (f x-f y)^2 ∂μ := by
  rw [← integral_indicator (measurableSet_singleton x).compl]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    by_cases h : y=x
    · subst y; simp
    · simp [h]

theorem offdiag_restrict [MeasurableSingletonClass E] (μ ν : Measure E) (x : E)
    (h : ∀ A : Set E, MeasurableSet A → μ (A \ {x}) ≤ ν (A \ {x})) :
    μ.restrict ({x} : Set E)ᶜ ≤ ν.restrict ({x} : Set E)ᶜ := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA,Measure.restrict_apply hA]
  simpa only [Set.diff_eq] using h A hA

theorem positive_operator [MeasurableSingletonClass E]
    (π : Measure E) [IsProbabilityMeasure π]
    (P₁ P₂ : Kernel E E) [IsMarkovKernel P₁] [IsMarkovKernel P₂]
    (hi1 : Kernel.Invariant P₁ π) (hi2 : Kernel.Invariant P₂ π)
    (hd : OffDiagDominates π P₁ P₂)
    (f : E → ℝ) (hm : Measurable f) (hf : MemLp f 2 π) :
    0 ≤ (∫ p, f p.1*f p.2 ∂π ⊗ₘ P₂) - ∫ p, f p.1*f p.2 ∂π ⊗ₘ P₁ := by
  have h1 := energy_integrable π P₁ hi1 f hf
  have h2 := energy_integrable π P₂ hi2 f hf
  have he1 := (Measure.integrable_compProd_iff h1.aestronglyMeasurable).mp h1
  have he2 := (Measure.integrable_compProd_iff h2.aestronglyMeasurable).mp h2
  have hout1 : Integrable (fun x => ∫ y, (f x-f y)^2 ∂P₁ x) π := by
    simpa only [Real.norm_eq_abs,abs_sq] using he1.2
  have hout2 : Integrable (fun x => ∫ y, (f x-f y)^2 ∂P₂ x) π := by
    simpa only [Real.norm_eq_abs,abs_sq] using he2.2
  have hle : (∫ p, (f p.1-f p.2)^2 ∂π ⊗ₘ P₂) ≤ ∫ p, (f p.1-f p.2)^2 ∂π ⊗ₘ P₁ := by
    rw [Measure.integral_compProd h1,Measure.integral_compProd h2]
    apply integral_mono_ae hout2 hout1
    filter_upwards [hd,he1.1] with x hx hxi
    rw [← remove_diagonal (P₁ x) f x,← remove_diagonal (P₂ x) f x]
    exact integral_mono_measure (offdiag_restrict _ _ x hx)
      (Eventually.of_forall fun y => sq_nonneg _) hxi.restrict
  rw [energy_identity π P₁ hi1 f hm hf,energy_identity π P₂ hi2 f hm hf] at hle
  linarith
end PeskunProof

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CTierney
variable {E : Type*} [MeasurableSpace E]

theorem reversible_iff_swap (π : Measure E) [IsFiniteMeasure π]
    (K : Kernel E E) [IsFiniteKernel K] :
    Kernel.IsReversible K π ↔ (π ⊗ₘ K).map Prod.swap=π ⊗ₘ K := by
  constructor
  · intro h
    apply Measure.ext_prod
    intro A B hA hB
    rw [Measure.map_apply measurable_swap (hA.prod hB)]
    simp only [Set.preimage_swap_prod]
    rw [Measure.compProd_apply_prod hB hA,Measure.compProd_apply_prod hA hB]
    exact h hB hA
  · intro h A B hA hB
    have he := congrArg (fun μ : Measure (E × E) => μ (B ×ˢ A)) h
    rw [Measure.map_apply measurable_swap (hB.prod hA)] at he
    simp only [Set.preimage_swap_prod] at he
    simpa only [Measure.compProd_apply_prod hA hB,Measure.compProd_apply_prod hB hA] using he

theorem rejection_reversible (π : Measure E) (r : E → ℝ≥0∞) (hr : Measurable r) :
    Kernel.IsReversible (Kernel.id.withDensity (fun x (_ : E) => r x)) π := by
  have hval : ∀ (x : E) (S : Set E), MeasurableSet S →
      (Kernel.id.withDensity (fun x (_ : E) => r x)) x S=S.indicator r x := by
    intro x S hS
    rw [Kernel.withDensity_apply' Kernel.id (f := fun x (_ : E) => r x) (hr.comp measurable_fst),Kernel.id_apply]
    simp [lintegral_const,Measure.dirac_apply',hS,Set.indicator]
  intro A B hA hB
  simp_rw [hval _ B hB,hval _ A hA]
  rw [lintegral_indicator hB,lintegral_indicator hA,Measure.restrict_restrict hB,
    Measure.restrict_restrict hA,Set.inter_comm]

theorem mh_reversible_iff (π : Measure E) [IsProbabilityMeasure π]
    (Q : Kernel E E) [IsMarkovKernel Q] (α : E × E → ℝ≥0∞)
    (hα : Measurable α) (hα1 : ∀ p, α p ≤ 1) :
    Kernel.IsReversible (TierneyMH.Shared.mhKernel Q α) π ↔
      ((π ⊗ₘ Q).withDensity α).map Prod.swap=(π ⊗ₘ Q).withDensity α := by
  let K := Q.withDensity (fun x y => α (x,y))
  let r : E → ℝ≥0∞ := fun x => ∫⁻ u, (1-α (x,u)) ∂Q x
  let J : Kernel E E := Kernel.id.withDensity (fun x (_ : E) => r x)
  have hr : Measurable r := (measurable_const.sub hα).lintegral_kernel_prod_right' (κ := Q)
  have hr1 : ∀ x, r x ≤ 1 := by
    intro x
    calc
      r x ≤ ∫⁻ _u, 1 ∂Q x := lintegral_mono (fun _ => tsub_le_self)
      _ = 1 := by simp
  letI : IsFiniteKernel K := Kernel.isFiniteKernel_withDensity_of_bounded Q ENNReal.one_ne_top (fun x y => hα1 (x,y))
  letI : IsFiniteKernel J := Kernel.isFiniteKernel_withDensity_of_bounded Kernel.id ENNReal.one_ne_top (fun x _ => hr1 x)
  have hJ : (π ⊗ₘ J).map Prod.swap=π ⊗ₘ J :=
    (reversible_iff_swap π J).mp (rejection_reversible π r hr)
  change Kernel.IsReversible (K+J) π ↔ _
  rw [reversible_iff_swap,Measure.compProd_add_right,Measure.map_add _ _ measurable_swap,hJ,Measure.add_left_inj]
  have hK : π ⊗ₘ K=(π ⊗ₘ Q).withDensity α := Measure.compProd_withDensity hα
  rw [hK]
end CTierney
namespace PeskunProof
variable {E : Type*} [MeasurableSpace E]

theorem markov_L2 (π : Measure E) [IsProbabilityMeasure π]
    (P : Kernel E E) [IsMarkovKernel P] (hi : Kernel.Invariant P π)
    (f : E → ℝ) (hm : Measurable f) (hf : MemLp f 2 π) :
    MemLp (fun x => ∫ y, f y ∂P x) 2 π ∧
      (∫ x, (∫ y, f y ∂P x)^2 ∂π) ≤ ∫ x, f x^2 ∂π := by
  have h2 := (joint_memLp π P hi f hf).2.integrable_sq
  have he := (Measure.integrable_compProd_iff h2.aestronglyMeasurable).mp h2
  have hout : Integrable (fun x => ∫ y, f y^2 ∂P x) π := by
    simpa only [Real.norm_eq_abs,abs_sq] using he.2
  have hms : StronglyMeasurable (fun x => ∫ y, f y ∂P x) := hm.stronglyMeasurable.integral_kernel
  have hle : ∀ᵐ x ∂π, (∫ y, f y ∂P x)^2 ≤ ∫ y, f y^2 ∂P x := by
    filter_upwards [he.1] with x hx
    have hlp : MemLp f 2 (P x) := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hx
    have hv := variance_nonneg f (P x)
    rw [variance_eq_sub hlp] at hv
    exact sub_nonneg.mp hv
  have hsq : Integrable (fun x => (∫ y, f y ∂P x)^2) π := by
    apply hout.mono' (hms.measurable.pow_const 2).aestronglyMeasurable
    filter_upwards [hle] with x hx
    simpa only [Real.norm_eq_abs,abs_sq] using hx
  refine ⟨(memLp_two_iff_integrable_sq hms.aestronglyMeasurable).mpr hsq, ?_⟩
  calc
    (∫ x, (∫ y, f y ∂P x)^2 ∂π) ≤ ∫ x, ∫ y, f y^2 ∂P x ∂π := integral_mono_ae hsq hout hle
    _ = ∫ p : E × E, f p.2^2 ∂π ⊗ₘ P := (Measure.integral_compProd h2).symm
    _ = ∫ x, f x^2 ∂π := integral_preserving _ _ _ (snd_preserving π P hi) _ (hm.pow_const 2)

theorem markov_mean (π : Measure E) [IsProbabilityMeasure π]
    (P : Kernel E E) [IsMarkovKernel P] (hi : Kernel.Invariant P π)
    (f : E → ℝ) (hm : Measurable f) (hf : MemLp f 2 π) :
    (∫ x, ∫ y, f y ∂P x ∂π) = ∫ x, f x ∂π := by
  have hj := (joint_memLp π P hi f hf).2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  calc
    (∫ x, ∫ y, f y ∂P x ∂π) = ∫ p : E × E, f p.2 ∂π ⊗ₘ P := (Measure.integral_compProd hj).symm
    _ = ∫ x, f x ∂π := integral_preserving _ _ _ (snd_preserving π P hi) _ hm

theorem markov_selfadjoint (π : Measure E) [IsProbabilityMeasure π]
    (P : Kernel E E) [IsMarkovKernel P] (hr : Kernel.IsReversible P π)
    (f g : E → ℝ) (hmf : Measurable f) (hf : MemLp f 2 π)
    (hmg : Measurable g) (hg : MemLp g 2 π) :
    (∫ x, (∫ y, f y ∂P x)*g x ∂π) = ∫ x, f x*(∫ y, g y ∂P x) ∂π := by
  have hi := hr.invariant
  have hswap := (CTierney.reversible_iff_swap π P).mp hr
  obtain ⟨hf1,hf2⟩ := joint_memLp π P hi f hf
  obtain ⟨hg1,hg2⟩ := joint_memLp π P hi g hg
  have hfg : Integrable (fun p : E × E => f p.1*g p.2) (π ⊗ₘ P) := hf1.integrable_mul hg2
  have hgf : Integrable (fun p : E × E => g p.1*f p.2) (π ⊗ₘ P) := hg1.integrable_mul hf2
  calc
    (∫ x, (∫ y, f y ∂P x)*g x ∂π) = ∫ p, g p.1*f p.2 ∂π ⊗ₘ P := by
      rw [Measure.integral_compProd hgf]
      simp_rw [integral_const_mul,mul_comm]
    _ = ∫ p, f p.1*g p.2 ∂(π ⊗ₘ P).map Prod.swap := by
      have he := integral_map (μ := π ⊗ₘ P) measurable_swap.aemeasurable
        ((hmf.comp measurable_fst).mul (hmg.comp measurable_snd)).aestronglyMeasurable
      simpa only [Function.comp_def,Pi.mul_apply,Prod.swap,mul_comm] using he.symm
    _ = ∫ p, f p.1*g p.2 ∂π ⊗ₘ P := by rw [hswap]
    _ = ∫ x, f x*(∫ y, g y ∂P x) ∂π := by
      rw [Measure.integral_compProd hfg]
      simp_rw [integral_const_mul]
end PeskunProof



/-- **Proof of Theorem 4** (Tierney 1998, p. 5): a reversible transition kernel `H` with
invariant distribution `π` represents a self-adjoint operator on
`L²₀(π) = {g ∈ L²(π) : ∫ g dπ = 0}` with spectral radius bounded by one.
Writing `(Hf)(x) = ∫ f(y) H(x, dy)`, for all `f, g ∈ L²₀(π)`:
1. `Hf ∈ L²(π)` and `∫ Hf dπ = 0` (so `H` maps `L²₀(π)` into itself);
2. `⟨Hf, g⟩ = ⟨f, Hg⟩` (self-adjointness);
3. `⟨Hf, Hf⟩ ≤ ⟨f, f⟩` (norm at most one).
For a self-adjoint bounded operator the spectral radius equals the operator norm, so (3) is
the paper's spectral-radius bound. Reversibility is `Kernel.IsReversible H π`, which is
detailed balance (2) on measurable rectangles and implies invariance. -/
theorem solution {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hH : Kernel.IsReversible H π)
    (f g : E → ℝ) (hf_meas : Measurable f) (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π = 0)
    (hg_meas : Measurable g) (hg : MemLp g 2 π) (hg0 : ∫ x, g x ∂π = 0) :
    MemLp (fun x => ∫ y, f y ∂(H x)) 2 π ∧
      ∫ x, (∫ y, f y ∂(H x)) ∂π = 0 ∧
      ∫ x, (∫ y, f y ∂(H x)) * g x ∂π = ∫ x, f x * (∫ y, g y ∂(H x)) ∂π ∧
      ∫ x, (∫ y, f y ∂(H x)) ^ 2 ∂π ≤ ∫ x, f x ^ 2 ∂π := by
  have hi := hH.invariant
  have hl := PeskunProof.markov_L2 π H hi f hf_meas hf
  exact ⟨hl.1, (PeskunProof.markov_mean π H hi f hf_meas hf).trans hf0,
    PeskunProof.markov_selfadjoint π H hH f g hf_meas hf hg_meas hg, hl.2⟩


