-- Prove2me | solution 1 for TierneyMH.Peskun.vLam_monotone
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:27:04.049007+00:00
-- url     : https://prove2.me/submissions/72df6522-0129-4451-825d-76744e8a5d3e

import Definitions.Def_TierneyMH_Peskun_vLam
import Definitions.Def_TierneyMH_Shared_mhKernel
import Mathlib.Tactic
import Definitions.Def_TierneyMH_Shared_OffDiagDominates
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.InfiniteSum.Module

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

namespace PeskunL2
open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace
variable {E : Type*} [MeasurableSpace E]
variable (π : Measure E) [IsProbabilityMeasure π] (H : Kernel E E) [IsMarkovKernel H]
  (hi : Kernel.Invariant H π)

include hi in
theorem ae_integrable (u : Lp ℝ 2 π) : ∀ᵐ x ∂π, Integrable u (H x) := by
  apply Measure.ae_integrable_of_integrable_comp
  rw [hi]
  exact (Lp.memLp u).integrable (by norm_num)

include hi in
theorem integral_congr {f g : E → ℝ} (hfg : f =ᵐ[π] g) :
    (fun x => ∫ y, f y ∂H x) =ᵐ[π] (fun x => ∫ y, g y ∂H x) := by
  have he : ∀ᵐ x ∂π, ∀ᵐ y ∂H x, f y=g y := by
    apply Measure.ae_ae_of_ae_comp
    rw [hi]
    exact hfg
  filter_upwards [he] with x hx
  exact integral_congr_ae hx

noncomputable def opFun (u : Lp ℝ 2 π) : Lp ℝ 2 π :=
  (PeskunProof.markov_L2 π H hi u (Lp.stronglyMeasurable u).measurable (Lp.memLp u)).1.toLp _

theorem opFun_ae (u : Lp ℝ 2 π) :
    opFun π H hi u =ᵐ[π] (fun x => ∫ y, u y ∂H x) := MemLp.coeFn_toLp _

theorem opFun_add (u v : Lp ℝ 2 π) : opFun π H hi (u+v)=opFun π H hi u+opFun π H hi v := by
  apply Lp.ext
  have hcongr := integral_congr π H hi (Lp.coeFn_add u v)
  filter_upwards [opFun_ae π H hi (u+v),opFun_ae π H hi u,opFun_ae π H hi v,
    Lp.coeFn_add (opFun π H hi u) (opFun π H hi v),hcongr,
    ae_integrable π H hi u,ae_integrable π H hi v] with x huv hu hv hsum hc hui hvi
  rw [huv,hsum]
  simp only [Pi.add_apply]
  rw [hu,hv,hc]
  exact integral_add hui hvi

theorem opFun_smul (a : ℝ) (u : Lp ℝ 2 π) : opFun π H hi (a • u)=a • opFun π H hi u := by
  apply Lp.ext
  have hcongr := integral_congr π H hi (Lp.coeFn_smul a u)
  filter_upwards [opFun_ae π H hi (a • u),opFun_ae π H hi u,
    Lp.coeFn_smul a (opFun π H hi u),hcongr] with x hau hu hsmul hc
  rw [hau,hsmul]
  simp only [Pi.smul_apply]
  rw [hu,hc]
  exact integral_smul a u

theorem norm_sq (u : Lp ℝ 2 π) : ‖u‖^2=∫ x, u x^2 ∂π := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

theorem opFun_norm (u : Lp ℝ 2 π) : ‖opFun π H hi u‖ ≤ ‖u‖ := by
  have hh := (PeskunProof.markov_L2 π H hi u (Lp.stronglyMeasurable u).measurable (Lp.memLp u)).2
  have he : (∫ x, (opFun π H hi u x)^2 ∂π) = ∫ x, (∫ y, u y ∂H x)^2 ∂π := by
    apply integral_congr_ae
    filter_upwards [opFun_ae π H hi u] with x hx
    rw [hx]
  rw [← he,← norm_sq,← norm_sq] at hh
  nlinarith [norm_nonneg u,norm_nonneg (opFun π H hi u)]

noncomputable def opLinear : Lp ℝ 2 π →ₗ[ℝ] Lp ℝ 2 π where
  toFun := opFun π H hi
  map_add' := opFun_add π H hi
  map_smul' := opFun_smul π H hi

noncomputable def op : Lp ℝ 2 π →L[ℝ] Lp ℝ 2 π :=
  (opLinear π H hi).mkContinuous 1 (fun u => by simpa [opLinear] using opFun_norm π H hi u)

theorem op_ae (u : Lp ℝ 2 π) : op π H hi u =ᵐ[π] (fun x => ∫ y, u y ∂H x) := opFun_ae π H hi u

theorem op_norm : ‖op π H hi‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem op_inner (u v : Lp ℝ 2 π) :
    ⟪op π H hi u,v⟫ = ∫ x, (∫ y, u y ∂H x)*v x ∂π := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [op_ae π H hi u] with x hx
  simp only [hx,Real.inner_apply,mul_comm]

theorem op_symm (hr : Kernel.IsReversible H π) :
    (op π H hi).toLinearMap.IsSymmetric := by
  intro u v
  change ⟪op π H hi u,v⟫ = ⟪u,op π H hi v⟫
  rw [op_inner,real_inner_comm (op π H hi v),op_inner]
  have hh := PeskunProof.markov_selfadjoint π H hr u v (Lp.stronglyMeasurable u).measurable
    (Lp.memLp u) (Lp.stronglyMeasurable v).measurable (Lp.memLp v)
  simpa only [mul_comm] using hh
end PeskunL2

namespace PeskunL2
open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace
open TierneyMH.Peskun
variable {E : Type*} [MeasurableSpace E]

instance markov_pow (H : Kernel E E) [IsMarkovKernel H] (k : ℕ) : IsMarkovKernel (H^k) := by
  induction k with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ k ih =>
    letI := ih
    rw [show k+1=1+k by omega,Kernel.pow_add,pow_one]
    infer_instance

theorem invariant_pow (π : Measure E) (H : Kernel E E) [IsMarkovKernel H]
    (hi : Kernel.Invariant H π) (k : ℕ) : Kernel.Invariant (H^k) π := by
  induction k with
  | zero => exact Measure.id_comp
  | succ k ih =>
    rw [show k+1=1+k by omega,Kernel.pow_add,pow_one]
    exact hi.comp ih

theorem op_pow_ae (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hi : Kernel.Invariant H π)
    (u : Lp ℝ 2 π) (k : ℕ) :
    ((op π H hi)^k) u =ᵐ[π] (fun x => ∫ y, u y ∂(H^k) x) := by
  induction k with
  | zero =>
    change u =ᵐ[π] (fun x => ∫ y, u y ∂Kernel.id x)
    exact Eventually.of_forall fun x => by simp [Kernel.id_apply,integral_dirac' _ _ (Lp.stronglyMeasurable u)]
  | succ k ih =>
    have hcongr := integral_congr π H hi ih
    have hint := ae_integrable π (H^(k+1)) (invariant_pow π H hi (k+1)) u
    have hkern : H^(k+1)=(H^k) ∘ₖ H := by rw [Kernel.pow_add,pow_one]
    have hop : ((op π H hi)^(k+1)) u=op π H hi (((op π H hi)^k) u) := by
      rw [pow_succ',ContinuousLinearMap.mul_apply]
    rw [hop]
    filter_upwards [op_ae π H hi (((op π H hi)^k) u),hcongr,hint] with x hx hc hiu
    rw [hx,hc,hkern]
    rw [hkern] at hiu
    exact (Kernel.integral_comp hiu).symm

theorem lag_inner (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hi : Kernel.Invariant H π)
    (f : E → ℝ) (hf : MemLp f 2 π) (k : ℕ) :
    ⟪hf.toLp f,((op π H hi)^k) (hf.toLp f)⟫=lagInner π H f k := by
  rw [L2.inner_def]
  unfold lagInner
  apply integral_congr_ae
  have hc := integral_congr π (H^k) (invariant_pow π H hi k) hf.coeFn_toLp
  filter_upwards [hf.coeFn_toLp,op_pow_ae π H hi (hf.toLp f) k,hc] with x hx hp hiu
  simp only [Real.inner_apply,hx,hp,hiu,mul_comm]

theorem op_inner_joint (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hi : Kernel.Invariant H π) (u : Lp ℝ 2 π) :
    ⟪op π H hi u,u⟫=∫ p : E × E, u p.1*u p.2 ∂π ⊗ₘ H := by
  have hp := PeskunProof.joint_memLp π H hi u (Lp.memLp u)
  have hint : Integrable (fun p : E × E => u p.1*u p.2) (π ⊗ₘ H) := hp.1.integrable_mul hp.2
  rw [op_inner,Measure.integral_compProd hint]
  simp only [integral_const_mul,mul_comm]

theorem op_order [MeasurableSingletonClass E] (π : Measure E) [IsProbabilityMeasure π]
    (H₁ H₂ : Kernel E E) [IsMarkovKernel H₁] [IsMarkovKernel H₂]
    (hi₁ : Kernel.Invariant H₁ π) (hi₂ : Kernel.Invariant H₂ π)
    (hd : TierneyMH.Shared.OffDiagDominates π H₁ H₂) (u : Lp ℝ 2 π) :
    ⟪op π H₁ hi₁ u,u⟫ ≤ ⟪op π H₂ hi₂ u,u⟫ := by
  rw [op_inner_joint,op_inner_joint]
  exact sub_nonneg.mp (PeskunProof.positive_operator π H₁ H₂ hi₁ hi₂ hd u
    (Lp.stronglyMeasurable u).measurable (Lp.memLp u))
end PeskunL2

set_option maxHeartbeats 1000000
open scoped BigOperators
namespace TierneyResolvent
variable {V:Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
local notation "⟪" x "," y "⟫" => inner ℝ x y

 theorem variational_compare (C D:V →L[ℝ] V)
    (hD : ∀ x y, ⟪D x,y⟫=⟪x,D y⟫)
    (hpos : ∀ x, 0 ≤ ⟪D x,x⟫)
    (horder : ∀ x, ⟪D x,x⟫ ≤ ⟪C x,x⟫)
    (f u v:V) (hu:C u=f) (hv:D v=f) : ⟪f,u⟫ ≤ ⟪f,v⟫ := by
  have hh := hpos (v-u)
  rw [map_sub,inner_sub_left,inner_sub_right,inner_sub_right,hv] at hh
  have hsym : ⟪D u,v⟫=⟪f,u⟫ := by rw [hD,hv,real_inner_comm]
  rw [hsym] at hh
  have hord := horder u
  rw [hu] at hord
  linarith

private theorem scaled_norm_lt (A:V →L[ℝ] V) (hA:‖A‖ ≤ 1)
    (lam:ℝ) (hl0:0 ≤ lam) (hl1:lam < 1) : ‖lam • A‖ < 1 := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hl0]
  exact (mul_le_mul_of_nonneg_left hA hl0).trans_lt (by simpa using hl1)

 theorem resolvent_order (A B:V →L[ℝ] V)
    (hBsym : ∀ x y, ⟪B x,y⟫=⟪x,B y⟫)
    (hA:‖A‖ ≤ 1) (hB:‖B‖ ≤ 1)
    (horder:∀ x,⟪A x,x⟫ ≤ ⟪B x,x⟫)
    (lam:ℝ) (hl0:0 ≤ lam) (hl1:lam < 1) (f:V) :
    ⟪f,Ring.inverse (1-lam • A) f⟫ ≤ ⟪f,Ring.inverse (1-lam • B) f⟫ := by
  have hnA := scaled_norm_lt A hA lam hl0 hl1
  have hnB := scaled_norm_lt B hB lam hl0 hl1
  apply variational_compare (1-lam • A) (1-lam • B)
  · intro x y
    simp only [sub_apply,ContinuousLinearMap.one_apply,smul_apply,
      inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,hBsym]
  · intro x
    have hb : ⟪B x,x⟫ ≤ ‖x‖^2 := by
      calc
        _ ≤ ‖B x‖*‖x‖ := real_inner_le_norm _ _
        _ ≤ (‖B‖*‖x‖)*‖x‖ := mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg _)
        _ ≤ ‖x‖^2 := by nlinarith only [hB,sq_nonneg ‖x‖]
    simp only [sub_apply,ContinuousLinearMap.one_apply,smul_apply,
      inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
    nlinarith only [hb,hl0,hl1,sq_nonneg ‖x‖]
  · intro x
    simp only [sub_apply,ContinuousLinearMap.one_apply,smul_apply,
      inner_sub_left,real_inner_smul_left]
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left (horder x) hl0) _
  · have hh := congrArg (fun T:V →L[ℝ] V => T f)
      (Ring.mul_inverse_cancel (1-lam • A) (isUnit_one_sub_of_norm_lt_one hnA))
    simpa only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.one_apply] using hh
  · have hh := congrArg (fun T:V →L[ℝ] V => T f)
      (Ring.mul_inverse_cancel (1-lam • B) (isUnit_one_sub_of_norm_lt_one hnB))
    simpa only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.one_apply] using hh

 theorem series_eq_resolvent (A:V →L[ℝ] V) (hA:‖A‖ ≤ 1)
    (lam:ℝ) (hl0:0 ≤ lam) (hl1:lam < 1) (f:V) :
    HasSum (fun k:ℕ => lam^k*⟪f,(A^k) f⟫) ⟪f,Ring.inverse (1-lam • A) f⟫ := by
  have hnA := scaled_norm_lt A hA lam hl0 hl1
  let ell : (V →L[ℝ] V) →L[ℝ] ℝ := (innerSL ℝ f).comp (ContinuousLinearMap.apply ℝ V f)
  have hh := ell.hasSum (hasSum_geom_series_inverse (lam • A) hnA)
  change HasSum (fun k:ℕ => ⟪f,((lam • A)^k) f⟫) ⟪f,Ring.inverse (1-lam • A) f⟫ at hh
  simpa only [smul_pow,smul_apply,real_inner_smul_right] using hh

 theorem series_monotone (A B:V →L[ℝ] V)
    (hBsym : ∀ x y, ⟪B x,y⟫=⟪x,B y⟫)
    (hA:‖A‖ ≤ 1) (hB:‖B‖ ≤ 1)
    (horder:∀ x,⟪A x,x⟫ ≤ ⟪B x,x⟫)
    (lam:ℝ) (hl0:0 ≤ lam) (hl1:lam < 1) (f:V) :
    (∑' k:ℕ,lam^k*⟪f,(A^k) f⟫) ≤ ∑' k:ℕ,lam^k*⟪f,(B^k) f⟫ := by
  rw [(series_eq_resolvent A hA lam hl0 hl1 f).tsum_eq,
    (series_eq_resolvent B hB lam hl0 hl1 f).tsum_eq]
  exact resolvent_order A B hBsym hA hB horder lam hl0 hl1 f
end TierneyResolvent

open TierneyMH.Peskun
open scoped RealInnerProductSpace

theorem solution {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    (π : Measure E) [IsProbabilityMeasure π]
    (P₁ P₂ : Kernel E E) [IsMarkovKernel P₁] [IsMarkovKernel P₂]
    (hrev₁ : Kernel.IsReversible P₁ π) (hrev₂ : Kernel.IsReversible P₂ π)
    (hdom : TierneyMH.Shared.OffDiagDominates π P₁ P₂)
    (f : E → ℝ) (hf_meas : Measurable f) (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π = 0)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) :
    vLam π P₁ f lam ≤ vLam π P₂ f lam := by
  have hi₁ := hrev₁.invariant
  have hi₂ := hrev₂.invariant
  have hmono := TierneyResolvent.series_monotone (PeskunL2.op π P₁ hi₁) (PeskunL2.op π P₂ hi₂)
    (PeskunL2.op_symm π P₂ hi₂ hrev₂) (PeskunL2.op_norm π P₁ hi₁) (PeskunL2.op_norm π P₂ hi₂)
    (PeskunL2.op_order π P₁ P₂ hi₁ hi₂ hdom) lam hlam0 hlam1 (hf.toLp f)
  have ha := (TierneyResolvent.series_eq_resolvent (PeskunL2.op π P₁ hi₁)
    (PeskunL2.op_norm π P₁ hi₁) lam hlam0 hlam1 (hf.toLp f)).summable
  have hb := (TierneyResolvent.series_eq_resolvent (PeskunL2.op π P₂ hi₂)
    (PeskunL2.op_norm π P₂ hi₂) lam hlam0 hlam1 (hf.toLp f)).summable
  simp_rw [PeskunL2.lag_inner] at ha hb hmono
  rw [ha.tsum_eq_zero_add,hb.tsum_eq_zero_add] at hmono
  simp only [pow_zero,one_mul] at hmono
  have he : lagInner π P₁ f 0=lagInner π P₂ f 0 := by
    rw [← PeskunL2.lag_inner π P₁ hi₁ f hf,← PeskunL2.lag_inner π P₂ hi₂ f hf]
    simp
  rw [he] at hmono
  unfold vLam
  linarith
