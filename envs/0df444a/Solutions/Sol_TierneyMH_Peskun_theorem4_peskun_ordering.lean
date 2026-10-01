-- Prove2me | solution 1 for TierneyMH.Peskun.theorem4_peskun_ordering
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:43:22.900479+00:00
-- url     : https://prove2.me/submissions/8c188971-8b22-4c29-994d-4d8a1166815d

import Definitions.Def_TierneyMH_Peskun_vLam
import Definitions.Def_TierneyMH_Shared_mhKernel
import Mathlib.Tactic
import Definitions.Def_TierneyMH_Shared_OffDiagDominates
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance
import Definitions.Def_TierneyMH_Peskun_chainMeasure
import Definitions.Def_TierneyMH_Peskun_lagInner
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.InfiniteSum.Module
section
section
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators RealInnerProductSpace Topology

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
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators RealInnerProductSpace Topology
open TierneyMH.Peskun
namespace PeskunChain
variable {E : Type*} [MeasurableSpace E]

instance (π : Measure E) [IsProbabilityMeasure π] (H : Kernel E E) [IsMarkovKernel H] :
    IsProbabilityMeasure (chainMeasure π H) := by unfold chainMeasure; infer_instance

theorem initial (π : Measure E) (H : Kernel E E) [IsMarkovKernel H] :
    (chainMeasure π H).map (fun ω => ω 0)=π := by
  let κ := fun n : ℕ => H.comap (fun x : (Π _ : Finset.Iic n, E) => x ⟨n,Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)
  change (Kernel.trajMeasure (X := fun _ => E) π κ).map (fun ω => ω 0)=π
  have he : (fun ω : ℕ → E => ω 0) =
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => E)) ∘ (Preorder.frestrictLe 0) := rfl
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [Kernel.trajMeasure,Measure.map_comp _ _ (by fun_prop),Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self,Measure.id_comp]
  exact (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => E)).symm.map_symm_map (μ := π)

theorem projection_step (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (i j : ℕ) (hij : i ≤ j) :
    (chainMeasure π H).map (fun ω => (ω i,ω (j+1))) =
      (Kernel.id ∥ₖ H) ∘ₘ (chainMeasure π H).map (fun ω => (ω i,ω j)) := by
  let P := chainMeasure π H
  let g := fun x : (Π _ : Finset.Iic j, E) => x ⟨j,Finset.mem_Iic.mpr le_rfl⟩
  let f := fun x : (Π _ : Finset.Iic j, E) => x ⟨i,Finset.mem_Iic.mpr hij⟩
  have hf : Measurable f := measurable_pi_apply _
  have hg : Measurable g := measurable_pi_apply _
  have hhist : P.map (Preorder.frestrictLe j) ⊗ₘ H.comap g hg =
      P.map (fun ω => (Preorder.frestrictLe j ω,ω (j+1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  have hleft : P.map (fun ω => (ω i,ω (j+1))) =
      (P.map (Preorder.frestrictLe j) ⊗ₘ H.comap g hg).map (Prod.map f id) := by
    rw [hhist,Measure.map_map (hf.prodMap measurable_id) (by fun_prop)]
    rfl
  have hright : P.map (fun ω => (ω i,ω j)) =
      (P.map (Preorder.frestrictLe j)).map (fun x => (f x,g x)) := by
    rw [Measure.map_map (hf.prodMk hg) (by fun_prop)]
    rfl
  change P.map (fun ω => (ω i,ω (j+1))) = (Kernel.id ∥ₖ H) ∘ₘ P.map (fun ω => (ω i,ω j))
  rw [hleft,hright,Measure.compProd_eq_comp_prod,Measure.map_comp _ _ (hf.prodMap measurable_id),
    ← Kernel.map_prod_eq _ _ hf,Kernel.id_map hf,
    ← Measure.deterministic_comp_eq_map (hf.prodMk hg),Measure.comp_assoc,
    Kernel.comp_deterministic_eq_comap]
  congr 1
  ext x
  simp only [Kernel.prod_apply,Kernel.deterministic_apply,Kernel.comap_apply,
    Kernel.parallelComp_apply,Kernel.id_apply]

theorem marginal_step (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (j : ℕ) :
    (chainMeasure π H).map (fun ω => ω (j+1)) = H ∘ₘ (chainMeasure π H).map (fun ω => ω j) := by
  let P := chainMeasure π H
  let g := fun x : (Π _ : Finset.Iic j, E) => x ⟨j,Finset.mem_Iic.mpr le_rfl⟩
  have hg : Measurable g := measurable_pi_apply _
  have hhist : P.map (Preorder.frestrictLe j) ⊗ₘ H.comap g hg =
      P.map (fun ω => (Preorder.frestrictLe j ω,ω (j+1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  have hh := congrArg (fun μ : Measure ((Π _ : Finset.Iic j,E) × E) => μ.snd) hhist
  rw [Measure.snd_compProd] at hh
  have he : (P.map (fun ω => (Preorder.frestrictLe j ω,ω (j+1)))).snd =
      P.map (fun ω => ω (j+1)) := by
    rw [Measure.snd,Measure.map_map measurable_snd (by fun_prop)]
    rfl
  rw [he] at hh
  change P.map (fun ω => ω (j+1))=H ∘ₘ P.map (fun ω => ω j)
  rw [← hh,← Kernel.comp_deterministic_eq_comap _ hg,← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map hg,Measure.map_map hg (by fun_prop)]
  rfl

theorem marginal (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hi : Kernel.Invariant H π) (j : ℕ) :
    (chainMeasure π H).map (fun ω => ω j)=π := by
  induction j with
  | zero => exact initial π H
  | succ j ih => rw [marginal_step,ih]; exact hi

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

theorem joint (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hi : Kernel.Invariant H π) (i k : ℕ) :
    (chainMeasure π H).map (fun ω => (ω i,ω (i+k)))=π ⊗ₘ (H^k) := by
  induction k with
  | zero =>
    rw [pow_zero]
    change (chainMeasure π H).map (fun ω => (ω i,ω (i+0)))=π ⊗ₘ Kernel.id
    rw [Measure.compProd_id]
    calc
      _ = ((chainMeasure π H).map (fun ω => ω i)).map Function.diag := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = π.map Function.diag := by rw [marginal π H hi i]
  | succ k ih =>
    rw [show i+(k+1)=(i+k)+1 by omega,projection_step π H i (i+k) (by omega),ih,
      Measure.parallelComp_comp_compProd,show k+1=1+k by omega,Kernel.pow_add,pow_one]

theorem coordinate_preserving (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hi : Kernel.Invariant H π) (i : ℕ) :
    MeasurePreserving (fun ω : ℕ → E => ω i) (chainMeasure π H) π :=
  ⟨measurable_pi_apply i,marginal π H hi i⟩

theorem correlation (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hi : Kernel.Invariant H π)
    (f : E → ℝ) (hm : Measurable f) (hf : MemLp f 2 π) (i k : ℕ) :
    (∫ ω, f (ω i)*f (ω (i+k)) ∂chainMeasure π H)=lagInner π H f k := by
  have hpair := PeskunProof.joint_memLp π (H^k) (invariant_pow π H hi k) f hf
  calc
    _ = ∫ p : E × E, f p.1*f p.2 ∂π ⊗ₘ (H^k) :=
      PeskunProof.integral_preserving _ _ _ ⟨by fun_prop,joint π H hi i k⟩ _ (by fun_prop)
    _ = lagInner π H f k := by
      have hp : Integrable (fun p : E × E => f p.1*f p.2) (π ⊗ₘ (H^k)) := hpair.1.integrable_mul hpair.2
      rw [Measure.integral_compProd hp]
      simp only [lagInner,integral_const_mul]

theorem covariance_lag (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hi : Kernel.Invariant H π)
    (f : E → ℝ) (hm : Measurable f) (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π=0) (i j : ℕ) :
    covariance (fun ω => f (ω i)) (fun ω => f (ω j)) (chainMeasure π H)=lagInner π H f (Nat.dist i j) := by
  have hcoord (i : ℕ) : MemLp (fun ω => f (ω i)) 2 (chainMeasure π H) :=
    hf.comp_measurePreserving (coordinate_preserving π H hi i)
  have hmean (i : ℕ) : (∫ ω, f (ω i) ∂chainMeasure π H)=0 :=
    (PeskunProof.integral_preserving _ _ _ (coordinate_preserving π H hi i) f hm).trans hf0
  rw [covariance_eq_sub (hcoord i) (hcoord j),hmean i,hmean j]
  simp only [zero_mul,sub_zero,Pi.mul_apply]
  by_cases hij : i ≤ j
  · rw [Nat.dist_eq_sub_of_le hij]
    convert! correlation π H hi f hm hf i (j-i) using 1
    rw [Nat.add_sub_of_le hij]
  · have hji : j ≤ i := by omega
    rw [Nat.dist_eq_sub_of_le_right hji]
    have hh := correlation π H hi f hm hf j (i-j)
    rw [Nat.add_sub_of_le hji] at hh
    simpa only [mul_comm] using hh

theorem lag_zero (π : Measure E) (H : Kernel E E) (f : E → ℝ) (hm : Measurable f) :
    lagInner π H f 0=∫ x, f x^2 ∂π := by
  change (∫ x, f x * ∫ y, f y ∂Kernel.id x ∂π)=_
  simp only [Kernel.id_apply,integral_dirac' _ _ hm.stronglyMeasurable,pow_two]

end PeskunChain
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators RealInnerProductSpace Topology
open Finset
namespace TierneyFiniteSum
 theorem reflected_Icc (c : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Icc 1 n, c (n+1-i)) = ∑ i ∈ Icc 1 n, c i := by
  refine sum_nbij' (fun i => n+1-i) (fun i => n+1-i) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [mem_Icc] at hi ⊢
    omega
  · intro i hi
    simp only [mem_Icc] at hi ⊢
    omega
  · intro i hi
    simp only [mem_Icc] at hi
    omega
  · intro i hi
    simp only [mem_Icc] at hi
    omega
  · intro i hi
    rfl
 theorem covariance_sum (c : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Icc 1 n, ∑ j ∈ Icc 1 n, c (Nat.dist i j)) =
      (n:ℝ)*c 0+2*∑ k ∈ Icc 1 n, ((n:ℝ)-k)*c k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrow : (∑ i ∈ Icc 1 n, c (Nat.dist i (n+1))) = ∑ i ∈ Icc 1 n, c i := by
      calc
        _ = ∑ i ∈ Icc 1 n, c (n+1-i) := by
          apply sum_congr rfl
          intro i hi
          rw [Nat.dist_eq_sub_of_le (by have := (mem_Icc.mp hi).2; omega)]
        _ = _ := reflected_Icc c n
    have hcol : (∑ i ∈ Icc 1 n, c (Nat.dist (n+1) i)) = ∑ i ∈ Icc 1 n, c i := by
      simpa only [Nat.dist_comm] using hrow
    have hw : (∑ k ∈ Icc 1 (n+1), (((n+1:ℕ):ℝ)-k)*c k) =
        (∑ k ∈ Icc 1 n, ((n:ℝ)-k)*c k)+(∑ k ∈ Icc 1 n, c k) := by
      rw [sum_Icc_succ_top (by omega)]
      simp only [sub_self, zero_mul, add_zero]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      push_cast
      ring
    rw [hw, sum_Icc_succ_top (by omega)]
    simp_rw [sum_Icc_succ_top (by omega : 1 ≤ n+1)]
    rw [sum_add_distrib, ih, hrow, hcol]
    simp only [Nat.dist_self, Nat.cast_add, Nat.cast_one]
    ring
end TierneyFiniteSum
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators RealInnerProductSpace Topology
namespace PeskunResult
open TierneyMH.Peskun
open Filter

theorem variance_identity {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hH : Kernel.IsReversible H π)
    (f : E → ℝ) (hf_meas : Measurable f) (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    variance (pathSum f n) (chainMeasure π H) / n =
      ∫ x, f x ^ 2 ∂π +
        2 * ∑ i ∈ Finset.Icc 1 n, (((n : ℝ) - i) / n) * lagInner π H f i := by
  have hi := hH.invariant
  have hcoord (i : ℕ) : MemLp (fun ω => f (ω i)) 2 (chainMeasure π H) :=
    hf.comp_measurePreserving (PeskunChain.coordinate_preserving π H hi i)
  have hv : variance (pathSum f n) (chainMeasure π H) =
      (n:ℝ)*lagInner π H f 0+2*∑ k ∈ Finset.Icc 1 n, ((n:ℝ)-k)*lagInner π H f k := by
    unfold pathSum
    rw [variance_fun_sum' (fun i _ => hcoord i)]
    simp_rw [PeskunChain.covariance_lag π H hi f hf_meas hf hf0]
    exact TierneyFiniteSum.covariance_sum _ n
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have he : (∑ k ∈ Finset.Icc 1 n, ((n:ℝ)-k)*lagInner π H f k)/(n:ℝ) =
      ∑ k ∈ Finset.Icc 1 n, (((n:ℝ)-k)/(n:ℝ))*lagInner π H f k := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hv,PeskunChain.lag_zero π H f hf_meas,add_div,mul_div_assoc 2,he]
  field_simp

end PeskunResult
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators RealInnerProductSpace Topology

open Filter
open scoped RealInnerProductSpace Topology
namespace PeskunCorrelation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem power_symm (A : V →L[ℝ] V) (hA : ∀ x y, ⟪A x,y⟫=⟪x,A y⟫) (k : ℕ) :
    ∀ x y, ⟪(A^k) x,y⟫=⟪x,(A^k) y⟫ := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro x y
    calc
      _ = ⟪x,(A^k) (A y)⟫ := by rw [pow_succ' A k,ContinuousLinearMap.mul_apply,hA,ih]
      _ = _ := by rw [← ContinuousLinearMap.mul_apply,← pow_succ A k]

theorem even (A : V →L[ℝ] V) (hA : ∀ x y, ⟪A x,y⟫=⟪x,A y⟫) (f : V) (k : ℕ) :
    ⟪f,(A^(2*k)) f⟫=‖(A^k) f‖^2 := by
  rw [two_mul,pow_add,ContinuousLinearMap.mul_apply,← power_symm A hA k,
    real_inner_self_eq_norm_sq]

theorem odd (A : V →L[ℝ] V) (hA : ∀ x y, ⟪A x,y⟫=⟪x,A y⟫) (f : V) (k : ℕ) :
    ⟪f,(A^(2*k+1)) f⟫=⟪(A^k) f,A ((A^k) f)⟫ := by
  rw [show 2*k+1=k+(k+1) by omega,pow_add,ContinuousLinearMap.mul_apply,
    ← power_symm A hA k,pow_succ' A k,ContinuousLinearMap.mul_apply]

theorem contract (A : V →L[ℝ] V) (hA : ‖A‖ ≤ 1) (x : V) : ‖A x‖ ≤ ‖x‖ := by
  simpa using (A.le_opNorm x).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg x))

theorem even_antitone (A : V →L[ℝ] V) (hA : ∀ x y, ⟪A x,y⟫=⟪x,A y⟫)
    (hAn : ‖A‖ ≤ 1) (f : V) : Antitone (fun k => ⟪f,(A^(2*k)) f⟫) := by
  apply antitone_nat_of_succ_le
  intro k
  rw [even A hA,even A hA,pow_succ' A k,ContinuousLinearMap.mul_apply]
  have hh := contract A hAn ((A^k) f)
  nlinarith [norm_nonneg ((A^k) f),norm_nonneg (A ((A^k) f))]

theorem pair_nonneg (A : V →L[ℝ] V) (hA : ∀ x y, ⟪A x,y⟫=⟪x,A y⟫)
    (hAn : ‖A‖ ≤ 1) (f : V) (k : ℕ) :
    0 ≤ ⟪f,(A^(2*k)) f⟫+⟪f,(A^(2*k+1)) f⟫ := by
  rw [even A hA,odd A hA]
  have hh := abs_real_inner_le_norm ((A^k) f) (A ((A^k) f))
  have hc := contract A hAn ((A^k) f)
  have hmul := mul_le_mul_of_nonneg_left hc (norm_nonneg ((A^k) f))
  have hneg := neg_le_abs ⟪(A^k) f,A ((A^k) f)⟫
  nlinarith

theorem bounded (A : V →L[ℝ] V) (hAn : ‖A‖ ≤ 1) (f : V) (k : ℕ) :
    |⟪f,(A^k) f⟫| ≤ ‖f‖^2 := by
  have hc : ‖(A^k) f‖ ≤ ‖f‖ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ' A k,ContinuousLinearMap.mul_apply]
      exact (contract A hAn _).trans ih
  have hh := abs_real_inner_le_norm f ((A^k) f)
  have hm := mul_le_mul_of_nonneg_left hc (norm_nonneg f)
  nlinarith

theorem even_limit (A : V →L[ℝ] V) (hA : ∀ x y, ⟪A x,y⟫=⟪x,A y⟫)
    (hAn : ‖A‖ ≤ 1) (f : V) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto (fun k => ⟪f,(A^(2*k)) f⟫) atTop (𝓝 L) := by
  have ha := even_antitone A hA hAn f
  have hnon (k : ℕ) : 0 ≤ ⟪f,(A^(2*k)) f⟫ := by rw [even A hA]; positivity
  have hb : BddBelow (Set.range (fun k => ⟪f,(A^(2*k)) f⟫)) := ⟨0,by rintro _ ⟨k,rfl⟩; exact hnon k⟩
  refine ⟨⨅ k, ⟪f,(A^(2*k)) f⟫,?_,tendsto_atTop_ciInf ha hb⟩
  exact le_ciInf hnon
end PeskunCorrelation
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators RealInnerProductSpace Topology
namespace PeskunResult
open TierneyMH.Peskun MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
variable {E : Type*} [MeasurableSpace E]

set_option maxHeartbeats 1000000 in
theorem pathSum_memLp (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hi : Kernel.Invariant H π)
    (f : E → ℝ) (hf : MemLp f 2 π) (n : ℕ) : MemLp (pathSum f n) 2 (chainMeasure π H) := by
  unfold pathSum
  exact memLp_finsetSum _ (fun i _ => hf.comp_measurePreserving (PeskunChain.coordinate_preserving π H hi i))

theorem evariance_ratio (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hi : Kernel.Invariant H π)
    (f : E → ℝ) (hf : MemLp f 2 π) (n : ℕ) (hn : 1 ≤ n) :
    evariance (pathSum f n) (chainMeasure π H)/(n:ℝ≥0∞) =
      ENNReal.ofReal (variance (pathSum f n) (chainMeasure π H)/(n:ℝ)) := by
  have hp : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [ENNReal.ofReal_div_of_pos hp,(pathSum_memLp π H hi f hf n).ofReal_variance_eq]
  simp

noncomputable def V (r : ℕ → ℝ) (n : ℕ) : ℝ :=
  r 0+2*∑ i ∈ Finset.Icc 1 n, (((n:ℝ)-i)/(n:ℝ))*r i

theorem ratio_eq_V (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hr : Kernel.IsReversible H π)
    (f : E → ℝ) (hm : Measurable f) (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π=0)
    (n : ℕ) (hn : 1 ≤ n) :
    evariance (pathSum f n) (chainMeasure π H)/(n:ℝ≥0∞)=ENNReal.ofReal (V (lagInner π H f) n) := by
  rw [evariance_ratio π H hr.invariant f hf n hn,variance_identity π H hr f hm hf hf0 n hn]
  unfold V
  rw [PeskunChain.lag_zero π H f hm]

theorem V_nonneg (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hr : Kernel.IsReversible H π)
    (f : E → ℝ) (hm : Measurable f) (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π=0) (n : ℕ) :
    0 ≤ V (lagInner π H f) n := by
  by_cases hn : n=0
  · subst n
    simp only [V,Finset.Icc_eq_empty_of_lt (by omega : 0 < (1:ℕ)),Finset.sum_empty,mul_zero,add_zero]
    rw [PeskunChain.lag_zero π H f hm]
    exact integral_nonneg fun x => sq_nonneg _
  · have hpos : (0:ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have he := variance_identity π H hr f hm hf hf0 n (by omega)
    rw [← PeskunChain.lag_zero π H f hm] at he
    change 0 ≤ lagInner π H f 0+2*∑ i ∈ Finset.Icc 1 n, (((n:ℝ)-i)/(n:ℝ))*lagInner π H f i
    rw [← he]
    exact div_nonneg (variance_nonneg _ _) hpos.le
end PeskunResult
end
end

section
set_option maxHeartbeats 1500000
open Filter Topology Finset
namespace TierneyVarianceLimit
noncomputable section

def weight (n k:ℕ) : ℝ := if n=0 then 0 else max (1-(2*(k:ℝ)+1)/(n:ℝ)) 0
def triangle (s:ℕ → ℝ) (n:ℕ) : ℝ := ∑ k∈range n, weight n k*s k

 theorem weight_nonneg (n k:ℕ) : 0 ≤ weight n k := by
  unfold weight
  split_ifs <;> simp [le_max_right]
 theorem weight_le_one (n k:ℕ) : weight n k ≤ 1 := by
  unfold weight
  split_ifs with hn
  · norm_num
  · apply max_le _ (by norm_num)
    have hh : 0 ≤ (2*(k:ℝ)+1)/(n:ℝ) := by positivity
    linarith
 theorem weight_zero (n k:ℕ) (h:n ≤ k) : weight n k=0 := by
  unfold weight
  split_ifs with hn
  · rfl
  · apply max_eq_right
    have hnpos : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hk : (n:ℝ) ≤ k := by exact_mod_cast h
    have hh : 1 ≤ (2*(k:ℝ)+1)/(n:ℝ) := (le_div_iff₀ hnpos).mpr (by nlinarith)
    linarith
 theorem weight_tendsto (k:ℕ) : Tendsto (fun n => weight n k) atTop (𝓝 1) := by
  have hh : Tendsto (fun n:ℕ => (2*(k:ℝ)+1)/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hm := ((tendsto_const_nhds (x:=(1:ℝ))).sub hh).max (tendsto_const_nhds (x:=(0:ℝ)))
  norm_num only [sub_zero,max_eq_left zero_le_one] at hm
  apply hm.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp [weight,show n ≠ 0 by omega]
 theorem triangle_tsum (s:ℕ → ℝ) (n:ℕ) :
    triangle s n=∑' k:ℕ,weight n k*s k := by
  symm
  apply tsum_eq_sum
  intro k hk
  rw [weight_zero n k (by simpa only [mem_range,not_lt] using hk),zero_mul]
 theorem triangle_tendsto (s:ℕ → ℝ) (hs:∀ k,0 ≤ s k) (hsum:Summable s) :
    Tendsto (triangle s) atTop (𝓝 (∑' k,s k)) := by
  have hlim := tendsto_tsum_of_dominated_convergence hsum
    (fun k => by simpa using (weight_tendsto k).mul_const (s k))
    (Eventually.of_forall (fun n k => show ‖weight n k*s k‖ ≤ s k from by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (weight_nonneg n k) (hs k))]
      simpa using mul_le_mul_of_nonneg_right (weight_le_one n k) (hs k)))
  simpa only [← triangle_tsum] using hlim
 theorem triangle_tendsto_top (s:ℕ → ℝ) (hs:∀ k,0 ≤ s k) (hsum:¬ Summable s) :
    Tendsto (triangle s) atTop atTop := by
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg hs).mp hsum
  apply tendsto_atTop.mpr
  intro M
  obtain ⟨N,hN⟩ := (hdiv.eventually (eventually_gt_atTop M)).exists
  have hpart : Tendsto (fun n:ℕ => ∑ k∈range N,weight n k*s k) atTop (𝓝 (∑ k∈range N,s k)) := by
    convert tendsto_finsetSum (range N) (fun k hk => (weight_tendsto k).mul_const (s k)) using 1 <;> simp
  have hevent := hpart.eventually (lt_mem_nhds hN)
  filter_upwards [hevent,eventually_ge_atTop N] with n hn hNn
  apply hn.le.trans
  apply sum_le_sum_of_subset_of_nonneg (range_mono hNn)
  intro k hk hk'
  exact mul_nonneg (weight_nonneg n k) (hs k)

 def halfCount (n:ℕ) : ℕ := (n+1)/2
 theorem halfCount_bounds (n:ℕ) : n ≤ 2*halfCount n ∧ 2*halfCount n ≤ n+1 := by
  dsimp [halfCount]
  omega
 theorem halfCount_atTop : Tendsto halfCount atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  filter_upwards [eventually_ge_atTop (2*N)] with n hn
  have hh := halfCount_bounds n
  omega
 theorem halfCount_ratio : Tendsto (fun n:ℕ => 2*(halfCount n:ℝ)/(n:ℝ)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun n:ℕ => (1:ℝ)/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using tendsto_const_nhds.add hinv)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hp : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    apply (le_div_iff₀ hp).mpr
    simpa only [one_mul] using (show (n:ℝ) ≤ 2*(halfCount n:ℝ) by exact_mod_cast (halfCount_bounds n).1)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hp : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    apply (div_le_iff₀ hp).mpr
    have hh : 2*(halfCount n:ℝ) ≤ (n:ℝ)+1 := by exact_mod_cast (halfCount_bounds n).2
    field_simp
    nlinarith only [hh]
 theorem even_average_tendsto (a:ℕ → ℝ) (L:ℝ) (ha:Tendsto a atTop (𝓝 L)) :
    Tendsto (fun n:ℕ => (2/(n:ℝ))*∑ k∈range (halfCount n),a k) atTop (𝓝 L) := by
  have hh := halfCount_ratio.mul (ha.cesaro.comp halfCount_atTop)
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hp : halfCount n ≠ 0 := by have hh:=halfCount_bounds n; omega
  have hpr : (halfCount n:ℝ) ≠ 0 := by exact_mod_cast hp
  dsimp only [Function.comp_def]
  field_simp

 theorem sum_pair (f:ℕ → ℝ) (m:ℕ) :
    (∑ i∈range (2*m),f i)=∑ k∈range m,(f (2*k)+f (2*k+1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1)=(2*m+1)+1 by omega,sum_range_succ,sum_range_succ,ih,sum_range_succ]
    ring
 theorem weighted_pair (r:ℕ → ℝ) (N:ℝ) (m:ℕ) :
    (∑ i∈range (2*m),(N-i)*r i)=
      (∑ k∈range m,(N-(2*(k:ℝ)+1))*(r (2*k)+r (2*k+1)))+
      ∑ k∈range m,r (2*k) := by
  rw [sum_pair,← sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  push_cast
  ring
 theorem weighted_half (r:ℕ → ℝ) (n:ℕ) :
    (∑ i∈range n,((n:ℝ)-i)*r i)=
      (∑ k∈range (halfCount n),((n:ℝ)-(2*(k:ℝ)+1))*(r (2*k)+r (2*k+1)))+
      ∑ k∈range (halfCount n),r (2*k) := by
  have hn : n=2*(n/2) ∨ n=2*(n/2)+1 := by omega
  rcases hn with hn|hn
  · have hq : halfCount n=n/2 := by dsimp [halfCount];omega
    rw [hq]
    nth_rw 1 [hn]
    exact weighted_pair r (n:ℝ) (n/2)
  · have hq : halfCount n=n/2+1 := by dsimp [halfCount];omega
    rw [hq]
    nth_rw 1 [hn]
    rw [sum_range_succ,weighted_pair,sum_range_succ,sum_range_succ]
    have hnr : (n:ℝ)=2*((n/2:ℕ):ℝ)+1 := by exact_mod_cast hn
    rw [hnr]
    push_cast
    ring

 theorem triangle_half (s:ℕ → ℝ) (n:ℕ) (hn:0 < n) :
    triangle s n=(1/(n:ℝ))*∑ k∈range (halfCount n),((n:ℝ)-(2*(k:ℝ)+1))*s k := by
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have hq : halfCount n ≤ n := by have hh:=halfCount_bounds n;omega
  have htruncate : (∑ k∈range n,weight n k*s k)=(∑ k∈range (halfCount n),weight n k*s k) := by
    symm
    apply sum_subset (range_mono hq)
    intro k hk hkn
    have hkq : halfCount n ≤ k := by simpa only [mem_range,not_lt] using hkn
    have hkpos : (n:ℝ) ≤ 2*(k:ℝ)+1 := by
      have hh:=halfCount_bounds n
      exact_mod_cast (show n ≤ 2*k+1 by omega)
    have hh : 1 ≤ (2*(k:ℝ)+1)/(n:ℝ) := (le_div_iff₀ hnp).mpr (by simpa using hkpos)
    simp only [weight,if_neg (Nat.ne_of_gt hn),max_eq_right (by linarith : 1-(2*(k:ℝ)+1)/(n:ℝ) ≤ 0),zero_mul]
  rw [triangle,htruncate,mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : 2*k+1 ≤ n := by have hh:=halfCount_bounds n;have:=mem_range.mp hk;omega
  have hkr : 2*(k:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast hkn
  have hh : (2*(k:ℝ)+1)/(n:ℝ) ≤ 1 := (div_le_iff₀ hnp).mpr (by simpa using hkr)
  rw [weight,if_neg (Nat.ne_of_gt hn),max_eq_left (by linarith)]
  field_simp

 def variance (r:ℕ → ℝ) (n:ℕ) : ℝ :=
    r 0+2*∑ i∈Icc 1 n,(((n:ℝ)-i)/(n:ℝ))*r i
 theorem variance_decomposition (r:ℕ → ℝ) (n:ℕ) (hn:0 < n) :
    variance r n=2*triangle (fun k=>r (2*k)+r (2*k+1)) n+
      (2/(n:ℝ))*∑ k∈range (halfCount n),r (2*k)-r 0 := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hI : (∑ i∈range n,((n:ℝ)-i)*r i)=
      (n:ℝ)*r 0+∑ i∈Icc 1 n,((n:ℝ)-i)*r i := by
    have hh := sum_range_eq_add_Ico (fun i:ℕ=>((n:ℝ)-i)*r i) (Nat.succ_pos n)
    rw [sum_range_succ,Nat.succ_eq_add_one,Ico_add_one_right_eq_Icc] at hh
    simpa only [Nat.cast_zero,sub_zero,sub_self,zero_mul,add_zero] using hh
  rw [triangle_half _ n hn]
  have hw := weighted_half r n
  unfold variance
  have hsum : (∑ i∈Icc 1 n,(((n:ℝ)-i)/(n:ℝ))*r i)=
      (1/(n:ℝ))*∑ i∈Icc 1 n,((n:ℝ)-i)*r i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    ring
  rw [hsum]
  field_simp
  nlinarith only [hw,hI]

 theorem triangle_ennreal (s:ℕ → ℝ) (hs:∀ k,0 ≤ s k) :
    Tendsto (fun n=>ENNReal.ofReal (triangle s n)) atTop (𝓝 (∑' k,ENNReal.ofReal (s k))) := by
  by_cases hsum:Summable s
  · simpa only [ENNReal.ofReal_tsum_of_nonneg hs hsum] using ENNReal.tendsto_ofReal (triangle_tendsto s hs hsum)
  · have htop : (∑' k,ENNReal.ofReal (s k))=⊤ := by
      by_contra hh
      have h := ENNReal.summable_toReal hh
      simp only [ENNReal.toReal_ofReal (hs _)] at h
      exact hsum h
    rw [htop]
    exact ENNReal.tendsto_ofReal_atTop.comp (triangle_tendsto_top s hs hsum)

 theorem variance_real_limit (r:ℕ → ℝ) (L:ℝ)
    (heven:Tendsto (fun k=>r (2*k)) atTop (𝓝 L))
    (hs:∀ k,0 ≤ r (2*k)+r (2*k+1))
    (hsum:Summable (fun k=>r (2*k)+r (2*k+1))) :
    Tendsto (variance r) atTop (𝓝 (2*(∑' k,(r (2*k)+r (2*k+1)))+L-r 0)) := by
  have hh := (((triangle_tendsto _ hs hsum).const_mul 2).add
    (even_average_tendsto _ L heven)).sub_const (r 0)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (variance_decomposition r n (by omega)).symm

 theorem variance_extended_limit (r:ℕ → ℝ) (L:ℝ)
    (ha:∀ k,0 ≤ r (2*k)) (heven:Tendsto (fun k=>r (2*k)) atTop (𝓝 L))
    (hs:∀ k,0 ≤ r (2*k)+r (2*k+1)) :
    Tendsto (fun n=>ENNReal.ofReal (variance r n)) atTop
      (𝓝 ((2:ENNReal)*(∑' k,ENNReal.ofReal (r (2*k)+r (2*k+1)))+
        ENNReal.ofReal L-ENNReal.ofReal (r 0))) := by
  have ht := triangle_ennreal (fun k=>r (2*k)+r (2*k+1)) hs
  have he := ENNReal.tendsto_ofReal (even_average_tendsto _ L heven)
  have htwo : Tendsto (fun n=>(2:ENNReal)*ENNReal.ofReal (triangle (fun k=>r (2*k)+r (2*k+1)) n)) atTop
      (𝓝 ((2:ENNReal)*(∑' k,ENNReal.ofReal (r (2*k)+r (2*k+1))))) := by
    exact ENNReal.Tendsto.mul tendsto_const_nhds (Or.inl (by norm_num)) ht (Or.inr (by norm_num))
  have hh := ENNReal.Tendsto.sub (htwo.add he) (tendsto_const_nhds (x:=ENNReal.ofReal (r 0))) (Or.inr ENNReal.ofReal_ne_top)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have ht0 : 0 ≤ triangle (fun k=>r (2*k)+r (2*k+1)) n :=
    sum_nonneg (fun k hk=>mul_nonneg (weight_nonneg n k) (hs k))
  have he0 : 0 ≤ (2/(n:ℝ))*∑ k∈range (halfCount n),r (2*k) :=
    mul_nonneg (by positivity) (sum_nonneg (fun k hk=>ha k))
  have hr0 : 0 ≤ r 0 := by simpa using ha 0
  rw [variance_decomposition r n (by omega)]
  rw [ENNReal.ofReal_sub _ hr0,ENNReal.ofReal_add (by positivity) he0,ENNReal.ofReal_mul (p:=2) (q:=triangle (fun k=>r (2*k)+r (2*k+1)) n) (by norm_num)]
  norm_num

 theorem variance_limit_exists (r:ℕ → ℝ) (ha:∀ k,0 ≤ r (2*k))
    (hanti:Antitone (fun k=>r (2*k))) (hs:∀ k,0 ≤ r (2*k)+r (2*k+1)) :
    ∃ v:ENNReal,Tendsto (fun n=>ENNReal.ofReal (variance r n)) atTop (𝓝 v) := by
  have hb : BddBelow (Set.range (fun k=>r (2*k))) := ⟨0,by rintro _ ⟨k,rfl⟩;exact ha k⟩
  exact ⟨_,variance_extended_limit r _ ha (tendsto_atTop_ciInf hanti hb) hs⟩
end
end TierneyVarianceLimit
end

section
section

open Filter Finset
open scoped Topology BigOperators
namespace PeskunAbelMean

theorem summable_weight (a : ℕ → ℝ) (C : ℝ) (ha : ∀ k, |a k| ≤ C)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) : Summable (fun k => a k*q^k) := by
  apply ((summable_geometric_of_lt_one hq0 hq1).mul_left C).of_norm_bounded
  intro k
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hq0 k)]
  exact mul_le_mul_of_nonneg_right (ha k) (pow_nonneg hq0 k)

theorem identity (a : ℕ → ℝ) (C : ℝ) (ha : ∀ k, |a k| ≤ C)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (1-q)*(∑' k, a k*q^k)=a 0+q*(∑' k, (a (k+1)-a k)*q^k) := by
  have h1 := summable_weight a C ha q hq0 hq1
  have h2 := summable_weight (fun k => a (k+1)) C (fun k => ha (k+1)) q hq0 hq1
  have hd : (∑' k, (a (k+1)-a k)*q^k)=(∑' k, a (k+1)*q^k)-(∑' k, a k*q^k) := by
    simp_rw [sub_mul]
    exact h2.tsum_sub h1
  have ht := h1.tsum_eq_zero_add
  simp only [pow_zero,mul_one] at ht
  have hs : (∑' k, a (k+1)*q^(k+1))=q*(∑' k, a (k+1)*q^k) := by
    rw [← tsum_mul_left]
    congr 1
    funext k
    rw [pow_succ]
    ring
  rw [hs] at ht
  rw [hd]
  nlinarith

theorem tendsto_mean (a : ℕ → ℝ) (C L : ℝ) (ha : ∀ k, |a k| ≤ C)
    (hlim : Tendsto a atTop (𝓝 L)) :
    Tendsto (fun q : ℝ => (1-q)*(∑' k, a k*q^k)) (𝓝[<] 1) (𝓝 L) := by
  have hd : Tendsto (fun n => ∑ k ∈ range n, (a (k+1)-a k)) atTop (𝓝 (L-a 0)) := by
    simp only [sum_range_sub]
    exact hlim.sub_const (a 0)
  have hab := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hd
  have ht : Tendsto (fun q : ℝ => a 0+q*(∑' k, (a (k+1)-a k)*q^k)) (𝓝[<] 1) (𝓝 (a 0+1*(L-a 0))) :=
    tendsto_const_nhds.add ((tendsto_id.mono_left nhdsWithin_le_nhds).mul hab)
  have ht' : Tendsto (fun q : ℝ => a 0+q*(∑' k, (a (k+1)-a k)*q^k)) (𝓝[<] 1) (𝓝 L) := by
    convert! ht using 1 <;> ring
  apply ht'.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with q hq
  exact (identity a C ha q hq.1.le hq.2).symm

theorem tendsto_even_mean (a : ℕ → ℝ) (C L : ℝ) (ha : ∀ k, |a k| ≤ C)
    (hlim : Tendsto a atTop (𝓝 L)) :
    Tendsto (fun q : ℝ => 2*(1-q)*(∑' k, q^(2*k)*a k)) (𝓝[<] 1) (𝓝 L) := by
  have hsquare : Tendsto (fun q : ℝ => q^2) (𝓝[<] 1) (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using ((tendsto_id.mono_left nhdsWithin_le_nhds).pow 2 : Tendsto (fun q : ℝ => q^2) (𝓝[<] 1) (𝓝 (1^2)))
    · filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with q hq
      change q^2 < 1
      nlinarith [hq.1,hq.2]
  have hm := (tendsto_mean a C L ha hlim).comp hsquare
  have hfactor : Tendsto (fun q : ℝ => 2/(1+q)) (𝓝[<] 1) (𝓝 1) := by
    convert! tendsto_const_nhds.div (tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds)) (by norm_num : (1:ℝ)+1 ≠ 0) using 1 <;> norm_num
  have ht := hfactor.mul hm
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with q hq
  have he : (∑' k, a k*(q^2)^k)=∑' k, q^(2*k)*a k := by
    apply tsum_congr
    intro k
    rw [← pow_mul]
    ring
  dsimp only [Function.comp_def]
  rw [he]
  have hn : (1+q) ≠ 0 := by linarith [hq.1]
  field_simp
  ring
end PeskunAbelMean

set_option maxHeartbeats 1000000
namespace PeskunAbelMean

theorem paired_identity (r : ℕ → ℝ) (C : ℝ) (hr : ∀ k, |r k| ≤ C)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    r 0+2*(∑' k, q^(k+1)*r (k+1)) =
      2*(∑' k, q^(2*k+1)*(r (2*k)+r (2*k+1)))+
        2*(1-q)*(∑' k, q^(2*k)*r (2*k))-r 0 := by
  have hall : Summable (fun k => q^k*r k) := by
    simpa only [mul_comm] using summable_weight r C hr q hq0 hq1
  have heven : Summable (fun k => q^(2*k)*r (2*k)) := hall.comp_injective (fun i j h => by omega)
  have hodd : Summable (fun k => q^(2*k+1)*r (2*k+1)) := hall.comp_injective (fun i j h => by omega)
  have he : (∑' k, q^(2*k)*r (2*k))+(∑' k, q^(2*k+1)*r (2*k+1))=∑' k, q^k*r k :=
    tsum_even_add_odd (f := fun k => q^k*r k) heven hodd
  have hp : (∑' k, q^(2*k+1)*(r (2*k)+r (2*k+1))) =
      q*(∑' k, q^(2*k)*r (2*k))+(∑' k, q^(2*k+1)*r (2*k+1)) := by
    calc
      _ = ∑' k, (q*(q^(2*k)*r (2*k))+q^(2*k+1)*r (2*k+1)) := by
        apply tsum_congr
        intro k
        rw [pow_succ]
        ring
      _ = _ := by rw [Summable.tsum_add (heven.mul_left q) hodd,tsum_mul_left]
  have hz := hall.tsum_eq_zero_add
  simp only [pow_zero,one_mul] at hz
  rw [hp]
  nlinarith only [he,hz]
end PeskunAbelMean
end

section

open Filter
open scoped Topology

namespace CPeskun

theorem odd_series_summable (s : ℕ → ℝ) (hs : ∀ k, 0 ≤ s k)
    (C : ℝ) (hC : ∀ k, s k ≤ C) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun k => r ^ (2 * k + 1) * s k) := by
  have hgeom : Summable (fun k : ℕ => r ^ (2 * k + 1)) := (summable_geometric_of_lt_one hr0 hr1).comp_injective
    (show Function.Injective (fun k : ℕ => 2 * k + 1) by intro i j hij; dsimp at hij; omega)
  exact (hgeom.mul_right C).of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg hr0 _) (hs k))
    (fun k => mul_le_mul_of_nonneg_left (hC k) (pow_nonneg hr0 _))

theorem ennreal_odd_series_tendsto (s : ℕ → ℝ) (hs : ∀ k, 0 ≤ s k) :
    Tendsto (fun r : ℝ => ∑' k, ENNReal.ofReal (r ^ (2 * k + 1) * s k))
      (𝓝[<] (1 : ℝ)) (𝓝 (∑' k, ENNReal.ofReal (s k))) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    rw [ENNReal.tsum_eq_iSup_sum] at ha
    obtain ⟨I, hI⟩ := lt_iSup_iff.mp ha
    have hcont : Continuous (fun r : ℝ => ∑ k ∈ I,
        ENNReal.ofReal (r ^ (2 * k + 1) * s k)) := by
      apply continuous_finset_sum
      intro k hk
      exact ENNReal.continuous_ofReal.comp ((continuous_id.pow _).mul continuous_const)
    have hevent : ∀ᶠ r in 𝓝 (1 : ℝ),
        a < ∑ k ∈ I, ENNReal.ofReal (r ^ (2 * k + 1) * s k) :=
      (hcont.tendsto 1).eventually (eventually_gt_nhds (by simpa using hI))
    filter_upwards [hevent.filter_mono nhdsWithin_le_nhds] with r hr
    exact hr.trans_le (ENNReal.sum_le_tsum I)
  · intro a ha
    have hlo : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 ≤ r :=
      ((eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).mono fun _ h => h.le).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hlo, self_mem_nhdsWithin] with r hr0 hr1
    apply lt_of_le_of_lt _ ha
    apply ENNReal.tsum_le_tsum
    intro k
    apply ENNReal.ofReal_le_ofReal
    calc
      r ^ (2 * k + 1) * s k ≤ 1 * s k :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hr0 (show r ≤ 1 from le_of_lt hr1)) (hs k)
      _ = s k := one_mul _

theorem ofReal_odd_series_tendsto (s : ℕ → ℝ) (hs : ∀ k, 0 ≤ s k)
    (C : ℝ) (hC : ∀ k, s k ≤ C) :
    Tendsto (fun r : ℝ => ENNReal.ofReal (∑' k, r ^ (2 * k + 1) * s k))
      (𝓝[<] (1 : ℝ)) (𝓝 (∑' k, ENNReal.ofReal (s k))) := by
  apply (ennreal_odd_series_tendsto s hs).congr'
  have hlo : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 ≤ r :=
    ((eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).mono fun _ h => h.le).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hlo, self_mem_nhdsWithin] with r hr0 hr1
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun k => mul_nonneg (pow_nonneg hr0 _) (hs k))
    (odd_series_summable s hs C hC hr0 hr1)).symm

end CPeskun

end

section
namespace PeskunAbelMean
open Filter
open scoped Topology BigOperators ENNReal

theorem regularized_extended_limit (r : ℕ → ℝ) (C L : ℝ) (hr : ∀ k, |r k| ≤ C)
    (ha : ∀ k, 0 ≤ r (2*k)) (hs : ∀ k, 0 ≤ r (2*k)+r (2*k+1))
    (hlim : Tendsto (fun k => r (2*k)) atTop (𝓝 L)) :
    Tendsto (fun q : ℝ => ENNReal.ofReal (r 0+2*(∑' k, q^(k+1)*r (k+1)))) (𝓝[<] 1)
      (𝓝 ((2:ℝ≥0∞)*(∑' k, ENNReal.ofReal (r (2*k)+r (2*k+1)))+
        ENNReal.ofReal L-ENNReal.ofReal (r 0))) := by
  have hsb (k : ℕ) : r (2*k)+r (2*k+1) ≤ 2*C := by
    have h1 := (abs_le.mp (hr (2*k))).2
    have h2 := (abs_le.mp (hr (2*k+1))).2
    linarith
  have ht := CPeskun.ofReal_odd_series_tendsto (fun k => r (2*k)+r (2*k+1)) hs (2*C) hsb
  have hm := ENNReal.tendsto_ofReal (tendsto_even_mean (fun k => r (2*k)) C L (fun k => hr (2*k)) hlim)
  have htwo : Tendsto (fun q : ℝ => (2:ℝ≥0∞)*ENNReal.ofReal (∑' k, q^(2*k+1)*(r (2*k)+r (2*k+1))))
      (𝓝[<] 1) (𝓝 ((2:ℝ≥0∞)*(∑' k, ENNReal.ofReal (r (2*k)+r (2*k+1))))) :=
    ENNReal.Tendsto.mul tendsto_const_nhds (Or.inl (by norm_num)) ht (Or.inr (by norm_num))
  have hh := ENNReal.Tendsto.sub (b := ENNReal.ofReal (r 0)) (htwo.add hm) tendsto_const_nhds (Or.inr ENNReal.ofReal_ne_top)
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with q hq
  have ht0 : 0 ≤ ∑' k, q^(2*k+1)*(r (2*k)+r (2*k+1)) :=
    tsum_nonneg fun k => mul_nonneg (pow_nonneg hq.1.le _) (hs k)
  have he0 : 0 ≤ 2*(1-q)*(∑' k, q^(2*k)*r (2*k)) :=
    mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hq.2.le)) (tsum_nonneg fun k => mul_nonneg (pow_nonneg hq.1.le _) (ha k))
  have hr0 : 0 ≤ r 0 := by simpa using ha 0
  rw [paired_identity r C hr q hq.1.le hq.2,ENNReal.ofReal_sub _ hr0,
    ENNReal.ofReal_add (by positivity) he0,ENNReal.ofReal_mul (p := 2) (q := ∑' k, q^(2*k+1)*(r (2*k)+r (2*k+1))) (by norm_num)]
  norm_num
end PeskunAbelMean
end
end

section
namespace PeskunResult
open TierneyMH.Peskun MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
variable {E : Type*} [MeasurableSpace E]

theorem lag_properties (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hr : Kernel.IsReversible H π)
    (f : E → ℝ) (hf : MemLp f 2 π) :
    ∃ C L : ℝ, (∀ k, |lagInner π H f k| ≤ C) ∧
      (∀ k, 0 ≤ lagInner π H f (2*k)) ∧
      (∀ k, 0 ≤ lagInner π H f (2*k)+lagInner π H f (2*k+1)) ∧
      Tendsto (fun k => lagInner π H f (2*k)) atTop (𝓝 L) := by
  let A := PeskunL2.op π H hr.invariant
  let u := hf.toLp f
  have hs : ∀ x y, ⟪A x,y⟫=⟪x,A y⟫ := PeskunL2.op_symm π H hr.invariant hr
  have hn : ‖A‖ ≤ 1 := PeskunL2.op_norm π H hr.invariant
  have he (k : ℕ) : ⟪u,(A^k) u⟫=lagInner π H f k := PeskunL2.lag_inner π H hr.invariant f hf k
  obtain ⟨L,hL0,hL⟩ := PeskunCorrelation.even_limit A hs hn u
  refine ⟨‖u‖^2,L,?_,?_,?_,?_⟩
  · intro k
    rw [← he]
    exact PeskunCorrelation.bounded A hn u k
  · intro k
    rw [← he,PeskunCorrelation.even A hs]
    positivity
  · intro k
    rw [← he,← he]
    exact PeskunCorrelation.pair_nonneg A hs hn u k
  · simpa only [he] using hL

theorem common_limit (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hr : Kernel.IsReversible H π)
    (f : E → ℝ) (hm : Measurable f) (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π=0) :
    ∃ v : ℝ≥0∞,
      Tendsto (fun n : ℕ => evariance (pathSum f n) (chainMeasure π H)/(n:ℝ≥0∞)) atTop (𝓝 v) ∧
      Tendsto (fun q : ℝ => ENNReal.ofReal (vLam π H f q)) (𝓝[<] 1) (𝓝 v) := by
  obtain ⟨C,L,hbound,ha,hs,hL⟩ := lag_properties π H hr f hf
  have hv := TierneyVarianceLimit.variance_extended_limit (lagInner π H f) L ha hL hs
  have hq := PeskunAbelMean.regularized_extended_limit (lagInner π H f) C L hbound ha hs hL
  refine ⟨(2:ℝ≥0∞)*(∑' k, ENNReal.ofReal (lagInner π H f (2*k)+lagInner π H f (2*k+1)))+
    ENNReal.ofReal L-ENNReal.ofReal (lagInner π H f 0),?_,?_⟩
  · apply hv.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (ratio_eq_V π H hr f hm hf hf0 n hn).symm
  · simpa only [PeskunChain.lag_zero π H f hm,vLam] using hq
end PeskunResult
end
end

section
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
end

section
open MeasureTheory ProbabilityTheory
namespace PeskunResult
open TierneyMH.Peskun
open scoped RealInnerProductSpace

theorem vLam_monotone {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
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

end PeskunResult
end

section

open MeasureTheory ProbabilityTheory Filter TierneyMH.Peskun TierneyMH.Shared
open scoped ENNReal RealInnerProductSpace Topology
theorem solution {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    (π : Measure E) [IsProbabilityMeasure π]
    (P₁ P₂ : Kernel E E) [IsMarkovKernel P₁] [IsMarkovKernel P₂]
    (hrev₁ : Kernel.IsReversible P₁ π) (hrev₂ : Kernel.IsReversible P₂ π)
    (f : E → ℝ) (hf_meas : Measurable f) (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π = 0)
    (hdom : OffDiagDominates π P₁ P₂) :
    ∃ v₁ v₂ : ℝ≥0∞,
      Tendsto (fun n : ℕ => evariance (pathSum f n) (chainMeasure π P₁) / n) atTop (𝓝 v₁) ∧
      Tendsto (fun n : ℕ => evariance (pathSum f n) (chainMeasure π P₂) / n) atTop (𝓝 v₂) ∧
      v₁ ≤ v₂ := by
  obtain ⟨v₁,hv₁,hq₁⟩ := PeskunResult.common_limit π P₁ hrev₁ f hf_meas hf hf0
  obtain ⟨v₂,hv₂,hq₂⟩ := PeskunResult.common_limit π P₂ hrev₂ f hf_meas hf hf0
  refine ⟨v₁,v₂,hv₁,hv₂,?_⟩
  apply le_of_tendsto_of_tendsto hq₁ hq₂
  filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with q hq
  exact ENNReal.ofReal_le_ofReal (PeskunResult.vLam_monotone π P₁ P₂ hrev₁ hrev₂ hdom f hf_meas hf hf0 q hq.1.le hq.2)
end
