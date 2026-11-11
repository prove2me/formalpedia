-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.modified_outer_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:40.296119+00:00
-- url     : https://prove2.me/submissions/40201ba8-c7d2-463c-9fe0-8bf985712dfb

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_BiholderTransport
import Definitions.Def_OAIQ232A026
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_local_branch_jet_bound_second
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_normal_relative_hessian_bound

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_FullSet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma bilinear_isBigO_norm_mul {α : Type*} (L : Filter α)
    (B : E →L[ℝ] F →L[ℝ] G) (u : α → E) (v : α → F) :
    (fun x => B (u x) (v x)) =O[L] (fun x => ‖u x‖*‖v x‖) := by
  apply Asymptotics.IsBigO.of_bound ‖B‖
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
      mul_assoc] using B.le_opNorm₂ (u x) (v x))

lemma bilinear_remainder_of_hasFDerivAt {a : E → F} {A : E →L[ℝ] F}
    (ha : HasFDerivAt a A 0) (ha0 : a 0=0) (B : F →L[ℝ] F →L[ℝ] ℝ) :
    (fun h => B (a h) (a h)-B (A h) (A h)) =o[𝓝 0] (fun h : E => ‖h‖^2) := by
  have hR : (fun h => a h-A h) =o[𝓝 0] (fun h : E => h) := by
    simpa only [zero_add,ha0,sub_zero] using hasFDerivAt_iff_isLittleO_nhds_zero.mp ha
  have hO : a =O[𝓝 0] (fun h : E => h) := by
    simpa only [ha0,sub_zero] using ha.isBigO_sub
  have hA : (fun h : E => A h) =O[𝓝 0] (fun h => h) := A.isBigO_id _
  have h1 := (bilinear_isBigO_norm_mul (𝓝 (0:E)) B (fun h => a h-A h) a).trans_isLittleO
    (hR.norm_left.norm_right.mul_isBigO hO.norm_left.norm_right)
  have h2 := (bilinear_isBigO_norm_mul (𝓝 (0:E)) B (fun h => A h) (fun h => a h-A h)).trans_isLittleO
    (hA.norm_left.norm_right.mul_isLittleO hR.norm_left.norm_right)
  have he : (fun h => B (a h) (a h)-B (A h) (A h)) =
      (fun h => B (a h-A h) (a h)+B (A h) (a h-A h)) := by
    funext h
    simp only [map_sub,_root_.sub_apply]
    ring
  rw [he]
  simpa only [pow_two] using h1.add h2

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_LowerTaylor
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma HasLowerSecondTaylor.mono {f g : E → ℝ} {l : E →L[ℝ] ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasLowerSecondTaylor f l B)
    (he : f 0=g 0) (hle : f≤ᶠ[𝓝 0] g) : HasLowerSecondTaylor g l B := by
  intro ε hε
  filter_upwards [hf ε hε,hle] with h hh hfg
  rw [←he]
  exact hh.trans hfg

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_LowerTaylorComposition
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma HasLowerSecondTaylor.comp_stationary {f : F → ℝ}
    {B : F →L[ℝ] F →L[ℝ] ℝ} (hf : HasLowerSecondTaylor f 0 B)
    {a : E → F} {A : E →L[ℝ] F} (ha : HasFDerivAt a A 0) (ha0 : a 0=0) :
    HasLowerSecondTaylor (fun h => f (a h)) 0 (pullBilinear B A) := by
  have hO : a =O[𝓝 0] (fun h : E => h) := by
    simpa only [ha0,sub_zero] using ha.isBigO_sub
  obtain ⟨C,hC,HC⟩ := hO.exists_pos
  have ht : Tendsto a (𝓝 0) (𝓝 0) := ha0 ▸ ha.continuousAt
  intro ε hε
  have hδ : 0 < ε/(2*C^2) := div_pos hε (by positivity)
  have hB := (bilinear_remainder_of_hasFDerivAt ha ha0 B).def hε
  filter_upwards [ht.eventually (hf _ hδ),HC.bound,hB] with h hh haB hb
  simp only [zero_apply,add_zero] at hh ⊢
  rw [ha0,pullBilinear_apply]
  have hb' : |B (a h) (a h)-B (A h) (A h)| ≤ ε*‖h‖^2 := by
    simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using hb
  have hsq : ‖a h‖^2 ≤ C^2*‖h‖^2 := by
    nlinarith only [sq_nonneg (C*‖h‖-‖a h‖),haB,norm_nonneg (a h),
      mul_nonneg hC.le (norm_nonneg h)]
  have hsq' := mul_le_mul_of_nonneg_left hsq (le_of_lt hδ)
  have he : ε/(2*C^2)*(C^2*‖h‖^2)=(ε/2)*‖h‖^2 := by
    field_simp [hC.ne']
  rw [he] at hsq'
  linarith only [hh,(abs_le.mp hb').1,hsq']

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_SecondFderivScalarComp
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma second_fderiv_scalar_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {φ : ℝ → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hφ : ContDiffAt ℝ 2 φ (f x)) (ξ : E) :
    fderiv ℝ (fderiv ℝ (fun h => φ (f h))) x ξ ξ =
      iteratedDeriv 2 φ (f x)*(fderiv ℝ f x ξ)^2+
        deriv φ (f x)*fderiv ℝ (fderiv ℝ f) x ξ ξ := by
  let g := fun t : ℝ => f (x+t • ξ)
  have hg : ContDiffAt ℝ 2 g 0 := by
    change ContDiffAt ℝ 2 (f ∘ fun t : ℝ => x+t • ξ) 0
    exact (show ContDiffAt ℝ 2 f (x+(0:ℝ) • ξ) from by simpa using hf).comp (0:ℝ)
      (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have hg0 : g 0=f x := by simp [g]
  have hline : HasDerivAt (fun t : ℝ => x+t • ξ) ξ 0 := by
    convert! (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const ξ) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hd : deriv g 0=fderiv ℝ f x ξ := by
    simpa only [Function.comp_def,g,zero_smul,add_zero] using
      ((show HasFDerivAt f (fderiv ℝ f x) (x+(0:ℝ) • ξ) from by
        simpa only [zero_smul,add_zero] using (hf.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt (0:ℝ) hline).deriv
  have H := iteratedDeriv_comp_two (show ContDiffAt ℝ 2 φ (g 0) from hg0.symm ▸ hφ) hg
  rw [hg0,hd,show iteratedDeriv 2 g 0=fderiv ℝ (fderiv ℝ f) x ξ ξ from
    iteratedDeriv_two_affine_line hf ξ] at H
  change fderiv ℝ (fderiv ℝ (φ ∘ f)) x ξ ξ = _
  rw [←iteratedDeriv_two_affine_line (hφ.comp x hf) ξ]
  exact H

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_JetDiffeomorphism
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma lower_jet_diffeomorphism_bound
    {f:E → F} {g:F → E} {p:E} {A:E →L[ℝ] F} {J:F →L[ℝ] E}
    (hf:HasFDerivAt f A p) (hg:HasFDerivAt g J (f p))
    (hgf:(fun x=>g (f x)) =ᶠ[𝓝 p] id)
    (hfg:(fun y=>f (g y)) =ᶠ[𝓝 (f p)] id)
    {v:F → ℝ} {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hjet:HasLowerSecondTaylor (fun d=>v (f (p+d))) 0 B)
    (hB:∀ d,0 ≤ B d d)
    {C:ℝ} (hC:0 ≤ C)
    (hbound:∀ H:F →L[ℝ] F →L[ℝ] ℝ,
      (∀ w,0 ≤ H w w) → HasLowerSecondTaylor (fun w=>v (f p+w)) 0 H → ∀ w,H w w ≤ C*‖w‖^2) :
    ∀ d,B d d ≤ C*‖A‖^2*‖d‖^2 := by
  have hg0:g (f p)=p := hgf.eq_of_nhds
  have ha:HasFDerivAt (fun w=>g (f p+w)-p) J 0 := by
    have hg' : HasFDerivAt g J (f p+id (0:F)) := by simpa only [id_eq,add_zero] using hg
    have H:=hg'.comp 0 ((hasFDerivAt_id (0:F)).const_add (f p))
    simpa only [add_zero,ContinuousLinearMap.comp_id,Function.comp_apply,id_eq] using H.sub_const p
  have ha0:g (f p+0)-p=0 := by rw [add_zero,hg0,sub_self]
  have H:=hjet.comp_stationary ha ha0
  have heq:(fun w=>v (f (p+(g (f p+w)-p)))) =ᶠ[𝓝 (0:F)]
      (fun w=>v (f p+w)) := by
    have ht:Tendsto (fun w:F=>f p+w) (𝓝 0) (𝓝 (f p)) := by
      simpa only [add_zero] using
        (tendsto_const_nhds.add (tendsto_id : Tendsto (fun w:F=>w) (𝓝 0) (𝓝 0)) :
          Tendsto (fun w:F=>f p+w) (𝓝 0) (𝓝 (f p+0)))
    filter_upwards [ht.eventually hfg] with w hw
    have hp:p+(g (f p+w)-p)=g (f p+w) := by abel
    rw [hp,hw,id_eq]
  have HE:=H.mono heq.eq_of_nhds heq.le
  have hJA:J.comp A=ContinuousLinearMap.id ℝ E := by
    have HD:= (hg.comp p hf).congr_of_eventuallyEq hgf.symm
    exact HD.unique (hasFDerivAt_id p)
  intro d
  have HH:=hbound (pullBilinear B J) (fun w=>by simpa only [pullBilinear_apply] using hB (J w)) HE (A d)
  have hid:J (A d)=d := by simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using congrArg (fun T:E →L[ℝ] E=>T d) hJA
  rw [pullBilinear_apply,hid] at HH
  have hn:=A.le_opNorm d
  have hsq:‖A d‖^2 ≤ ‖A‖^2*‖d‖^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  exact HH.trans (by nlinarith only [mul_le_mul_of_nonneg_left hsq hC])

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_FiberJet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma fiber_local_inverse
    (e:OpenPartialHomeomorph (E×F) (E×F)) (he:∀q,(e q).1=q.1)
    {b:E} {p:F} (hq:(b,p)∈e.source) :
    let f:=fun v:F=>(e (b,v)).2
    let g:=fun w:F=>(e.symm (b,w)).2
    (fun v=>g (f v)) =ᶠ[𝓝 p] id ∧ (fun w=>f (g w)) =ᶠ[𝓝 (f p)] id := by
  dsimp only
  have hf0:e (b,p)=(b,(e (b,p)).2) := Prod.ext (he _) rfl
  constructor
  · have H:∀ᶠ v in 𝓝 p,(b,v)∈e.source :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hq)
    filter_upwards [H] with v hv
    have Hinv:=e.left_inv hv
    have Hpair:e (b,v)=(b,(e (b,v)).2) := Prod.ext (he _) rfl
    calc
      _ = (e.symm (e (b,v))).2 := congrArg (fun q=>(e.symm q).2) Hpair.symm
      _ = v := congrArg Prod.snd Hinv
  · have ht:(b,(e (b,p)).2)∈e.target := hf0 ▸ e.map_source hq
    have H:∀ᶠ w in 𝓝 ((e (b,p)).2),(b,w)∈e.target :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (e.open_target.mem_nhds ht)
    filter_upwards [H] with w hw
    have Hinv:=e.right_inv hw
    have Hfirst:(e.symm (b,w)).1=b := by
      rw [←he (e.symm (b,w)),Hinv]
    have Hpair:e.symm (b,w)=(b,(e.symm (b,w)).2) := Prod.ext Hfirst rfl
    calc
      _ = (e (e.symm (b,w))).2 := congrArg (fun q=>(e q).2) Hpair.symm
      _ = w := congrArg Prod.snd Hinv

lemma fiber_jet_bound
    (e:OpenPartialHomeomorph (E×F) (E×F)) (he:∀q,(e q).1=q.1)
    {b:E} {p:F} (hq:(b,p)∈e.source)
    (hf:DifferentiableAt ℝ e (b,p)) (hg:DifferentiableAt ℝ e.symm (e (b,p)))
    {v:F → ℝ} {B:F →L[ℝ] F →L[ℝ] ℝ}
    (hjet:HasLowerSecondTaylor (fun d=>v ((e (b,p+d)).2)) 0 B)
    (hB:∀d,0 ≤ B d d) {C:ℝ} (hC:0 ≤ C)
    (hbound:∀ H:F →L[ℝ] F →L[ℝ] ℝ,(∀d,0 ≤ H d d) →
      HasLowerSecondTaylor (fun w=>v ((e (b,p)).2+w)) 0 H → ∀d,H d d ≤ C*‖d‖^2) :
    ∀d,B d d ≤ C*‖fderiv ℝ e (b,p)‖^2*‖d‖^2 := by
  let f:=fun v:F=>(e (b,v)).2
  let g:=fun w:F=>(e.symm (b,w)).2
  let T:=fderiv ℝ e (b,p)
  let A:F →L[ℝ] F := (ContinuousLinearMap.snd ℝ E F).comp
    (T.comp (ContinuousLinearMap.inr ℝ E F))
  have hsection:HasFDerivAt (fun v:F=>(b,v)) (ContinuousLinearMap.inr ℝ E F) p := by
    have hi:ContinuousLinearMap.inr ℝ E F=(0: F →L[ℝ] E).prod (ContinuousLinearMap.id ℝ F) := by
      ext d <;> rfl
    rw [hi]
    exact (hasFDerivAt_const b p).prodMk (hasFDerivAt_id p)
  have hAf:HasFDerivAt f A p := (hf.hasFDerivAt.comp p hsection).snd
  have hG:DifferentiableAt ℝ g (f p) := by
    have heq:(b,f p)=e (b,p) := by
      apply Prod.ext
      · exact (he (b,p)).symm
      · rfl
    have hg':DifferentiableAt ℝ e.symm (b,f p) := heq.symm ▸ hg
    exact (hg'.comp _ ((differentiableAt_const b).prodMk differentiableAt_id)).snd
  obtain ⟨hgf,hfg⟩:=fiber_local_inverse e he hq
  have H:=lower_jet_diffeomorphism_bound hAf hG.hasFDerivAt hgf hfg hjet hB hC hbound
  have hnorm:‖A‖ ≤ ‖T‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro d
    change ‖(T (0,d)).2‖ ≤ ‖T‖*‖d‖
    calc
      _ ≤ ‖T (0,d)‖ := norm_snd_le _
      _ ≤ ‖T‖*‖(0,d)‖ := T.le_opNorm _
      _ = ‖T‖*‖d‖ := by simp
  intro d
  exact (H d).trans (by gcongr)

lemma exists_uniform_fiber_jet_transfer
    (e:OpenPartialHomeomorph (E×F) (E×F)) (he:∀q,(e q).1=q.1)
    (hf:ContDiffOn ℝ ∞ e e.source) (hg:ContDiffOn ℝ ∞ e.symm e.target)
    {q:E×F} (hq:q∈e.source) :
    ∃ U:Set (E×F),U∈𝓝 q ∧ U⊆e.source ∧ ∃ K≥0,
      ∀z∈U,∀v:F → ℝ,∀B:F →L[ℝ] F →L[ℝ] ℝ,
      HasLowerSecondTaylor (fun d=>v ((e (z.1,z.2+d)).2)) 0 B →
      (∀d,0 ≤ B d d) → ∀C:ℝ,0 ≤ C →
      (∀ H:F →L[ℝ] F →L[ℝ] ℝ,(∀d,0 ≤ H d d) →
        HasLowerSecondTaylor (fun w=>v ((e z).2+w)) 0 H → ∀d,H d d ≤ C*‖d‖^2) →
      ∀d,B d d ≤ C*K*‖d‖^2 := by
  let R:=‖fderiv ℝ e q‖+1
  let U:=e.source ∩ {z|‖fderiv ℝ e z‖<R}
  have hR:0 < R := by dsimp [R] <;> positivity
  have hU:U∈𝓝 q := inter_mem (e.open_source.mem_nhds hq)
    (((hf.contDiffAt (e.open_source.mem_nhds hq)).continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).norm.preimage_mem_nhds
      (gt_mem_nhds (show ‖fderiv ℝ e q‖<R by dsimp [R] <;> linarith)))
  refine ⟨U,hU,inter_subset_left,R^2,sq_nonneg _,?_⟩
  intro z hz v B hjet hB C hC HB d
  have HF: DifferentiableAt ℝ e z :=
    (hf.contDiffAt (e.open_source.mem_nhds hz.1)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have HG: DifferentiableAt ℝ e.symm (e z) :=
    (hg.contDiffAt (e.open_target.mem_nhds (e.map_source hz.1))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have H:=fiber_jet_bound e he hz.1 HF HG hjet hB hC HB d
  exact H.trans (by gcongr; exact hz.2.le)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ScalarFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport

lemma continuous_scalar_family_deriv {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    Continuous (fun p:ℝ×ℝ=>deriv (fun s=>Φ (p.1,s)) p.2) := by
  have heq (p:ℝ×ℝ) := (scalar_family_hasDeriv hΦ p).deriv
  simp_rw [heq]
  exact (contDiff_infty_iff_fderiv.mp hΦ).2.continuous.clm_apply continuous_const

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ScalarInverseJet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma exists_scalar_inverse_jet {φ : ℝ → ℝ} {v l : ℝ}
    (hφ : ContDiffAt ℝ 2 φ v) (hd : HasDerivAt φ l v) (hl : l≠0) :
    ∃ i : ℝ → ℝ, ContDiffAt ℝ 2 i (φ v) ∧ i (φ v)=v ∧
      HasDerivAt i l⁻¹ (φ v) ∧
      (∀ᶠ w in 𝓝 (φ v),φ (i w)=w) ∧
      iteratedDeriv 2 i (φ v)= -iteratedDeriv 2 φ v/l^3 := by
  let i := hφ.localInverse (hd.hasFDerivAt_equiv hl) (by norm_num)
  have hi : ContDiffAt ℝ 2 i (φ v) := hφ.to_localInverse (hd.hasFDerivAt_equiv hl) (by norm_num)
  have hiv : i (φ v)=v := hφ.localInverse_apply_image (hd.hasFDerivAt_equiv hl) (by norm_num)
  have hr : ∀ᶠ w in 𝓝 (φ v),φ (i w)=w :=
    (hφ.hasStrictFDerivAt' (hd.hasFDerivAt_equiv hl) (by norm_num)).eventually_right_inverse
  have hiD : HasDerivAt i l⁻¹ (φ v) := (show HasDerivAt φ l (i (φ v)) from hiv.symm ▸ hd).of_local_left_inverse hi.continuousAt hl (by
    simpa only [hiv] using hr)
  refine ⟨i,hi,hiv,hiD,hr,?_⟩
  have hsecond := iteratedDeriv_comp_two (show ContDiffAt ℝ 2 φ (i (φ v)) from hiv.symm ▸ hφ) hi
  have hid : iteratedDeriv 2 (φ ∘ i) (φ v)=0 := by
    have H : (φ ∘ i)=ᶠ[𝓝 (φ v)] (fun w : ℝ => w) := hr
    have H2 := H.deriv.deriv_eq
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,deriv_id'',deriv_const] using H2
  rw [hid,hiv,hd.deriv,hiD.deriv] at hsecond
  apply (eq_div_iff (pow_ne_zero 3 hl)).mpr
  field_simp at hsecond
  nlinarith only [hsecond]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma scalar_inverse_lower_test {φ : ℝ → ℝ} (hmono : StrictMono φ)
    {v F : E → ℝ} {x : E} (hφ : ContDiffAt ℝ 2 φ (v x))
    {l : ℝ} (hd : HasDerivAt φ l (v x)) (hl : l≠0)
    (hF : ContDiffAt ℝ 2 F x) (hval : F x=φ (v x))
    (hlo : ∀ᶠ y in 𝓝 x,F y≤φ (v y)) :
    ∃ f : E → ℝ, ContDiffAt ℝ 2 f x ∧ f x=v x ∧
      (∀ᶠ y in 𝓝 x,f y≤v y) ∧
      fderiv ℝ f x=l⁻¹ • fderiv ℝ F x ∧
      ∀ ξ : E, fderiv ℝ (fderiv ℝ f) x ξ ξ=
        l⁻¹*fderiv ℝ (fderiv ℝ F) x ξ ξ-
          (iteratedDeriv 2 φ (v x)/l^3)*(fderiv ℝ F x ξ)^2 := by
  obtain ⟨i,hi,hiv,hiD,hir,hi2⟩ := exists_scalar_inverse_jet hφ hd hl
  let f := i ∘ F
  have hiF : ContDiffAt ℝ 2 i (F x) := hval.symm ▸ hi
  have hiDF : HasDerivAt i l⁻¹ (F x) := hval.symm ▸ hiD
  refine ⟨f,hiF.comp x hF,by dsimp [f]; rw [hval,hiv],?_,?_,?_⟩
  · have hr' := hF.continuousAt.eventually (show ∀ᶠ a in 𝓝 (F x),φ (i a)=a by rwa [hval])
    filter_upwards [hlo,hr'] with y hy hry
    apply hmono.le_iff_le.mp
    simpa only [f,Function.comp_apply,hry] using hy
  · exact (hiDF.comp_hasFDerivAt x (hF.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  · intro ξ
    rw [show f=(fun y => i (F y)) from rfl,second_fderiv_scalar_comp hF hiF ξ,
      hval,hi2,hiD.deriv]
    ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ScalarJetNeighborhood
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma scalar_jet_neighborhood {E:Type*} [TopologicalSpace E]
    {f:E → ℝ} {x:E} (hf:ContinuousAt f x)
    {A B:ℝ×ℝ → ℝ} (hA:Continuous A) (hB:Continuous B) {β:ℝ}
    {U:Set (E×ℝ)} (hU:U∈𝓝 (x,A (β,f x)))
    (hcurve:B (β,f x) < 0) :
    ∃V:Set (E×ℝ),V∈𝓝 (x,β) ∧ ∀q∈V,
      (q.1,A (q.2,f q.1))∈U ∧
      B (q.2,f q.1) < 0 := by
  let Q:=fun q:E×ℝ=>(q.2,f q.1)
  have hQ:ContinuousAt Q (x,β) := continuousAt_snd.prodMk (hf.comp continuousAt_fst)
  let J:=fun q:E×ℝ=>(q.1,A (q.2,f q.1))
  have hJ:ContinuousAt J (x,β) := continuousAt_fst.prodMk
    (hA.continuousAt.comp hQ)
  have hJU:J ⁻¹' U∈𝓝 (x,β) := hJ.preimage_mem_nhds hU
  have hK:ContinuousAt (fun q:E×ℝ=>B (q.2,f q.1)) (x,β) :=
    hB.continuousAt.comp hQ
  exact ⟨{q|J q∈U ∧ B (q.2,f q.1) < 0},
    inter_mem hJU (hK.eventually (gt_mem_nhds hcurve)),fun q hq=>hq⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ScalarSecond
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma contDiff_scalar_family_deriv {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (fun p:ℝ×ℝ=>deriv (fun s=>Φ (p.1,s)) p.2) := by
  have heq (p:ℝ×ℝ) := (scalar_family_hasDeriv hΦ p).deriv
  simp_rw [heq]
  exact (contDiff_infty_iff_fderiv.mp hΦ).2.clm_apply contDiff_const

lemma continuous_scalar_family_second {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    Continuous (fun p:ℝ×ℝ=>iteratedDeriv 2 (fun s=>Φ (p.1,s)) p.2) := by
  have H:=continuous_scalar_family_deriv (contDiff_scalar_family_deriv hΦ)
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using H

lemma scalar_family_contDiff {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (b:ℝ) :
    ContDiff ℝ ∞ (fun s=>Φ (b,s)) :=
  hΦ.comp (contDiff_const.prodMk contDiff_id)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_CenterSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma scalarCostSupport_self (φ : ℝ → ℝ) (v0 : ℝ) (x : M)
    (p : TangentSpace 𝓘(ℝ,Model n) x) (s : ℝ) :
    scalarCostSupport φ v0 x p s x=φ v0 := by simp [scalarCostSupport]

lemma scalarCostSupport_normal_jet {φ : ℝ → ℝ} {v0 l : ℝ} {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {s : ℝ} (hs : s≠0)
    (hp : s • p∈injectivityDomain x) (hφ : ContDiffAt ℝ 2 φ v0)
    (hl : deriv φ v0=l) :
    ContDiffAt ℝ 2 (fun h : TangentSpace 𝓘(ℝ,Model n) x =>
      scalarCostSupport φ v0 x p s (riemannianExp x h)) 0 ∧
    HasFDerivAt (fun h : TangentSpace 𝓘(ℝ,Model n) x =>
      scalarCostSupport φ v0 x p s (riemannianExp x h)) (innerSL ℝ (l • p)) 0 ∧
    ∀ ξ : TangentSpace 𝓘(ℝ,Model n) x,
      fderiv ℝ (fderiv ℝ (fun h => scalarCostSupport φ v0 x p s (riemannianExp x h))) 0 ξ ξ =
        -(l/s)*hessianValue x (s • p) ξ+iteratedDeriv 2 φ v0*(inner ℝ p ξ)^2 := by
  let C := normalCost x (s • p)
  let f := fun h : TangentSpace 𝓘(ℝ,Model n) x => v0+C 0/s+(-s⁻¹)*C h
  have hf0 : f 0=v0 := by dsimp [f] <;> ring
  have hC : ContDiffAt ℝ 2 C 0 :=
    (normalCost_contDiffAt hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hf : ContDiffAt ℝ 2 f 0 := contDiffAt_const.add (contDiffAt_const.mul hC)
  have hD : HasFDerivAt f (innerSL ℝ p) 0 := by
    apply (((normalCost_hasFDerivAt_zero hp).const_mul (-s⁻¹)).const_add (v0+C 0/s)).congr_fderiv
    ext h
    simp only [_root_.smul_apply,smul_eq_mul,innerSL_apply_apply,inner_neg_left,real_inner_smul_left]
    field_simp
  have he (h : TangentSpace 𝓘(ℝ,Model n) x) :
      scalarCostSupport φ v0 x p s (riemannianExp x h)=φ (f h) := by
    dsimp [scalarCostSupport,f,C,normalCost]
    rw [riemannianExp_zero]
    congr 1
    ring
  have heq : (fun h => scalarCostSupport φ v0 x p s (riemannianExp x h))=fun h => φ (f h) := funext he
  rw [heq]
  have hφf : ContDiffAt ℝ 2 φ (f 0) := hf0.symm ▸ hφ
  refine ⟨hφf.comp 0 hf,?_,?_⟩
  · have H := (hφf.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt 0 hD
    rw [hf0,hl] at H
    apply H.congr_fderiv
    ext h
    simp only [_root_.smul_apply,smul_eq_mul,innerSL_apply_apply,real_inner_smul_left]
  · intro ξ
    rw [second_fderiv_scalar_comp hf hφf ξ,hf0,hl,hD.fderiv]
    have H : fderiv ℝ (fderiv ℝ f) 0 ξ ξ=(-s⁻¹)*hessianValue x (s • p) ξ := by
      have hd : fderiv ℝ f=fun h => (-s⁻¹) • fderiv ℝ C h := by
        funext h
        dsimp only [f]
        rw [fderiv_const_add]
        exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := C) (-s⁻¹)) h
      rw [hd]
      change fderiv ℝ ((-s⁻¹) • fderiv ℝ C) 0 ξ ξ = _
      rw [fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ C) (-s⁻¹)]
      rw [hessianValue_eq_normalHessian hp]
      rfl
    rw [H]
    simp only [innerSL_apply_apply]
    ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_BranchCost2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_cost_branch_with_action (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2)) :
    ∃ G : M×M → ℝ,
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
        (z.1,riemannianExp z.1 z.2) ∧
      (∀ᶠ r in 𝓝 z,G (r.1,riemannianExp r.1 r.2)=‖r.2‖^2/2) ∧
      ∀ᶠ r in 𝓝 z, r.2 ∈ injectivityDomain r.1 →
        (fun q : M×M => cost q.1 q.2) =ᶠ[𝓝 (r.1,riemannianExp r.1 r.2)] G := by
  obtain ⟨P,hP,hPz,hleft,hright⟩ := exists_smooth_exp_branch z hz
  let G : M×M → ℝ := fun q => ‖(P q).2‖^2/2
  refine ⟨G,(contMDiff_tangent_energy (P (z.1,riemannianExp z.1 z.2))).comp _ hP,?_,?_⟩
  · filter_upwards [hleft] with r hr
    change ‖(P (r.1,riemannianExp r.1 r.2)).2‖^2/2=‖r.2‖^2/2
    rw [hr]
  let F : TangentBundle 𝓘(ℝ,Model n) M → M×M := fun r => (r.1,riemannianExp r.1 r.2)
  have hF : Continuous F :=
    ((Bundle.contMDiff_proj (fun v : M => TangentSpace 𝓘(ℝ,Model n) v)).prodMk contMDiff_riemannianExp).continuous
  have hPnear : ∀ᶠ q in 𝓝 (F z), ContinuousAt P q := by
    have hzero : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 0 P (F z) := hP.of_le bot_le
    exact ((contMDiffAt_iff_contMDiffAt_nhds (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mp hzero).mono
      (fun point hpoint => hpoint.continuousAt)
  have hRnear : ∀ᶠ q in 𝓝 (F z), ∀ᶠ q' in 𝓝 q,
      (P q').1=q'.1 ∧ riemannianExp (P q').1 (P q').2=q'.2 :=
    eventually_eventually_nhds.mpr hright
  filter_upwards [hleft,(hF.continuousAt.eventually (hPnear.and hRnear))] with r hr hnear
  intro hrID
  have hC : {v : TangentBundle 𝓘(ℝ,Model n) M | v.2 ∈ minimizingVectors v.1} ∈ 𝓝 (P (F r)) := by
    rw [show P (F r)=r from hr]
    exact mem_interior_iff_mem_nhds.mp (interior_total_minimizingVectors r hrID)
  have hmin := hnear.1.preimage_mem_nhds hC
  filter_upwards [hmin,hnear.2] with q hqmin hq
  change dist q.1 q.2^2/2=‖(P q).2‖^2/2
  change dist (P q).1 (riemannianExp (P q).1 (P q).2)=‖(P q).2‖ at hqmin
  have hd : dist q.1 q.2=‖(P q).2‖ :=
    (congrArg₂ dist hq.1.symm hq.2.symm).trans hqmin
  rw [hd]
end WeakMTWTransport

end



noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma contMDiff_reverseRay : ContMDiff
    (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ (reverseRay (n := n) (M := M)) := by
  exact contMDiff_tangentScale.comp
    (contMDiff_const.prodMk (contMDiff_sprayFlow.comp (contMDiff_const.prodMk contMDiff_id)))

lemma fiber_nonconjugate_of_smooth_left_inverse
    (z : TangentBundle 𝓘(ℝ,Model n) M)
    (P : M×M → TangentBundle 𝓘(ℝ,Model n) M)
    (hP : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ P (z.1,riemannianExp z.1 z.2))
    (hPz : P (z.1,riemannianExp z.1 z.2)=z)
    (hleft : ∀ᶠ r in 𝓝 z,P (r.1,riemannianExp r.1 r.2)=r) :
    Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2) := by
  let V := TangentSpace 𝓘(ℝ,Model n) z.1
  let y := riemannianExp z.1 z.2
  let d := extChartAt 𝓘(ℝ,Model n) y
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
  let τ := trivializationAt (Model n) (fun b : M => TangentSpace 𝓘(ℝ,Model n) b) z.1
  let L : V ≃L[ℝ] Model n :=
    τ.continuousLinearEquivAt ℝ z.1 (mem_baseSet_trivializationAt (Model n) _ z.1)
  let f : V → Model n := fun v => d (riemannianExp z.1 v)
  let g : Model n → Model n := fun w => (χ (P (z.1,d.symm w))).2
  have hdy : d.symm (d y)=y := d.left_inv (mem_extChartAt_source y)
  have hd : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d.symm (d y) :=
    (contMDiffOn_extChartAt_symm y).contMDiffAt
      ((isOpen_extChartAt_target y).mem_nhds (d.map_source (mem_extChartAt_source y)))
  have hp : ContMDiffAt 𝓘(ℝ,Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞
      (fun w => P (z.1,d.symm w)) (d y) := by
    have hm : ContMDiffAt 𝓘(ℝ,Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞
        (fun w => (z.1,d.symm w)) (d y) := contMDiffAt_const.prodMk hd
    have hP' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ P (z.1,d.symm (d y)) := by
      rw [hdy]; exact hP
    exact hP'.comp (d y) hm
  have hχ : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      𝓘(ℝ,Model n×Model n) ∞ χ (P (z.1,d.symm (d y))) := by
    rw [hdy,hPz]
    exact contMDiffAt_extChartAt
  have hg : ContDiffAt ℝ ∞ g (f z.2) :=
    contDiffAt_snd.comp (f z.2) (hχ.comp (d y) hp).contDiffAt
  have hf : ContDiffAt ℝ ∞ f z.2 :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d y from
      contMDiffAt_extChartAt).comp z.2 (contMDiff_riemannianExp_fiber z.1 z.2)).contDiffAt
  have hfiber : Continuous (fun v : V => (⟨z.1,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)) :=
    (contMDiff_fiber_embedding z.1).continuous
  have hfleft : ∀ᶠ v in 𝓝 z.2,P (z.1,riemannianExp z.1 v)=⟨z.1,v⟩ :=
    hfiber.continuousAt.eventually hleft
  have hsrc : ∀ᶠ v in 𝓝 z.2,riemannianExp z.1 v∈d.source :=
    (continuous_riemannianExp z.1).continuousAt.eventually (extChartAt_source_mem_nhds y)
  have heq : g ∘ f =ᶠ[𝓝 z.2] L := by
    filter_upwards [hfleft,hsrc] with v hv hvs
    change (χ (P (z.1,d.symm (d (riemannianExp z.1 v))))).2=L v
    rw [d.left_inv hvs,hv]
    rfl
  have hD : (fderiv ℝ g (f z.2)).comp (fderiv ℝ f z.2)=(L : V →L[ℝ] Model n) := by
    rw [←fderiv_comp _ (hg.differentiableAt (by simp)) (hf.differentiableAt (by simp)),
      heq.fderiv_eq,L.fderiv]
  intro u v huv
  apply L.injective
  have H := congrArg (fderiv ℝ g (f z.2)) huv
  change ((fderiv ℝ g (f z.2)).comp (fderiv ℝ f z.2)) u=
    ((fderiv ℝ g (f z.2)).comp (fderiv ℝ f z.2)) v at H
  rw [hD] at H
  exact H

lemma reverseRay_nonconjugate (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2)) :
    Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp (reverseRay z).1 (reverseRay z).2)
      (riemannianExp (reverseRay z).1 v)) (reverseRay z).2) := by
  obtain ⟨P,hP,hPz,hleft,_⟩ := exists_smooth_exp_branch z hz
  let Q : M×M → TangentBundle 𝓘(ℝ,Model n) M := fun q => reverseRay (P (q.2,q.1))
  have hQ : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ Q
      ((reverseRay z).1,riemannianExp (reverseRay z).1 (reverseRay z).2) := by
    rw [reverseRay_endpoint,reverseRay_base]
    have hs : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ (fun q : M×M => (q.2,q.1))
        (riemannianExp z.1 z.2,z.1) := contMDiffAt_snd.prodMk contMDiffAt_fst
    have hp : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ (fun q : M×M => P (q.2,q.1))
        (riemannianExp z.1 z.2,z.1) := hP.comp (riemannianExp z.1 z.2,z.1) hs
    exact contMDiff_reverseRay.contMDiffAt.comp (riemannianExp z.1 z.2,z.1) hp
  apply fiber_nonconjugate_of_smooth_left_inverse (reverseRay z) Q hQ
  · dsimp only [Q]
    rw [reverseRay_endpoint,reverseRay_base,hPz]
  · have H := continuous_reverseRay.continuousAt.eventually
      (show ∀ᶠ r in 𝓝 (reverseRay (reverseRay z)),P (r.1,riemannianExp r.1 r.2)=r from
        by rw [reverseRay_involutive]; exact hleft)
    filter_upwards [H] with r hr
    dsimp only [Q]
    rw [reverseRay_endpoint,reverseRay_base] at hr
    rw [hr,reverseRay_involutive]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_EndpointLowerJet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section EndpointLowerJet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma norm_reverseRay (z : TangentBundle 𝓘(ℝ,Model n) M) :
    ‖(reverseRay z).2‖=‖z.2‖ := by
  change ‖(-1:ℝ) • (sprayFlow 1 z).2‖=‖z.2‖
  rw [neg_one_smul,norm_neg,sprayFlow_speed]

lemma exists_reverse_branch_with_forward_action
    (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2)) :
    ∃ G : M×M → ℝ,
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
        ((reverseRay z).1,riemannianExp (reverseRay z).1 (reverseRay z).2) ∧
      (∀ᶠ r in 𝓝 z,G (riemannianExp r.1 r.2,r.1)=‖r.2‖^2/2) ∧
      ∀ᶠ r in 𝓝 (reverseRay z),r.2∈injectivityDomain r.1 →
        (fun q : M×M => cost q.1 q.2) =ᶠ[𝓝 (r.1,riemannianExp r.1 r.2)] G := by
  obtain ⟨G,hG,ha,hagree⟩ := exists_smooth_cost_branch_with_action
    (reverseRay z) (reverseRay_nonconjugate z hz)
  refine ⟨G,hG,?_,hagree⟩
  filter_upwards [continuous_reverseRay.continuousAt.eventually ha] with r hr
  rw [norm_reverseRay,reverseRay_endpoint,reverseRay_base] at hr
  exact hr

end EndpointLowerJet
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_RadialNull
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder

section TransportCertificates
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

omit [MetricSpace M] [BorelSpace M] in
lemma density_nonnegative {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    ∀ᵐ x ∂vol, 0 ≤ rho x := by
  filter_upwards [hrho.2.2.2] with x hx
  exact hlam.le.trans hx.1

omit [MetricSpace M] [BorelSpace M] in
lemma densityMeasure_probability {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    IsProbabilityMeasure (densityMeasure vol rho) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hrho.2.1 (density_nonnegative hlam hrho),
    hrho.2.2.1, ENNReal.ofReal_one]

end TransportCertificates

open scoped BoundedContinuousFunction

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_CompactDual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma cTransform_add_const {v : M → ℝ} (hv : Continuous v) (a : ℝ) :
    cTransform (fun x => v x + a) = fun x => cTransform v x - a := by
  funext x
  apply le_antisymm
  · rw [cTransform_le_iff (v := fun x => v x + a) (hv.add continuous_const)]
    intro y
    have hh := ((cTransform_le_iff hv x (cTransform v x)).mp le_rfl) y
    linarith
  · obtain ⟨y, hy, _⟩ := exists_cTransform_contact hv x
    have hh := cTransform_gap_nonneg (v := fun x => v x + a) (hv.add continuous_const) x y
    dsimp [contactGap] at hh
    linarith

variable [MeasurableSpace M] [BorelSpace M]

omit [CompactSpace M] [Nonempty M] in
lemma dualObjective_add_constants (mu nu : Measure M) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (a b : M →ᵇ ℝ) (k : ℝ) :
    dualObjective mu nu (a + BoundedContinuousFunction.const M (-k),
      b + BoundedContinuousFunction.const M k) = dualObjective mu nu (a,b) := by
  change (∫ x, (a x + -k) ∂mu) + (∫ y, (b y + k) ∂nu) = _
  rw [integral_add (a.integrable mu) (integrable_const _),
    integral_add (b.integrable nu) (integrable_const _)]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  dsimp [dualObjective]
  ring

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_CompactCrossing
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma bilinear_lower_of_unit (L : E →L[ℝ] E →L[ℝ] ℝ) {c : ℝ}
    (h : ∀ v:E, ‖v‖=1 → c ≤ L v v) (v:E) : c*‖v‖^2 ≤ L v v := by
  by_cases hv : v=0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖=1 := by simp only [w,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have he : v=‖v‖ • w := by dsimp [w]; rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  have H := mul_le_mul_of_nonneg_left (h w hw) (sq_nonneg ‖v‖)
  calc
    c*‖v‖^2 = ‖v‖^2*c := mul_comm _ _
    _ ≤ ‖v‖^2*L w w := H
    _ = L (‖v‖ • w) (‖v‖ • w) := by simp only [map_smul,smul_apply,smul_eq_mul] <;> ring
    _ = L v v := by rw [←he]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_PositiveBilinearBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Metric

namespace WeakMTWTransport
section PositiveBilinearBound
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_bilinear_positive_baseline (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E,v≠0 → 0 < B v v) :
    ∃ m>0,∀ v : E,m*‖v‖^2≤B v v := by
  let S := sphere (0:E) 1
  have hS : IsCompact S := isCompact_sphere _ _
  have hc : ContinuousOn (fun v:E => B v v) S :=
    (B.continuous.clm_apply continuous_id).continuousOn
  obtain ⟨m,hm,Hm⟩ : ∃ m>0,∀ v∈S,m≤B v v := by
    by_cases hne : S.Nonempty
    · obtain ⟨v,hv,Hv⟩ := hS.exists_isMinOn hne hc
      have hn : ‖v‖=1 := by simpa only [S,mem_sphere,dist_zero_right] using hv
      have hp : 0 < B v v := hB v (by intro he; simp [he] at hn)
      exact ⟨B v v,hp,fun w hw => Hv hw⟩
    · exact ⟨1,zero_lt_one,fun v hv => (hne ⟨v,hv⟩).elim⟩
  exact ⟨m,hm,bilinear_lower_of_unit B (fun v hv => Hm v (by simpa only [S,mem_sphere,dist_zero_right] using hv))⟩

end PositiveBilinearBound
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section DividedBaseline
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma divided_hessian_decrease {a : M} {r ξ : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) (hs : s<1) :
    hessianValue a (s • r) ξ/s ≤ hessianValue a (t • r) ξ/t := by
  rcases eq_or_lt_of_le hts with h | h
  · simp only [h,le_refl]
  by_cases hξ : ξ=0
  · subst ξ
    rw [hessianValue_eq_normalHessian (contracted_minimizer_mem_injectivityDomain hr (ht.trans h) hs),
      hessianValue_eq_normalHessian (contracted_minimizer_mem_injectivityDomain hr ht (h.trans hs))]
    simp only [map_zero,zero_div,le_refl]
  exact (divided_hessian_strict_decrease hr ht h hs hξ).le

lemma exists_divided_hessian_baseline {a : M} {r : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {t s0 : ℝ} (ht : 0 < t) (hts : t < s0) (hs0 : s0<1) :
    ∃ m>0,∀ s : ℝ,s0 ≤ s → s<1 → ∀ ξ : TangentSpace 𝓘(ℝ,Model n) a,
      m*‖ξ‖^2 ≤ hessianValue a (t • r) ξ/t-hessianValue a (s • r) ξ/s := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) a) := inferInstanceAs (FiniteDimensional ℝ (Model n))
  let B := t⁻¹ • normalHessian a (t • r)-s0⁻¹ • normalHessian a (s0 • r)
  have hIDt := contracted_minimizer_mem_injectivityDomain hr ht (hts.trans hs0)
  have hIDs := contracted_minimizer_mem_injectivityDomain hr (ht.trans hts) hs0
  have hB (ξ : TangentSpace 𝓘(ℝ,Model n) a) : B ξ ξ=
      hessianValue a (t • r) ξ/t-hessianValue a (s0 • r) ξ/s0 := by
    rw [hessianValue_eq_normalHessian hIDt,hessianValue_eq_normalHessian hIDs]
    simp only [B,sub_apply,smul_apply,smul_eq_mul]
    ring
  obtain ⟨m,hm,Hm⟩ := exists_bilinear_positive_baseline B (fun ξ hξ => by
    rw [hB]
    exact sub_pos.mpr (divided_hessian_strict_decrease hr ht hts hs0 hξ))
  refine ⟨m,hm,?_⟩
  intro s hss hs1 ξ
  have H := Hm ξ
  rw [hB] at H
  have Hd := divided_hessian_decrease (ξ := ξ) hr (ht.trans hts) hss hs1
  linarith only [H,Hd]

end DividedBaseline
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_SectionOscillation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

section SectionOscillation
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

variable [MeasurableSpace M] [BorelSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
lemma reverseNormalizedPair_mem {x0 : M} {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)}
    (huv : uv ∈ normalizedDualPairs x0) :
    reverseNormalizedPair x0 uv ∈ normalizedDualPairs x0 := by
  change (uv.2 x0 + -uv.2 x0 = 0) ∧ _ ∧ _
  refine ⟨add_neg_cancel _, ?_, ?_⟩
  · apply BoundedContinuousFunction.ext
    intro x
    change cTransform (fun y => uv.1 y + uv.2 x0) x = uv.2 x + -uv.2 x0
    rw [cTransform_add_const uv.1.continuous]
    have hh := congrArg (fun f : M →ᵇ ℝ => f x) huv.2.2
    change cTransform uv.1 x = uv.2 x at hh
    change cTransform uv.1 x - uv.2 x0 = uv.2 x + -uv.2 x0
    rw [hh]
    ring
  · apply BoundedContinuousFunction.ext
    intro x
    change cTransform (fun y => uv.2 y + -uv.2 x0) x = uv.1 x + uv.2 x0
    rw [cTransform_add_const uv.2.continuous]
    have hh := congrArg (fun f : M →ᵇ ℝ => f x) huv.2.1
    change cTransform uv.2 x = uv.1 x at hh
    change cTransform uv.2 x - -uv.2 x0 = uv.1 x + uv.2 x0
    rw [hh]
    ring

lemma densityDualClass_reverse {vol : Measure M} {lam cap : ℝ} (hlam : 0 < lam)
    {x0 : M} {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)}
    (huv : uv ∈ densityDualClass vol lam cap x0) :
    reverseNormalizedPair x0 uv ∈ densityDualClass vol lam cap x0 := by
  obtain ⟨hnorm, rho0, rho1, hrho0, hrho1, hmin⟩ := huv
  let := densityMeasure_probability hlam hrho0
  let := densityMeasure_probability hlam hrho1
  refine ⟨reverseNormalizedPair_mem hnorm, rho1, rho0, hrho1, hrho0, ?_⟩
  intro a b hab
  have hba : ∀ x y, 0 ≤ contactGap b a x y := by
    intro x y
    have hh := hab y x
    dsimp [contactGap] at hh ⊢
    rw [cost_symm y x] at hh
    linarith
  have hh := hmin b a hba
  rw [reverseNormalizedPair, dualObjective_add_constants]
  dsimp [dualObjective] at hh ⊢
  linarith

end SectionOscillation

open Filter

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_LocalOuterLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section LocalOuterLog
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_local_outer_log_jet_bound (hmtw:WeakMTW (n := n) (M := M))
    {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap)
    (z:TangentBundle 𝓘(ℝ,Model n) M) (hmin:z.2∈minimizingVectors z.1)
    (hnc:Function.Injective (fderiv ℝ (fun v=>extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2))
    {l:ℝ} (hl:1 < l) :
    let χ:=extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
    ∃U:Set ((Model n×Model n)×ℝ),U∈𝓝 (χ z,l) ∧ ∃C≥0,
      ∀q∈U,∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      let r:=χ.symm q.1
      ∀φ:ℝ → ℝ,StrictMono φ → ContDiffAt ℝ 2 φ (uv.2 (riemannianExp r.1 r.2)) →
      HasDerivAt φ q.2 (uv.2 (riemannianExp r.1 r.2)) →
      iteratedDeriv 2 φ (uv.2 (riemannianExp r.1 r.2)) ≤ 0 →
      ∀B:Model n →L[ℝ] Model n →L[ℝ] ℝ,(∀d,0 ≤ B d d) →
      HasLowerSecondTaylor (fun d=>
        let s:=χ.symm (q.1.1,q.1.2+d)
        φ (uv.2 (riemannianExp s.1 s.2))+‖s.2‖^2/2) 0 B →
      ∀d,B d d ≤ C*‖d‖^2 := by
  dsimp only
  let χ:=extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
  let d:=extChartAt 𝓘(ℝ,Model n) (riemannianExp z.1 z.2)
  obtain ⟨e,he,hze,heχ,hes,hfe,hge⟩:=exists_joint_exp_inverse_of_nonconjugate z hnc
  have hefirst:∀q,(e q).1=q.1 := by intro q; rw [he]
  obtain ⟨W,hW,hWe,K,hK,HK⟩:=exists_uniform_fiber_jet_transfer e hefirst hfe hge hze
  obtain ⟨G,hG,hact,hagree⟩:=exists_reverse_branch_with_forward_action z hnc
  have Hb:=hmtw.exists_local_branch_jet_bound_second hlam hcap
    (reverseRay_minimizing hmin) hG hagree hl
  simp only [reverseRay_base,reverseRay_endpoint] at Hb
  obtain ⟨N,hN,C,hC,HN⟩:=Hb
  have hχleft:χ.symm (χ z)=z := χ.left_inv (mem_extChartAt_source z)
  have hχsym:ContinuousAt χ.symm (χ z) := continuousAt_extChartAt_symm'' (mem_extChartAt_target z)
  have hχlim:Tendsto χ.symm (𝓝 (χ z)) (𝓝 z) := by simpa only [hχleft] using hχsym.tendsto
  have hAct:∀ᶠ q in 𝓝 (χ z),G (riemannianExp (χ.symm q).1 (χ.symm q).2,(χ.symm q).1)=‖(χ.symm q).2‖^2/2 :=
    hχlim.eventually hact
  obtain ⟨V,hV,hVo,hVz⟩:=mem_nhds_iff.mp (inter_mem hW hAct)
  have hVe:V⊆e.source := fun q hq=>hWe (hV hq).1
  let J:=fun q:(Model n×Model n)×ℝ=>(((e q.1).2,(χ.symm q.1).1),q.2)
  have hJ:ContinuousAt J (χ z,l) := by
    have hE : ContinuousAt (fun q : (Model n × Model n) × ℝ => e q.1) (χ z,l) :=
      (e.continuousAt hze).comp (x := (χ z,l)) (f := Prod.fst) continuousAt_fst
    have hχ : ContinuousAt (fun q : (Model n × Model n) × ℝ => χ.symm q.1) (χ z,l) :=
      hχsym.comp (x := (χ z,l)) (f := Prod.fst) continuousAt_fst
    have hb := (FiberBundle.continuous_proj (Model n)
      (TangentSpace 𝓘(ℝ,Model n))).continuousAt.comp hχ
    exact (hE.snd.prodMk hb).prodMk continuousAt_snd
  have hJ0:J (χ z,l)=((d (riemannianExp z.1 z.2),z.1),l) := by
    dsimp only [J]
    rw [he]
    dsimp only
    rw [hχleft]
  let U:=Prod.fst ⁻¹' V ∩ J ⁻¹' N
  have hU:U∈𝓝 (χ z,l) := inter_mem
    (continuous_fst.continuousAt.preimage_mem_nhds (hVo.mem_nhds hVz))
    (hJ.preimage_mem_nhds (by rwa [hJ0]))
  refine ⟨U,hU,C*K,mul_nonneg hC hK,?_⟩
  intro q hq x0 uv huv φ hmono hφ hd hconc B hB hjet ξ
  let r:=χ.symm q.1
  let v:=fun w:Model n=>φ (uv.2 (d.symm w))+G (d.symm w,r.1)
  have hqe:q.1∈e.source := hVe hq.1
  have hepoint:d.symm (e q.1).2=riemannianExp r.1 r.2 := by
    rw [he]
    exact d.left_inv (hes q.1 hqe)
  have HEq:(fun δ:Model n=>v ((e (q.1.1,q.1.2+δ)).2)) =ᶠ[𝓝 0]
      (fun δ=>let s:=χ.symm (q.1.1,q.1.2+δ)
        φ (uv.2 (riemannianExp s.1 s.2))+‖s.2‖^2/2) := by
    have ht:ContinuousAt (fun δ:Model n=>(q.1.1,q.1.2+δ)) 0 :=
      continuousAt_const.prodMk (continuousAt_const.add continuousAt_id)
    have hv0:(q.1.1,q.1.2+(0:Model n))∈V := by simpa only [add_zero,Prod.eta] using (show q.1∈V from hq.1)
    filter_upwards [ht.preimage_mem_nhds (hVo.mem_nhds hv0)] with δ hδ
    have hδe:=hVe hδ
    have haδ: G (riemannianExp (χ.symm (q.1.1,q.1.2+δ)).1 (χ.symm (q.1.1,q.1.2+δ)).2,
        (χ.symm (q.1.1,q.1.2+δ)).1)=‖(χ.symm (q.1.1,q.1.2+δ)).2‖^2/2 := (hV hδ).2
    dsimp only [v]
    rw [he]
    dsimp only
    rw [d.left_inv (hes _ hδe)]
    have hb:(χ.symm (q.1.1,q.1.2+δ)).1=r.1 := rfl
    rw [hb] at haδ
    congr 1
  have hjet':HasLowerSecondTaylor (fun δ:Model n=>v ((e (q.1.1,q.1.2+δ)).2)) 0 B :=
    hjet.mono HEq.eq_of_nhds.symm HEq.symm.le
  apply HK q.1 (hV hq.1).1 v B hjet' hB C hC _ ξ
  intro H hH hHjet η
  apply HN (J q) hq.2 x0 uv huv φ hmono _ _ _ H hH _ η
  · change ContDiffAt ℝ 2 φ (uv.2 (d.symm (e q.1).2))
    rw [hepoint]
    exact hφ
  · change HasDerivAt φ q.2 (uv.2 (d.symm (e q.1).2))
    rw [hepoint]
    exact hd
  · change iteratedDeriv 2 φ (uv.2 (d.symm (e q.1).2)) ≤ 0
    rw [hepoint]
    exact hconc
  · exact hHjet

end LocalOuterLog
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_OuterCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section OuterCoordinate
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_outer_coordinate_jet_bound (hmtw:WeakMTW (n := n) (M := M))
    {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {a:M}
    {p:Model n} (hmin:p∈minimizingVectors a)
    (hnc:Function.Injective (fderiv ℝ (fun v=>extChartAt 𝓘(ℝ,Model n)
      (riemannianExp a p) (riemannianExp a v)) p))
    {l:ℝ} (hl:1 < l) :
    ∃U:Set ((Model n×Model n)×ℝ),U∈𝓝 ((extChartAt 𝓘(ℝ,Model n) a a,(p:Model n)),l) ∧ ∃C≥0,
      ∀q∈U,∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀φ:ℝ → ℝ,StrictMono φ → ContDiffAt ℝ 2 φ (uv.2 (movingNormal a q.1)) →
      HasDerivAt φ q.2 (uv.2 (movingNormal a q.1)) →
      iteratedDeriv 2 φ (uv.2 (movingNormal a q.1)) ≤ 0 →
      ∀B:Model n →L[ℝ] Model n →L[ℝ] ℝ,(∀d,0 ≤ B d d) →
      HasLowerSecondTaylor (fun d=>φ (uv.2 (movingNormal a (q.1.1,q.1.2+d)))+
        ‖chartFiberInverse a q.1.1 (q.1.2+d)‖^2/2) 0 B →
      ∀d,B d d ≤ C*‖d‖^2 := by
  let z:TangentBundle 𝓘(ℝ,Model n) M:=⟨a,p⟩
  have H:=hmtw.exists_local_outer_log_jet_bound hlam hcap z hmin hnc hl
  dsimp only at H
  have hz:extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z z=
      (extChartAt 𝓘(ℝ,Model n) a a,(p:Model n)) := tangent_chart_at_self_base z p
  rw [hz] at H
  obtain ⟨U,hU,C,hC,HC⟩:=H
  let V:=U∩(fun q:(Model n×Model n)×ℝ=>q.1.1) ⁻¹' (extChartAt 𝓘(ℝ,Model n) a).target
  have hV:V∈𝓝 ((extChartAt 𝓘(ℝ,Model n) a a,(p:Model n)),l) :=
    inter_mem hU ((continuous_fst.comp continuous_fst).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target a).mem_nhds (mem_extChartAt_target a)))
  refine ⟨V,hV,C,hC,?_⟩
  intro q hq x0 uv huv φ hmono hφ hd hconc B hB hjet d
  have hqt:q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).target := hq.2
  apply HC q hq.1 x0 uv huv φ hmono
  · exact hφ
  · exact hd
  · exact hconc
  · exact hB
  · convert hjet using 1
    all_goals try with_reducible_and_instances rfl
    funext δ
    have he:=tangent_chart_symm_trivialization (q := (q.1.1,q.1.2+δ)) hqt
    change (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z).symm (q.1.1,q.1.2+δ)=_ at he
    rw [he]
    simp only [movingNormal_eq hqt]
end OuterCoordinate
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_OuterSplitLowerTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section OuterSplitLowerTest
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma outer_split_lower_test {v : M → ℝ} {a : M}
    {r : TangentSpace 𝓘(ℝ,Model n) a} (hr : r∈minimizingVectors a)
    {φ : ℝ → ℝ} (hmono : StrictMono φ) (hφ : ContDiffAt ℝ 2 φ (v a))
    {l : ℝ} (hd : HasDerivAt φ l (v a)) (hl : l≠0)
    (hmount : ∀ y : M,φ (v a)+cost a (riemannianExp a r)-cost y (riemannianExp a r)≤φ (v y))
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ f : TangentSpace 𝓘(ℝ,Model n) a → ℝ, ContDiffAt ℝ 2 f 0 ∧ f 0=v a ∧
      (∀ᶠ h in 𝓝 0,f h≤v (riemannianExp a h)) ∧
      fderiv ℝ f 0=innerSL ℝ (l⁻¹ • r) ∧
      ∀ ξ,fderiv ℝ (fderiv ℝ f) 0 ξ ξ=
        -(l*s)⁻¹*hessianValue a (s • r) ξ-
          (iteratedDeriv 2 φ (v a)/l^3)*(inner ℝ r ξ)^2 := by
  let : Nonempty M := ⟨a⟩
  let F : TangentSpace 𝓘(ℝ,Model n) a → ℝ := fun h =>
    scalarCostSupport id (φ (v a)) a r s (riemannianExp a h)
  have hsp := contracted_minimizer_mem_injectivityDomain hr hs hs1
  obtain ⟨hF,hDF,hHF⟩ := scalarCostSupport_normal_jet (φ := id) (v0 := φ (v a))
    (l := 1) hs.ne' hsp contDiffAt_id (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hD : fderiv ℝ F 0=innerSL ℝ r := by simpa only [one_smul] using hDF.fderiv
  have hFv : F 0=φ (v (riemannianExp a (0 : TangentSpace 𝓘(ℝ,Model n) a))) := by
    simp only [F,riemannianExp_zero,scalarCostSupport_self,id_eq]
  have hlo : ∀ᶠ h in 𝓝 0,F h≤φ (v (riemannianExp a h)) := by
    apply Filter.Eventually.of_forall
    intro h
    have H := hmount (riemannianExp a h)
    have Hs := minimizing_split_upper_support hr hs hs1 (riemannianExp a h)
    have He := minimizing_split_contact hr hs hs1
    dsimp only [F,scalarCostSupport,id_eq]
    linarith only [H,Hs,He]
  obtain ⟨f,hf,hfv,hfl,hfd,hfh⟩ := scalar_inverse_lower_test hmono
    (v := fun h => v (riemannianExp a h)) (x := 0)
    (by simpa only [riemannianExp_zero] using hφ)
    (by simpa only [riemannianExp_zero] using hd) hl hF hFv hlo
  refine ⟨f,hf,by simpa only [riemannianExp_zero] using hfv,hfl,?_,?_⟩
  · rw [hfd,hD,map_smul]
  · intro ξ
    rw [hfh,hD]
    have H := hHF ξ
    change fderiv ℝ (fderiv ℝ F) 0 ξ ξ=_ at H
    simp only [iteratedDeriv_succ,iteratedDeriv_zero,deriv_id',deriv_const,zero_mul,add_zero,one_div] at H
    rw [H,riemannianExp_zero,innerSL_apply_apply]
    ring

end OuterSplitLowerTest
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_OuterNonconjugacy
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section OuterNonconjugacy
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.modified_outer_nonconjugate (hmtw : WeakMTW (n := n) (M := M))
    {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap) {x0 a : M}
    {uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)} (huv : uv∈densityDualClass (metricVolume n) lam cap x0)
    {r : TangentSpace 𝓘(ℝ,Model n) a} (hr : r∈minimizingVectors a)
    {φ : ℝ → ℝ} (hmono : StrictMono φ) (hφ : ContDiffAt ℝ 2 φ (uv.1 a))
    {l : ℝ} (hd : HasDerivAt φ l (uv.1 a)) (hl : 1 < l)
    (hconc : iteratedDeriv 2 φ (uv.1 a) ≤ 0)
    (hmount : ∀ y : M,φ (uv.1 a)+cost a (riemannianExp a r)-cost y (riemannianExp a r) ≤ φ (uv.1 y)) :
    Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp a r) (riemannianExp a v)) r) := by
  have hlp : 0 < l := zero_lt_one.trans hl
  have ht : 0 < l⁻¹ := inv_pos.mpr hlp
  have ht1 : l⁻¹ < 1 := (inv_lt_one₀ hlp).mpr hl
  let s0 := (l⁻¹+1)/2
  have hts : l⁻¹ < s0 := by dsimp [s0]; linarith only [ht1]
  have hs0 : s0 < 1 := by dsimp [s0]; linarith only [ht1]
  have hp := contracted_minimizer_mem_injectivityDomain hr ht ht1
  obtain ⟨m,hm,Hm⟩ := exists_divided_hessian_baseline hr ht hts hs0
  obtain ⟨C,hC,HC⟩ := hmtw.exists_normal_relative_hessian_bound hlam hcap hp (div_pos hm hlp)
  let D := fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n) (riemannianExp a r) (riemannianExp a v)) r
  have hz (ξ : TangentSpace 𝓘(ℝ,Model n) a) (hξ : D ξ=0) : ξ=0 := by
    by_contra hne
    have hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) a) 𝓘(ℝ,Model n)
        (riemannianExp a) r ξ=0 := by rw [exp_mfderiv_apply_eq_coordinate]; exact hξ
    have H := conjugate_radial_hessian_tendsto_atBot hr hk (inner_self_ne_zero.mpr hne)
    let A := hessianValue a (l⁻¹ • r) ξ
    let K := |A|+C*‖ξ‖^2
    have hK : 0 ≤ K := add_nonneg (abs_nonneg A) (mul_nonneg hC (sq_nonneg _))
    have hb := H.eventually (eventually_lt_atBot (-l*K-1))
    have hn : ∀ᶠ s : ℝ in 𝓝[<] 1,s0 ≤ s ∧ s < 1 :=
      (((eventually_gt_nhds hs0).filter_mono nhdsWithin_le_nhds).mono (fun _ h => h.le)).and self_mem_nhdsWithin
    obtain ⟨s,hs,hlt⟩ := (hn.and hb).exists
    have hsp : 0 < s := ht.trans_le (hts.le.trans hs.1)
    obtain ⟨f,hf,hfv,hflo,hfD,hfH⟩ := outer_split_lower_test hr hmono hφ hd hlp.ne' hmount hsp hs.2
    have hscalar (d : TangentSpace 𝓘(ℝ,Model n) a) :
        0 ≤ -(iteratedDeriv 2 φ (uv.1 a)/l^3)*(inner ℝ r d)^2 :=
      mul_nonneg (neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hconc (pow_nonneg hlp.le _))) (sq_nonneg _)
    have hpos (d : TangentSpace 𝓘(ℝ,Model n) a) :
        (m/l)*‖d‖^2 ≤ fderiv ℝ (fderiv ℝ f) 0 d d+hessianValue a (l⁻¹ • r) d := by
      rw [hfH]
      have Hbase := mul_le_mul_of_nonneg_left (Hm s hs.1 hs.2 d) ht.le
      have Halgebra : l⁻¹*(hessianValue a (l⁻¹ • r) d/l⁻¹-hessianValue a (s • r) d/s)=
          -(l*s)⁻¹*hessianValue a (s • r) d+hessianValue a (l⁻¹ • r) d := by
        field_simp
        ring
      rw [Halgebra] at Hbase
      have HP := hscalar d
      simp only [div_eq_mul_inv] at Hbase HP ⊢
      nlinarith only [Hbase,HP]
    have HB := HC x0 uv huv f hf hfD hfv.symm hflo hpos ξ
    rw [hfH] at HB
    have HA : -A ≤ |A| := neg_le_abs A
    have HS := hscalar ξ
    have Hbound : -hessianValue a (s • r) ξ/(l*s) ≤ K := by
      dsimp [A,K] at *
      simp only [mul_inv_rev,div_eq_mul_inv] at *
      nlinarith only [HB,HA,HS]
    have Hmul := (div_le_iff₀ (mul_pos hlp hsp)).mp Hbound
    have Hls : l*s ≤ l := by nlinarith only [hs.2,hlp]
    have Hmul' := mul_le_mul_of_nonneg_left Hls hK
    linarith only [Hmul,Hmul',hlt]
  intro p q hpq
  apply sub_eq_zero.mp
  apply hz (p-q)
  rw [map_sub,hpq,sub_self]

end OuterNonconjugacy
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActiveGraphLimit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]

lemma chartFiberInverse_at_center (a : M) (p : Model n) :
    chartFiberInverse a ((extChartAt 𝓘(ℝ,Model n) a) a) p=p := by
  dsimp only [chartFiberInverse]
  rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)]
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source (Model n) a)]
  exact tangentCoordChange_self (I := 𝓘(ℝ,Model n)) (mem_extChartAt_source a)
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ParametricActive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ParametricActive
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma activeLogs_iff_minimum {v:M → ℝ} (hv:Continuous v) {x:M}
    {p:TangentSpace 𝓘(ℝ,Model n) x} : p∈activeLogs v x ↔
    p∈minimizingVectors x ∧ ∀ y:M,v (riemannianExp x p)+cost x (riemannianExp x p) ≤ v y+cost x y := by
  constructor
  · rintro ⟨hm,hcontact⟩
    refine ⟨hm,fun y=>?_⟩
    have H:=cTransform_gap_nonneg hv x y
    dsimp only [contactGap] at *
    linarith only [H,hcontact]
  · rintro ⟨hm,hmin⟩
    refine ⟨hm,?_⟩
    obtain ⟨y,hy⟩:=cTransform_gap_zero hv x
    have H:=cTransform_gap_nonneg hv x (riemannianExp x p)
    have HH:=hmin y
    dsimp only [contactGap] at *
    linarith only [H,HH,hy]

end ParametricActive
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActiveOuter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section ActiveOuter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.active_outer_nonconjugate (hmtw:WeakMTW (n := n) (M := M))
    {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {x0:M}
    {uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)} (huv:uv∈densityDualClass (metricVolume n) lam cap x0)
    {φ:ℝ → ℝ} (hφc:Continuous φ) (hmono:StrictMono φ)
    {z:TangentBundle 𝓘(ℝ,Model n) M}
    (ha:z.2∈activeLogs (φ ∘ uv.2) z.1)
    (hφ:ContDiffAt ℝ 2 φ (uv.2 (riemannianExp z.1 z.2)))
    {l:ℝ} (hd:HasDerivAt φ l (uv.2 (riemannianExp z.1 z.2))) (hl:1 < l)
    (hconc:iteratedDeriv 2 φ (uv.2 (riemannianExp z.1 z.2)) ≤ 0) :
    Function.Injective (fderiv ℝ (fun v=>extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2) := by
  let w:=reverseRay z
  let vu:=reverseNormalizedPair x0 uv
  let ψ:=fun s:ℝ=>φ (uv.2 x0+s)
  have hnorm (y:M):uv.2 x0+vu.1 y=uv.2 y := by
    change uv.2 x0+(uv.2 y+-uv.2 x0)=uv.2 y
    ring
  have hbase:uv.2 x0+vu.1 w.1=uv.2 (riemannianExp z.1 z.2) := by
    rw [hnorm,show w.1=riemannianExp z.1 z.2 from reverseRay_base z]
  have hψ:ContDiffAt ℝ 2 ψ (vu.1 w.1) := by
    exact (hbase.symm ▸ hφ).comp _ (contDiffAt_const.add contDiffAt_id)
  have hψD:HasDerivAt ψ l (vu.1 w.1) := by
    have hd':HasDerivAt φ l (uv.2 x0+vu.1 w.1) := hbase.symm ▸ hd
    have H:=hd'.comp (vu.1 w.1) ((hasDerivAt_id (vu.1 w.1)).const_add (uv.2 x0))
    simpa only [mul_one,Function.comp_def,ψ] using H
  have hψC:iteratedDeriv 2 ψ (vu.1 w.1) ≤ 0 := by
    dsimp only [ψ]
    rw [iteratedDeriv_comp_const_add]
    dsimp only
    rw [hbase]
    exact hconc
  have hψmono:StrictMono ψ := fun _ _ h=>hmono (by linarith)
  have hm:∀y:M,ψ (vu.1 w.1)+cost w.1 (riemannianExp w.1 w.2)-
      cost y (riemannianExp w.1 w.2) ≤ ψ (vu.1 y) := by
    intro y
    have H:=((activeLogs_iff_minimum (hφc.comp uv.2.continuous)).mp ha).2 y
    dsimp only [Function.comp_apply] at H
    dsimp only [ψ]
    rw [hnorm,hnorm,show riemannianExp w.1 w.2=z.1 from reverseRay_endpoint z,
      show w.1=riemannianExp z.1 z.2 from reverseRay_base z,cost_symm _ z.1,cost_symm y z.1]
    linarith only [H]
  have H:=hmtw.modified_outer_nonconjugate hlam hcap (densityDualClass_reverse hlam huv)
    (reverseRay_minimizing ha.1) hψmono hψ hψD hl hψC hm
  have H':=reverseRay_nonconjugate w H
  have hw:reverseRay w=z := reverseRay_involutive z
  rw [hw] at H'
  exact H'

end ActiveOuter
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ModifiedOuterNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section ModifiedOuterNeighborhood
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.modified_outer_neighborhood_oai (hmtw:WeakMTW (n := n) (M := M))
    {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {x0:M}
    {uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)} (huv:uv∈densityDualClass (metricVolume n) lam cap x0)
    {Φ:ℝ×ℝ → ℝ} (hΦ:ContDiff ℝ ∞ Φ) {β:ℝ} (hmono:StrictMono (fun s=>Φ (β,s)))
    {a:M} {p:Model n}
    (ha:p∈activeLogs (fun y=>Φ (β,uv.2 y)) a)
    (hslope:1 < deriv (fun s=>Φ (β,s)) (uv.2 (riemannianExp a p)))
    (hcurve:iteratedDeriv 2 (fun s=>Φ (β,s)) (uv.2 (riemannianExp a p)) < 0) :
    ∃V:Set ((Model n×Model n)×ℝ),V∈𝓝 ((extChartAt 𝓘(ℝ,Model n) a a,(p:Model n)),β) ∧
      ∃C≥0,∀q∈V,StrictMono (fun s=>Φ (q.2,s)) →
      ∀B:Model n →L[ℝ] Model n →L[ℝ] ℝ,(∀d,0 ≤ B d d) →
      HasLowerSecondTaylor (fun d=>Φ (q.2,uv.2 (movingNormal a (q.1.1,q.1.2+d)))+
        ‖chartFiberInverse a q.1.1 (q.1.2+d)‖^2/2) 0 B →
      ∀d,B d d ≤ C*‖d‖^2 := by
  have hφ:=scalar_family_contDiff hΦ β
  have hφ2:ContDiff ℝ 2 (fun s=>Φ (β,s)):=hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hnc:=hmtw.active_outer_nonconjugate hlam hcap huv hφ.continuous hmono
    (z := (⟨a,p⟩:TangentBundle 𝓘(ℝ,Model n) M)) ha hφ2.contDiffAt (scalar_family_derivable hΦ (β,uv.2 (riemannianExp a p))) hslope hcurve.le
  obtain ⟨U,hU,C,hC,HC⟩:=hmtw.exists_outer_coordinate_jet_bound hlam hcap ha.1 hnc hslope
  let q0:(Model n×Model n)×ℝ:=((extChartAt 𝓘(ℝ,Model n) a a,(p:Model n)),β)
  have he:movingNormal a q0.1=riemannianExp a p := by
    change movingNormal a (extChartAt 𝓘(ℝ,Model n) a a,p)=_
    rw [movingNormal_eq (mem_extChartAt_target (I := 𝓘(ℝ,Model n)) a)]
    change riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a))
      (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a) p)=_
    rw [chartFiberInverse_at_center]
    congr 1
    exact (extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)
  have hf:ContinuousAt (fun q:Model n×Model n=>uv.2 (movingNormal a q)) q0.1 :=
    uv.2.continuous.continuousAt.comp ((movingNormal_contMDiffAt
      (q := q0.1) (mem_extChartAt_target a)).continuousAt)
  obtain ⟨V,hV,HV⟩:=scalar_jet_neighborhood hf (continuous_scalar_family_deriv hΦ) (continuous_scalar_family_second hΦ)
    (by simpa only [he,q0] using hU) (by simpa only [he,q0] using hcurve)
  refine ⟨V,hV,C,hC,?_⟩
  intro q hq hm B hB hjet d
  exact HC _ (HV q hq).1 x0 uv huv (fun s=>Φ (q.2,s)) hm
    (((scalar_family_contDiff hΦ q.2).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt)
    (scalar_family_derivable hΦ (q.2,uv.2 (movingNormal a q.1))) (HV q hq).2.le B hB hjet d

end ModifiedOuterNeighborhood
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.modified_outer_neighborhood_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.modified_outer_neighborhood_oai.{u_1}
