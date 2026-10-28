-- Prove2me | solution 1 for OAI.WeakHessian.RCD.compact_core_localized_pairing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T18:57:41.856373+00:00
-- url     : https://prove2.me/submissions/bd6b9386-a878-49d6-bcde-f23e66089ab8

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh007
import Theorems.Thm_OAI_WeakHessian_RCD_test_gradientSquare_sobolev

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_DriftResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile148
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [SigmaFinite m] in
lemma norm_gamma_toLp_le (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {V u : X → ℝ}
    {L : ℝ≥0} (hV : LipschitzWith L V) (hu : Sobolev m u) :
    ‖(memLp_gamma_of_lipschitz hfinite hpar hV hu).toLp (gamma m V u)‖ ≤
      (L:ℝ)*‖hu.2.2.toLp (weakGradient m u)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(memLp_gamma_of_lipschitz hfinite hpar hV hu).coeFn_toLp,hu.2.2.coeFn_toLp,
    abs_gamma_le hfinite hpar (localSobolev_of_lipschitz hfinite hV) hu.2.1,
    weakGradient_le_lipschitz hfinite hV,weakGradient_nonneg (m := m) u]
    with x hb hd hab hv hn
  rw [hb,hd,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hn]
  exact hab.trans (mul_le_mul_of_nonneg_right hv hn)
end WeakHessian

end
end InlinedFile148

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_TestLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile128
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

variable [SigmaFinite m]

lemma RCD.test_gamma_sobolev {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {u v : X → ℝ} (hu : IsTestFunction m u) (hv : IsTestFunction m v) :
    Sobolev m (gamma m u v) := by
  have hpar := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  have hsquare {f : X → ℝ} (hf : IsTestFunction m f) : Sobolev m (gamma m f f) :=
    (sobolev_congr_ae (gamma_self (m := m) f)).mpr (hrcd.test_gradientSquare_sobolev hN hfull hfin o hf)
  have huS := (laplacian_isLaplacian hu.1).1
  have hvS := (laplacian_isLaplacian hv.1).1
  have He : (fun x => (2:ℝ)⁻¹*(gamma m (fun y => u y+v y) (fun y => u y+v y) x-gamma m u u x-gamma m v v x)) =ᵐ[m] gamma m u v := by
    filter_upwards [gamma_add_left hfin hpar huS.2.1 hvS.2.1 ((huS.add hfin hvS).2.1),
      gamma_add_right hfin hpar huS.2.1 huS.2.1 hvS.2.1,
      gamma_add_right hfin hpar hvS.2.1 huS.2.1 hvS.2.1,gamma_comm (m := m) v u] with x h1 h2 h3 h4
    rw [h1,h2,h3,h4]
    ring
  exact (sobolev_congr_ae He).mp (((hsquare (hu.add hfin hpar hv)).sub hfin (hsquare hu)).sub hfin (hsquare hv) |>.const_mul (2:ℝ)⁻¹)
end WeakHessian

end
end InlinedFile128

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_TestProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile129
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma IsLaplacian.mul_lipschitz (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u v A B : X → ℝ} (hu : IsLaplacian m u A) (hv : IsLaplacian m v B)
    {L M : ℝ≥0} (huL : LipschitzWith L u) (hvL : LipschitzWith M v)
    {C D : ℝ} (huB : ∀ x,|u x| ≤ C) (hvB : ∀ x,|v x| ≤ D) :
    IsLaplacian m (fun x => u x*v x)
      (fun x => A x*v x+B x*u x+2*gamma m u v x) := by
  have huD : ∀ᵐ x ∂m,|weakGradient m u x| ≤ L := by
    filter_upwards [weakGradient_nonneg (m := m) u,weakGradient_le_lipschitz hfin huL] with x hn hb
    simpa only [abs_of_nonneg hn] using hb
  have hvD : ∀ᵐ x ∂m,|weakGradient m v x| ≤ M := by
    filter_upwards [weakGradient_nonneg (m := m) v,weakGradient_le_lipschitz hfin hvL] with x hn hb
    simpa only [abs_of_nonneg hn] using hb
  have hAv := memLp_mul_bounded hu.2.1 hvL.continuous.aestronglyMeasurable (ae_of_all _ hvB)
  have hBu := memLp_mul_bounded hv.2.1 huL.continuous.aestronglyMeasurable (ae_of_all _ huB)
  have hgam := memLp_gamma_lipschitz hfin hpar hu.1 hvL
  refine ⟨hu.1.mul_bounded hfin hv.1.2.1 (ae_of_all _ hvB) hvD,(hAv.add hBu).add (hgam.const_mul 2),?_⟩
  intro w hw
  have h1 := hu.2.2 (fun x => w x*v x) (hw.mul_bounded hfin hv.1.2.1 (ae_of_all _ hvB) hvD)
  have h2 := hv.2.2 (fun x => w x*u x) (hw.mul_bounded hfin hu.1.2.1 (ae_of_all _ huB) huD)
  have hiu : Integrable (fun x => u x*gamma m v w x) m :=
    (integrable_gamma hfin hv.1 hw).bdd_mul huL.continuous.aestronglyMeasurable (ae_of_all _ huB)
  have hiv : Integrable (fun x => v x*gamma m u w x) m :=
    (integrable_gamma hfin hu.1 hw).bdd_mul hvL.continuous.aestronglyMeasurable (ae_of_all _ hvB)
  have hic : Integrable (fun x => gamma m u v x*w x) m := hgam.integrable_mul hw.1
  have hiA := hAv.integrable_mul hw.1
  have hiB := hBu.integrable_mul hw.1
  change Integrable (fun x => A x*v x*w x) m at hiA
  change Integrable (fun x => B x*u x*w x) m at hiB
  have he1 : (∫ x,gamma m u (fun y => w y*v y) x ∂m) =
      (∫ x,gamma m u v x*w x ∂m)+(∫ x,v x*gamma m u w x ∂m) := by
    rw [← integral_add hic hiv]
    apply integral_congr_ae
    filter_upwards [gamma_mul_left hfin hpar hw.2.1 hv.1.2.1 hu.1.2.1 (ae_of_all _ hvB) hvD,
      gamma_comm (m := m) u (fun y => w y*v y),gamma_comm (m := m) v u,gamma_comm (m := m) w u] with x hh h0 h3 h4
    rw [h0,hh,h3,h4]
    ring
  have he2 : (∫ x,gamma m v (fun y => w y*u y) x ∂m) =
      (∫ x,gamma m u v x*w x ∂m)+(∫ x,u x*gamma m v w x ∂m) := by
    rw [← integral_add hic hiu]
    apply integral_congr_ae
    filter_upwards [gamma_mul_left hfin hpar hw.2.1 hu.1.2.1 hv.1.2.1 (ae_of_all _ huB) huD,
      gamma_comm (m := m) v (fun y => w y*u y),gamma_comm (m := m) w v] with x hh h0 h3
    rw [h0,hh,h3]
    ring
  rw [he1] at h1
  rw [he2] at h2
  have hp : (∫ x,gamma m (fun y => u y*v y) w x ∂m) =
      (∫ x,u x*gamma m v w x ∂m)+(∫ x,v x*gamma m u w x ∂m) := by
    rw [← integral_add hiu hiv]
    exact integral_congr_ae (gamma_mul_left hfin hpar hu.1.2.1 hv.1.2.1 hw.2.1 (ae_of_all _ hvB) hvD)
  have hA : (∫ x,A x*(w x*v x) ∂m) = ∫ x,(A x*v x)*w x ∂m := integral_congr_ae (ae_of_all _ fun x => by ring)
  have hB : (∫ x,B x*(w x*u x) ∂m) = ∫ x,(B x*u x)*w x ∂m := integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [hA] at h1
  rw [hB] at h2
  have hr : (∫ x,(A x*v x+B x*u x+2*gamma m u v x)*w x ∂m) =
      (∫ x,(A x*v x)*w x ∂m)+(∫ x,(B x*u x)*w x ∂m)+2*(∫ x,gamma m u v x*w x ∂m) := by
    simp_rw [add_mul,mul_assoc (2:ℝ)]
    rw [integral_add (f := fun x => A x*v x*w x+B x*u x*w x) (hiA.add hiB) (hic.const_mul 2),integral_add hiA hiB,integral_const_mul]
  rw [hp,hr]
  linarith

variable [SigmaFinite m]

lemma RCD.test_mul {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {u v : X → ℝ} (hu : IsTestFunction m u) (hv : IsTestFunction m v) :
    IsTestFunction m (fun x => u x*v x) := by
  have hpar := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  obtain ⟨L,hL⟩ := hu.2.2.1
  obtain ⟨M,hM⟩ := hv.2.2.1
  obtain ⟨C,hC⟩ := hu.2.1
  obtain ⟨D,hD⟩ := hv.2.1
  have hgen := (laplacian_isLaplacian hu.1).mul_lipschitz hfin hpar (laplacian_isLaplacian hv.1) hL hM hC hD
  have huD : ∀ᵐ x ∂m,|weakGradient m u x| ≤ L := by
    filter_upwards [weakGradient_nonneg (m := m) u,weakGradient_le_lipschitz hfin hL] with x hn hb
    simpa only [abs_of_nonneg hn] using hb
  have hvD : ∀ᵐ x ∂m,|weakGradient m v x| ≤ M := by
    filter_upwards [weakGradient_nonneg (m := m) v,weakGradient_le_lipschitz hfin hM] with x hn hb
    simpa only [abs_of_nonneg hn] using hb
  have huS := (laplacian_isLaplacian hu.1).1
  have hvS := (laplacian_isLaplacian hv.1).1
  have hsA := hu.2.2.2.mul_bounded hfin hvS.2.1 (ae_of_all _ hD) hvD
  have hsB := hv.2.2.2.mul_bounded hfin huS.2.1 (ae_of_all _ hC) huD
  refine ⟨⟨_,hgen⟩,⟨C*D,fun x => ?_⟩,⟨_,lipschitz_mul_bounded hL hM hC hD⟩,?_⟩
  · rw [abs_mul]
    exact mul_le_mul (hC x) (hD x) (abs_nonneg _) ((abs_nonneg _).trans (hC x))
  · exact (sobolev_congr_ae (hgen.ae_laplacian hfin)).mpr
      ((hsA.add hfin hsB).add hfin ((hrcd.test_gamma_sobolev hN hfull hfin o hu hv).const_mul 2))
end WeakHessian

end
end InlinedFile129

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_CompactCoreLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile159
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma boundedMulLp_inner_swap {χ : X → ℝ} (hχ : AEStronglyMeasurable χ m)
    {B : ℝ} (hB : ∀ᵐ x ∂m,|χ x| ≤ B) (f g : Lp ℝ 2 m) :
    ⟪boundedMulLp hχ hB f,g⟫_ℝ = ⟪f,boundedMulLp hχ hB g⟫_ℝ := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedMulLp_ae hχ hB f,boundedMulLp_ae hχ hB g] with x hf hg
  simp only [hf,hg,Real.inner_apply]
  ring

lemma RCD.compact_core_localized_pairing_oai {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (f : Lp ℝ 2 m)
    (hof : ∀ g,IsTestFunction m g → HasCompactSupport g → ∀ u A : Lp ℝ 2 m,
      g =ᵐ[m] u → laplacian m g =ᵐ[m] A → ⟪f,u-A⟫_ℝ = 0)
    {χ : X → ℝ} (hχ : IsTestFunction m χ) (hχc : HasCompactSupport χ)
    {D : ℝ} (hD : ∀ᵐ x ∂m,|laplacian m χ x| ≤ D)
    {B : ℝ} (hB : ∀ x,|χ x| ≤ B) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ g,IsTestFunction m g → ∀ u A : Lp ℝ 2 m,
      g =ᵐ[m] u → laplacian m g =ᵐ[m] A →
      |⟪boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hB) f,A⟫_ℝ|
        ≤ C*(‖u‖+Real.sqrt (2*(cheegerEnergy m (u : X → ℝ)).toReal)) := by
  have hpar := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  let M := boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hB)
  let T := boundedMulLp (laplacian_isLaplacian hχ.1).2.1.aestronglyMeasurable hD
  let L := hχ.2.2.1.choose
  have hL : LipschitzWith L χ := hχ.2.2.1.choose_spec
  refine ⟨‖f‖*(‖M‖+‖T‖+2*(L:ℝ)),by positivity,?_⟩
  intro g hg u A hgu hgA
  have hgS := (laplacian_isLaplacian hg.1).1
  let G := (memLp_gamma_of_lipschitz hfin hpar hL hgS).toLp (gamma m χ g)
  have hG := (memLp_gamma_of_lipschitz hfin hpar hL hgS).coeFn_toLp
  have hP := hrcd.test_mul hN hfull hfin o hχ hg
  have hPc : HasCompactSupport (fun x => χ x*g x) := hχc.mul_right
  have hpe : (fun x => χ x*g x) =ᵐ[m] M u := by
    filter_upwards [hgu,boundedMulLp_ae _ (ae_of_all m hB) u] with x hu hp
    rw [hp,hu,mul_comm]
  have hgen := (laplacian_isLaplacian hχ.1).mul_lipschitz hfin hpar
    (laplacian_isLaplacian hg.1) hL hg.2.2.1.choose_spec hB hg.2.1.choose_spec
  have hAe : laplacian m (fun x => χ x*g x) =ᵐ[m] (T u+M A+(2:ℝ) • G : Lp ℝ 2 m) := by
    apply (hgen.ae_laplacian hfin).trans
    filter_upwards [hgu,hgA,boundedMulLp_ae _ hD u,boundedMulLp_ae _ (ae_of_all m hB) A,
      Lp.coeFn_add (T u) (M A),Lp.coeFn_add (T u+M A) ((2:ℝ) • G),Lp.coeFn_smul (2:ℝ) G,hG]
      with x hu hA ht hm h1 h2 h3 hgam
    change (T u) x = u x*laplacian m χ x at ht
    change (M A) x = A x*χ x at hm
    change G x = gamma m χ g x at hgam
    simp only [h2,Pi.add_apply,h1,h3,Pi.smul_apply,smul_eq_mul,hgam,ht,hm]
    rw [hu,hA]
    ring
  have hh := hof _ hP hPc (M u) (T u+M A+(2:ℝ) • G) hpe hAe
  have he : ⟪M f,A⟫_ℝ = ⟪f,M u-T u-(2:ℝ) • G⟫_ℝ := by
    rw [boundedMulLp_inner_swap]
    simp only [inner_sub_right,inner_add_right,real_inner_smul_right] at hh ⊢
    linarith only [hh]
  have hgSn : Sobolev m (u : X → ℝ) := (sobolev_congr_ae hgu).mp hgS
  have hDge : ‖hgS.2.2.toLp (weakGradient m g)‖ =
      Real.sqrt (2*(cheegerEnergy m (u : X → ℝ)).toReal) := by
    rw [cheegerEnergy_congr_ae hgu.symm,hrcd.1.global_cheegerEnergy_toReal hfin o hrcd.2 hgS]
    have hid := norm_toLp_sq_eq_integral hgS.2.2
    rw [show 2*((∫ x,(weakGradient m g x)^2 ∂m)/2) = ∫ x,(weakGradient m g x)^2 ∂m by ring,← hid,
      Real.sqrt_sq (norm_nonneg _)]
  have hGn : ‖G‖ ≤ (L:ℝ)*Real.sqrt (2*(cheegerEnergy m (u : X → ℝ)).toReal) := by
    rw [← hDge]
    exact norm_gamma_toLp_le hfin hpar hL hgS
  rw [he]
  apply (abs_real_inner_le_norm _ _).trans
  have hn := (norm_sub_le (M u-T u) ((2:ℝ) • G)).trans
    (add_le_add (norm_sub_le (M u) (T u)) le_rfl)
  norm_num only [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ) < 2)] at hn
  have hmu := M.le_opNorm u
  have htu := T.le_opNorm u
  have hn' : ‖M u-T u-(2:ℝ) • G‖ ≤
      (‖M‖+‖T‖)*‖u‖+2*(L:ℝ)*Real.sqrt (2*(cheegerEnergy m (u : X → ℝ)).toReal) := by
    nlinarith only [hn,hmu,htu,hGn]
  apply (mul_le_mul_of_nonneg_left hn' (norm_nonneg f)).trans
  have hs := Real.sqrt_nonneg (2*(cheegerEnergy m (u : X → ℝ)).toReal)
  have ha := mul_nonneg (norm_nonneg M) hs
  have hb := mul_nonneg (norm_nonneg T) hs
  have hc := mul_nonneg (NNReal.coe_nonneg L) (norm_nonneg u)
  calc
    _ ≤ ‖f‖*((‖M‖+‖T‖+2*(L:ℝ))*(‖u‖+Real.sqrt (2*(cheegerEnergy m (u : X → ℝ)).toReal))) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg f)
      nlinarith only [ha,hb,hc]
    _ = _ := by ring
end WeakHessian

end
end InlinedFile159

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakHessian.RCD.compact_core_localized_pairing_oai.{u_1} := @OAI.WeakHessian.RCD.compact_core_localized_pairing_oai.{u_1}
