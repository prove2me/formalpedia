-- Prove2me | solution 1 for OAI.YauCounterexamples.three_rank_separating_tensor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:50:23.287881+00:00
-- url     : https://prove2.me/submissions/fff2db56-e539-400f-b0fa-3ad1c5baffaf

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A005
import Definitions.Def_OAIQ070A006
import Definitions.Def_OAIQ070A007
import Definitions.Def_OAIQ070A008
import Theorems.Thm_OAI_YauCounterexamples_exists_supported_separating_tensor
import Theorems.Thm_OAI_YauCounterexamples_proportional_eigen_global

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RectangularFactorization
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology
namespace YauCounterexamples
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem rectangular_factorization {I : Set ℝ} {J : Set W}
    (hIo : IsOpen I) (hJo : IsOpen J) (hJc : IsPreconnected J)
    {w₀ : W} (hw₀ : w₀ ∈ J) (V : ℝ × W → ℝ)
    (hV : ContDiffOn ℝ 2 V (I ×ˢ J))
    (hvert : ∀ s ∈ I, ∀ w ∈ J, ∀ v : W,
      fderiv ℝ V (s,w) (0,v) = 0) :
    ∃ F : ℝ → ℝ, ContDiffOn ℝ 2 F I ∧
      ∀ s ∈ I, ∀ w ∈ J, V (s,w) = F s := by
  let F : ℝ → ℝ := fun s => V (s,w₀)
  refine ⟨F, ?_, ?_⟩
  · exact hV.comp (contDiffOn_id.prodMk contDiffOn_const) (fun s hs => ⟨hs,hw₀⟩)
  intro s hs w hw
  have hd (w : W) (hw : w ∈ J) : DifferentiableAt ℝ V (s,w) :=
    (hV.differentiableOn (by norm_num)).differentiableAt
      ((hIo.prod hJo).mem_nhds ⟨hs,hw⟩)
  have hslice : DifferentiableOn ℝ (fun w : W => V (s,w)) J := by
    intro w hw
    exact ((hd w hw).comp w ((differentiableAt_const s).prodMk differentiableAt_id)).differentiableWithinAt
  have hz : EqOn (fderiv ℝ (fun w : W => V (s,w))) 0 J := by
    intro w hw
    change fderiv ℝ (V ∘ (fun w : W => (s,w))) w = 0
    rw [fderiv_comp w (hd w hw) ((differentiableAt_const s).prodMk differentiableAt_id)]
    ext v
    simpa [(hasFDerivAt_prodMk_right (𝕜:=ℝ) s w).fderiv] using hvert s hs w hw v
  exact hJo.is_const_of_fderiv_eq_zero hJc hslice hz hw hw₀
open Filter Function Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem local_factor_of_kernel {f g : E → ℝ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U)
    (hd : fderiv ℝ f x ≠ 0)
    (hker : ∀ y ∈ U, ∀ v : E, fderiv ℝ f y v = 0 → fderiv ℝ g y v = 0) :
    ∃ (V : Set E) (I : Set ℝ) (F : ℝ → ℝ), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      IsOpen I ∧ IsPreconnected I ∧ f x ∈ I ∧ ContDiffOn ℝ 2 F I ∧
      MapsTo f V I ∧ EqOn g (F ∘ f) V := by
  let L := fderiv ℝ f x
  have hL : L.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    apply surjective_of_nonzero_of_finrank_eq_one (K := ℝ) (f := L.toLinearMap) (by simp)
    intro hh
    apply hd
    ext y
    exact DFunLike.congr_fun hh y
  have hfx := (hf x hx).contDiffAt (hU.mem_nhds hx)
  have hs : HasStrictFDerivAt f L x := hfx.hasStrictFDerivAt (by norm_num)
  have hLc : L.ker.ClosedComplemented := L.ker_closedComplemented_of_finiteDimensional_range
  let φ := hs.implicitFunctionDataOfComplemented f L hL hLc
  let e := φ.toOpenPartialHomeomorph
  have hex : x ∈ e.source := φ.pt_mem_toOpenPartialHomeomorph_source
  have hefx (y : E) : (e y).1 = f y := rfl
  have he0 : e x = (f x,0) := by simp [e,φ,ImplicitFunctionData.prodFun]
  have hext : (f x, (0 : L.ker)) ∈ e.target := he0 ▸ e.map_source hex
  have heix : e.symm (f x,0) = x := by rw [←he0]; exact e.left_inv hex
  have hr : ContDiffAt ℝ 2 φ.rightFun φ.pt := by
    exact ((Classical.choose hLc).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hi := φ.contDiffAt_implicitFunction hfx hr (by norm_num)
  change ContDiffAt ℝ 2 e.symm (e x) at hi
  rw [he0] at hi
  have hpre : e.symm ⁻¹' U ∈ 𝓝 (f x,(0:L.ker)) := by
    apply (e.continuousAt_symm hext).tendsto
    rw [heix]
    exact hU.mem_nhds hx
  obtain ⟨r,hrpos,hrsub⟩ := Metric.mem_nhds_iff.mp
    (((hi.eventually (by norm_num)).and (e.open_target.mem_nhds hext)).and hpre)
  let I := ball (f x) r
  let J : Set L.ker := ball 0 r
  let B := I ×ˢ J
  have hBo : IsOpen B := isOpen_ball.prod isOpen_ball
  have hBsub (y : ℝ × L.ker) (hy : y ∈ B) :
      ContDiffAt ℝ 2 e.symm y ∧ y ∈ e.target ∧ e.symm y ∈ U := by
    have hy' : y ∈ ball (f x,(0:L.ker)) r := by
      rw [←ball_prod_same]; exact hy
    have hh := hrsub hy'
    exact ⟨hh.1.1,hh.1.2,hh.2⟩
  let G := g ∘ e.symm
  have hG : ContDiffOn ℝ 2 G B := by
    intro y hy
    exact (((hg _ (hBsub y hy).2.2).contDiffAt (hU.mem_nhds (hBsub y hy).2.2)).comp y
      (hBsub y hy).1).contDiffWithinAt
  have hvertical : ∀ s ∈ I, ∀ w ∈ J, ∀ v : L.ker,
      fderiv ℝ G (s,w) (0,v) = 0 := by
    intro s hs w hw v
    let y : ℝ × L.ker := (s,w)
    have hy : y ∈ B := ⟨hs,hw⟩
    have hyU := (hBsub y hy).2.2
    have hdi := (hBsub y hy).1.differentiableAt (by norm_num)
    have hdf := ((hf _ hyU).contDiffAt (hU.mem_nhds hyU)).differentiableAt (by norm_num)
    have hdg := ((hg _ hyU).contDiffAt (hU.mem_nhds hyU)).differentiableAt (by norm_num)
    have heq : f ∘ e.symm =ᶠ[𝓝 y] Prod.fst := by
      filter_upwards [e.open_target.mem_nhds (hBsub y hy).2.1] with z hz
      exact congrArg Prod.fst (e.right_inv hz)
    have hff : fderiv ℝ f (e.symm y) (fderiv ℝ e.symm y (0,v)) = 0 := by
      have hh := heq.fderiv_eq (𝕜:=ℝ)
      rw [fderiv_comp y hdf hdi] at hh
      rw [fderiv_fst] at hh
      exact congrArg (fun A : (ℝ × L.ker) →L[ℝ] ℝ => A (0,v)) hh
    change fderiv ℝ (g ∘ e.symm) y (0,v) = 0
    rw [fderiv_comp y hdg hdi]
    exact hker _ hyU _ hff
  obtain ⟨F,hF,hGF⟩ := rectangular_factorization (I:=I) (J:=J) isOpen_ball isOpen_ball
    (convex_ball (0:L.ker) r).isPreconnected (mem_ball_self hrpos) G hG hvertical
  let V := e.source ∩ e ⁻¹' B
  have hVo : IsOpen V := e.continuousOn.isOpen_inter_preimage e.open_source hBo
  have hxV : x ∈ V := ⟨hex,by change e x ∈ B; rw [he0]; exact ⟨mem_ball_self hrpos,mem_ball_self hrpos⟩⟩
  have hVU : V ⊆ U := by
    intro y hy
    have hh := (hBsub (e y) hy.2).2.2
    rwa [e.left_inv hy.1] at hh
  refine ⟨V,I,F,hVo,hxV,hVU,isOpen_ball,(convex_ball (f x) r).isPreconnected,
    mem_ball_self hrpos,hF,?_,?_⟩
  · intro y hy
    exact hy.2.1
  · intro y hy
    have hh := hGF (e y).1 hy.2.1 (e y).2 hy.2.2
    change g (e.symm (e y)) = F (f y) at hh
    rwa [e.left_inv hy.1] at hh
end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ScalarCompDirectional
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
section ProductCalculus
variable {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [RCLike 𝕜]
lemma second_fderiv_mul_at {u v : E → 𝕜} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) (a b : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => u z * v z) y b) x a =
      u x * fderiv ℝ (fun y => fderiv ℝ v y b) x a +
      v x * fderiv ℝ (fun y => fderiv ℝ u y b) x a +
      fderiv ℝ u x a * fderiv ℝ v x b +
      fderiv ℝ u x b * fderiv ℝ v x a := by
  have hdu := hu.differentiableAt (by norm_num)
  have hdv := hv.differentiableAt (by norm_num)
  have hdu' : DifferentiableAt ℝ (fun y => fderiv ℝ u y b) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const b)
  have hdv' : DifferentiableAt ℝ (fun y => fderiv ℝ v y b) x :=
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const b)
  have he : (fun y => fderiv ℝ (fun z => u z * v z) y b) =ᶠ[𝓝 x]
      (fun y => u y * fderiv ℝ v y b + v y * fderiv ℝ u y b) := by
    filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)] with y hy hz
    rw [fderiv_fun_mul (hy.differentiableAt (by norm_num)) (hz.differentiableAt (by norm_num))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [he.fderiv_eq]
  erw [fderiv_fun_add (hdu.mul hdv') (hdv.mul hdu'),
    fderiv_fun_mul hdu hdv', fderiv_fun_mul hdv hdu']
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring
end ProductCalculus
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma laplaceBeltrami_mul {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) (g : SmoothMetric E M) (x : M) :
    laplaceBeltrami g (fun y => u y * v y) x =
      u x * laplaceBeltrami g v x + v x * laplaceBeltrami g u x +
        2 * coordinateGradientPair g u v x := by
  let c := chartAt E x
  let b := Module.finBasis ℝ E
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hinv : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  have hu' := contDiffAt_inChart_C2 hu x hx
  have hv' := contDiffAt_inChart_C2 hv x hx
  change localLaplacian g _ x (c x) = _
  have huv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (fun y => u y * v y) := hu.mul hv
  rw [localLaplacian_expansion_C2 huv g x hx]
  change _ = u x * localLaplacian g v x (c x) +
    v x * localLaplacian g u x (c x) + 2 * coordinateGradientPair g u v x
  rw [localLaplacian_expansion_C2 hu g x hx, localLaplacian_expansion_C2 hv g x hx]
  have hs (i j : CoordIndex E) : (metricCoefficients g x (c x))⁻¹ j i =
      (metricCoefficients g x (c x))⁻¹ i j := by
    have h := congrArg (fun A : Matrix (CoordIndex E) (CoordIndex E) ℝ => A i j)
      (metricCoefficients_posDef g x hx).inv.isHermitian.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have hcross : (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
      fderiv ℝ (u ∘ c.symm) (c x) (b j) * fderiv ℝ (v ∘ c.symm) (c x) (b i)) =
      coordinateGradientPair g u v x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs]
  change (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
      fderiv ℝ (fun y => fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z) y (b j)) (c x) (b i)) +
      ∑ j, metricFirstCoefficient g x j (c x) *
        fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z) (c x) (b j) = _
  have hd1 (j : CoordIndex E) :
      fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z) (c x) (b j) =
        u x * fderiv ℝ (v ∘ c.symm) (c x) (b j) +
        v x * fderiv ℝ (u ∘ c.symm) (c x) (b j) := by
    erw [fderiv_fun_mul (hu'.differentiableAt (by norm_num))
      (hv'.differentiableAt (by norm_num))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, Function.comp_apply]
    dsimp only [c] at hinv ⊢
    rw [hinv]
  have hd2 (i j : CoordIndex E) :
      fderiv ℝ (fun y => fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z)
        y (b j)) (c x) (b i) =
      u x * fderiv ℝ (fun y => fderiv ℝ (v ∘ c.symm) y (b j)) (c x) (b i) +
      v x * fderiv ℝ (fun y => fderiv ℝ (u ∘ c.symm) y (b j)) (c x) (b i) +
      fderiv ℝ (u ∘ c.symm) (c x) (b i) * fderiv ℝ (v ∘ c.symm) (c x) (b j) +
      fderiv ℝ (u ∘ c.symm) (c x) (b j) * fderiv ℝ (v ∘ c.symm) (c x) (b i) := by
    have he := second_fderiv_mul_at hu' hv' (b i) (b j)
    dsimp only [c] at hinv he ⊢
    simpa only [Function.comp_apply, hinv] using he
  simp_rw [hd2, hd1]
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [← mul_assoc, hcross]
  unfold coordinateGradientPair
  dsimp only [c, b]
  simp only [← Finset.mul_sum, mul_assoc, mul_left_comm]
  ring


end

open Set Filter Manifold
open scoped Topology ContDiff
section ScalarComposition
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma scalar_comp_directional {F : ℝ → ℝ} {u : E → ℝ} {x : E}
    (hF : DifferentiableAt ℝ F (u x)) (hu : DifferentiableAt ℝ u x) (v : E) :
    fderiv ℝ (F ∘ u) x v = deriv F (u x) * fderiv ℝ u x v := by
  rw [fderiv_comp x hF hu, ContinuousLinearMap.comp_apply]
  exact fderiv_eq_deriv_mul
lemma scalar_comp_second_directional {F : ℝ → ℝ} {u : E → ℝ} {x : E}
    (hF : ContDiffAt ℝ 2 F (u x)) (hu : ContDiffAt ℝ 2 u x) (a b : E) :
    fderiv ℝ (fun y => fderiv ℝ (F ∘ u) y b) x a =
      deriv (deriv F) (u x) * fderiv ℝ u x a * fderiv ℝ u x b +
      deriv F (u x) * fderiv ℝ (fun y => fderiv ℝ u y b) x a := by
  have hdu := hu.differentiableAt (by norm_num)
  have hF' : DifferentiableAt ℝ (deriv F) (u x) :=
    by
      simpa only [fderiv_apply_one_eq_deriv] using
        ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
          (differentiableAt_const (1 : ℝ))
  have hdu' : DifferentiableAt ℝ (fun y => fderiv ℝ u y b) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const b)
  have he : (fun y => fderiv ℝ (F ∘ u) y b) =ᶠ[𝓝 x]
      (fun y => deriv F (u y) * fderiv ℝ u y b) := by
    filter_upwards [hu.eventually (by norm_num),
      (hdu.continuousAt.preimage_mem_nhds (hF.eventually (by norm_num)))] with y hy hFy
    change ContDiffAt ℝ 2 F (u y) at hFy
    exact scalar_comp_directional (hFy.differentiableAt (by norm_num))
      (hy.differentiableAt (by norm_num)) b
  rw [he.fderiv_eq]
  erw [fderiv_fun_mul (hF'.comp x hdu) hdu']
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  have hfder := scalar_comp_directional hF' hdu a
  change fderiv ℝ (deriv F ∘ u) x a = _ at hfder
  rw [hfder]
  simp only [Function.comp_apply]
  ring
end ScalarComposition
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
lemma localLaplacian_expansion_at {u : M → ℝ}
    (g : SmoothMetric E M) (p : M) {y : E} (hy : y ∈ (chartAt E p).target)
    (hu : ContDiffAt ℝ 2 (u ∘ (chartAt E p).symm) y) :
    localLaplacian g u p y =
      (∑ i, ∑ j, (metricCoefficients g p y)⁻¹ i j *
        fderiv ℝ (fun z => fderiv ℝ (u ∘ (chartAt E p).symm) z (Module.finBasis ℝ E j)) y
          (Module.finBasis ℝ E i)) +
      ∑ j, metricFirstCoefficient g p j y *
        fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j) := by
  classical
  let ρ := fun z => Real.sqrt (metricCoefficients g p z).det
  let A := metricCoefficients g p
  let v := u ∘ (chartAt E p).symm
  let b := Module.finBasis ℝ E
  have hρ : DifferentiableAt ℝ ρ y := ((contDiffOn_metricDensity g p).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hA (i j : CoordIndex E) : DifferentiableAt ℝ (fun z => (A z)⁻¹ i j) y :=
    ((contDiffOn_metricInverse g p i j).contDiffAt
      ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hv : DifferentiableAt ℝ (fderiv ℝ v) y :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he (i : CoordIndex E) : (fun z => metricFlux g u p z i) =
      fun z => ∑ j, (ρ z * (A z)⁻¹ i j) * fderiv ℝ v z (b j) := by
    funext z
    simp only [metricFlux, ρ, A, v, b, Finset.mul_sum, mul_assoc]
  have hder (i : CoordIndex E) : fderiv ℝ (fun z => metricFlux g u p z i) y (b i) =
      ∑ j, ((ρ y * (A y)⁻¹ i j) * fderiv ℝ (fun z => fderiv ℝ v z (b j)) y (b i) +
        fderiv ℝ v y (b j) * fderiv ℝ (fun z => ρ z * (A z)⁻¹ i j) y (b i)) := by
    rw [he]
    erw [fderiv_fun_sum (u := Finset.univ)
      (A := fun j z => (ρ z * (A z)⁻¹ i j) * fderiv ℝ v z (b j))
      (fun j _ => (hρ.mul (hA i j)).mul (hv.clm_apply (differentiableAt_const _)))]
    simp only [_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    erw [fderiv_mul (c := fun z => ρ z * (A z)⁻¹ i j)
      (d := fun z => fderiv ℝ v z (b j)) (hρ.mul (hA i j))
      (hv.clm_apply (differentiableAt_const _))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  change (ρ y)⁻¹ * ∑ i, fderiv ℝ (fun z => metricFlux g u p z i) y (b i) = _
  simp_rw [hder, Finset.sum_add_distrib]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  have hn : ρ y ≠ 0 := (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  have hmain : (∑ i, (ρ y)⁻¹ * ∑ j, ρ y * (A y)⁻¹ i j *
      fderiv ℝ (fun z => fderiv ℝ v z (b j)) y (b i)) =
      ∑ i, ∑ j, (A y)⁻¹ i j * fderiv ℝ (fun z => fderiv ℝ v z (b j)) y (b i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [hmain]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [metricFirstCoefficient, ρ, A, b, v, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem laplaceBeltrami_comp_at {F : ℝ → ℝ} {u : M → ℝ}
    (g : SmoothMetric E M) (x : M) (hF : ContDiffAt ℝ 2 F (u x))
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 u) :
    laplaceBeltrami g (F ∘ u) x = deriv F (u x) * laplaceBeltrami g u x +
      deriv (deriv F) (u x) * coordinateGradientPair g u u x := by
  let c := chartAt E x
  let b := Module.finBasis ℝ E
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hinv : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  have hu' := contDiffAt_inChart_C2 hu x hx
  have hF' : ContDiffAt ℝ 2 F ((u ∘ c.symm) (c x)) := by
    simpa only [Function.comp_apply,hinv] using hF
  have hFu : ContDiffAt ℝ 2 ((F ∘ u) ∘ c.symm) (c x) := hF'.comp (c x) hu'
  change localLaplacian g (F ∘ u) x (c x) =
    deriv F (u x) * localLaplacian g u x (c x) +
      deriv (deriv F) (u x) * coordinateGradientPair g u u x
  rw [localLaplacian_expansion_at g x hx hFu, localLaplacian_expansion_C2 hu g x hx]
  have hd1 (i : CoordIndex E) :
      fderiv ℝ ((F ∘ u) ∘ c.symm) (c x) (b i) =
      deriv F (u x) * fderiv ℝ (u ∘ c.symm) (c x) (b i) := by
    change fderiv ℝ (F ∘ (u ∘ c.symm)) (c x) (b i) = _
    rw [scalar_comp_directional (hF'.differentiableAt (by norm_num))
      (hu'.differentiableAt (by norm_num)), Function.comp_apply, hinv]
  have hd2 (i j : CoordIndex E) :
      fderiv ℝ (fun z => fderiv ℝ ((F ∘ u) ∘ c.symm) z (b j)) (c x) (b i) =
      deriv (deriv F) (u x) * fderiv ℝ (u ∘ c.symm) (c x) (b i) *
        fderiv ℝ (u ∘ c.symm) (c x) (b j) +
      deriv F (u x) * fderiv ℝ (fun z => fderiv ℝ (u ∘ c.symm) z (b j)) (c x) (b i) := by
    change fderiv ℝ (fun z => fderiv ℝ (F ∘ (u ∘ c.symm)) z (b j)) (c x) (b i) = _
    rw [scalar_comp_second_directional hF' hu', Function.comp_apply,hinv]
  change (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
      fderiv ℝ (fun z => fderiv ℝ ((F ∘ u) ∘ c.symm) z (b j)) (c x) (b i)) +
      ∑ j, metricFirstCoefficient g x j (c x) * fderiv ℝ ((F ∘ u) ∘ c.symm) (c x) (b j) = _
  simp_rw [hd1,hd2,mul_add,Finset.sum_add_distrib]
  unfold coordinateGradientPair
  simp only [Finset.mul_sum]
  simp only [mul_left_comm,mul_comm]
  ring



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_JointLocalLaplacian
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contDiffAt_metricFlux {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) (i : CoordIndex E) :
    ContDiffAt ℝ ∞ (fun z => metricFlux g u p z i) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  apply hd.mul
  apply ContDiffAt.sum
  intro j _
  have ha := (contDiffOn_metricInverse g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hv := (contDiffAt_inChart hu p hy).fderiv_right (m := ∞) (by simp)
  exact ha.mul (hv.clm_apply contDiffAt_const)

lemma contDiffAt_localLaplacian {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (localLaplacian g u p) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hn : Real.sqrt (metricCoefficients g p y).det ≠ 0 :=
    (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  apply (hd.inv hn).mul
  apply ContDiffAt.sum
  intro i _
  exact ((contDiffAt_metricFlux hu g p hy i).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

lemma contMDiff_laplaceBeltrami {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (laplaceBeltrami g u) := by
  intro x
  rw [contMDiffAt_iff_source]
  simp only [mfld_simps, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  have hx := (chartAt E x).map_source (mem_chart_source E x)
  apply (contDiffAt_localLaplacian hu g x hx).congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_target.mem_nhds hx] with y hy
  have he := laplaceBeltrami_inChart hu g x ((chartAt E x).symm y) ((chartAt E x).map_target hy)
  simpa only [Function.comp_apply, (chartAt E x).right_inv hy] using he

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RoundMetricExists
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contMDiff_coordinateGradientPair {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (coordinateGradientPair g u v) := by
  have he : coordinateGradientPair g u v = fun x => (2 : ℝ)⁻¹ *
      (laplaceBeltrami g (fun y => u y * v y) x -
        u x * laplaceBeltrami g v x - v x * laplaceBeltrami g u x) := by
    funext x
    rw [laplaceBeltrami_mul (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (hv.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
    ring
  rw [he]
  exact contMDiff_const.mul (((contMDiff_laplaceBeltrami (hu.mul hv) g).sub
    (hu.mul (contMDiff_laplaceBeltrami hv g))).sub (hv.mul (contMDiff_laplaceBeltrami hu g)))

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma localGradientPair_eq_global {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    localGradientPair g u u p y = coordinateGradientPair g u u ((chartAt E p).symm y) := by
  rw [coordinateGradientPair_inChart hu hu g p ((chartAt E p).symm y) ((chartAt E p).map_target hy),
    (chartAt E p).right_inv hy]


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_PinningFactorGradient
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma laplaceBeltrami_congr_nhds (g : SmoothMetric E M) {u v : M → ℝ} {x : M}
    (hu : u =ᶠ[𝓝 x] v) : laplaceBeltrami g u x=laplaceBeltrami g v x := by
  let c := chartAt E x
  have hx := c.map_source (mem_chart_source E x)
  have ht : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
    simpa only [c.left_inv (mem_chart_source E x)] using (c.continuousAt_symm hx).tendsto
  have hu' := (hu.comp_tendsto ht).fderiv (𝕜:=ℝ)
  have he (i : CoordIndex E) :
      (fun y => Real.sqrt (metricCoefficients g x y).det * ∑ j,
        (metricCoefficients g x y)⁻¹ i j * fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j))
      =ᶠ[𝓝 (c x)]
      (fun y => Real.sqrt (metricCoefficients g x y).det * ∑ j,
        (metricCoefficients g x y)⁻¹ i j * fderiv ℝ (v ∘ c.symm) y (Module.finBasis ℝ E j)) := by
    filter_upwards [hu'] with y hy
    rw [hy]
  unfold laplaceBeltrami
  change (Real.sqrt (metricCoefficients g x (c x)).det)⁻¹ * ∑ i, _ = _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun T : E →L[ℝ] ℝ => T (Module.finBasis ℝ E i)) (he i).fderiv_eq


end



section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma chart_germ_of_pullback {u v : M → ℝ} (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target)
    (he : (u ∘ (chartAt E p).symm) =ᶠ[𝓝 y] (v ∘ (chartAt E p).symm)) :
    u =ᶠ[𝓝 ((chartAt E p).symm y)] v := by
  let c := chartAt E p
  have hs : c.symm y ∈ c.source := c.map_target hy
  have ht : Tendsto c (𝓝 (c.symm y)) (𝓝 y) := by
    simpa only [c.right_inv hy] using (c.continuousAt hs).tendsto
  filter_upwards [he.comp_tendsto ht,c.open_source.mem_nhds hs] with z hz hzs
  change u (c.symm (c z)) = v (c.symm (c z)) at hz
  simpa only [c.left_inv hzs] using hz


end

open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma pinning_factor_gradient (F : ℝ → ℝ) {I : Set ℝ} (hIo : IsOpen I)
    (hIc : IsPreconnected I) (hF : ContDiffOn ℝ 2 F I)
    {Λ : ℝ} (hΛ : 0<Λ) {r₀ r₁ : ℝ} (hr : r₀ < r₁)
    (he : ∀ s ∈ I, ∀ r ∈ ({r₀,r₁}:Set ℝ),
      deriv (deriv F) s*r + Λ*(F s-s*deriv F s)=0) :
    ∃ c : ℝ, ∀ s ∈ I, F s=c*s := by
  have hsecond (s : ℝ) (hs : s∈I) : deriv (deriv F) s=0 := by
    have h0 := he s hs r₀ (by simp)
    have h1 := he s hs r₁ (by simp)
    have hz : (r₁-r₀)*deriv (deriv F) s=0 := by nlinarith [h0,h1]
    exact (mul_eq_zero.mp hz).resolve_left (sub_pos.mpr hr).ne'
  have hd : DifferentiableOn ℝ (deriv F) I :=
    (hF.deriv_of_isOpen (m:=1) hIo (by norm_num)).differentiableOn (by norm_num)
  obtain ⟨c,hc⟩ := hIo.exists_is_const_of_deriv_eq_zero hIc hd hsecond
  refine ⟨c,fun s hs => ?_⟩
  have h0 := he s hs r₀ (by simp)
  rw [hsecond s hs,hc s hs] at h0
  have hz : F s-s*c=0 := (mul_eq_zero.mp (by simpa using h0)).resolve_left hΛ.ne'
  linarith
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem local_eigen_proportional_of_gradient_rank
    (g : SmoothMetric E M) {u v R : M → ℝ} (p : M) {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hUt : U ⊆ (chartAt E p).target)
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 v)
    (hdu : fderiv ℝ (u ∘ (chartAt E p).symm) x ≠ 0)
    (hker : ∀ y ∈ U, ∀ w, fderiv ℝ (u ∘ (chartAt E p).symm) y w = 0 →
      fderiv ℝ (v ∘ (chartAt E p).symm) y w = 0)
    (hpair : ContDiffAt ℝ 1 (fun y => (u ((chartAt E p).symm y), R ((chartAt E p).symm y))) x)
    (hrank : Function.Surjective (fderiv ℝ
      (fun y => (u ((chartAt E p).symm y), R ((chartAt E p).symm y))) x))
    (hR : 0 < R ((chartAt E p).symm x)) {Λ : ℝ} (hΛ : 0 < Λ)
    (hue : ∀ y ∈ U, laplaceBeltrami g u ((chartAt E p).symm y) =
      -Λ * u ((chartAt E p).symm y))
    (hve : ∀ y ∈ U, laplaceBeltrami g v ((chartAt E p).symm y) =
      -Λ * v ((chartAt E p).symm y))
    (hquad : ∀ y ∈ U, coordinateGradientPair g u u ((chartAt E p).symm y) =
      R ((chartAt E p).symm y)) :
    ∃ c : ℝ, v =ᶠ[𝓝 ((chartAt E p).symm x)] (fun y => c*u y) := by
  let chart := chartAt E p
  let f := u ∘ chart.symm
  let h := v ∘ chart.symm
  let H : E → ℝ × ℝ := fun y => (f y, R (chart.symm y))
  have hf : ContDiffOn ℝ 2 f U := fun y hy =>
    (contDiffAt_inChart_C2 hu p (hUt hy)).contDiffWithinAt
  have hh : ContDiffOn ℝ 2 h U := fun y hy =>
    (contDiffAt_inChart_C2 hv p (hUt hy)).contDiffWithinAt
  obtain ⟨V,I,F,hVo,hxV,hVU,hIo,hIc,hfxI,hF,hfV,hVF⟩ :=
    local_factor_of_kernel hU hx hf hh hdu hker
  have hlocal (y : E) (hy : y ∈ V) :
      v =ᶠ[𝓝 (chart.symm y)] (F ∘ u) := by
    apply chart_germ_of_pullback p (hUt (hVU hy))
    filter_upwards [hVo.mem_nhds hy] with z hz
    exact hVF hz
  have hPDE (y : E) (hy : y ∈ V) :
      deriv (deriv F) (f y) * R (chart.symm y) +
      Λ * (F (f y) - f y * deriv F (f y)) = 0 := by
    have hcomp := laplaceBeltrami_comp_at g (chart.symm y)
      ((hF _ (hfV hy)).contDiffAt (hIo.mem_nhds (hfV hy))) hu
    rw [← laplaceBeltrami_congr_nhds g (hlocal y hy),hue y (hVU hy),hve y (hVU hy),hquad y (hVU hy)] at hcomp
    have hval : v (chart.symm y) = F (f y) := hVF hy
    rw [hval] at hcomp
    change -Λ*F (f y) =
      deriv F (f y) * (-Λ*f y) +
      deriv (deriv F) (f y) * R (chart.symm y) at hcomp
    linear_combination -hcomp
  have hmap : Filter.map H (𝓝 x) = 𝓝 (H x) :=
    (hpair.hasStrictFDerivAt one_ne_zero).map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hrank)
  have himage : H '' V ∈ 𝓝 (H x) := by
    rw [←hmap]
    exact Filter.image_mem_map (hVo.mem_nhds hxV)
  have hbox : I ×ˢ Ioi (0:ℝ) ∈ 𝓝 (H x) :=
    (hIo.prod isOpen_Ioi).mem_nhds ⟨hfxI,hR⟩
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp (inter_mem himage hbox)
  let K := ball (f x) ε
  let r₀ := R (chart.symm x) - ε/2
  let r₁ := R (chart.symm x) + ε/2
  have hr₀B : r₀ ∈ ball (R (chart.symm x)) ε := by
    rw [mem_ball,Real.dist_eq,abs_lt]; dsimp [r₀]; constructor <;> linarith
  have hr₁B : r₁ ∈ ball (R (chart.symm x)) ε := by
    rw [mem_ball,Real.dist_eq,abs_lt]; dsimp [r₁]; constructor <;> linarith
  have hpairmem (s : ℝ) (hs : s ∈ K) (r : ℝ) (hr : r ∈ ({r₀,r₁}:Set ℝ)) :
      (s,r) ∈ H '' V ∩ (I ×ˢ Ioi (0:ℝ)) := by
    apply hεsub
    change (s,r) ∈ ball (f x,R (chart.symm x)) ε
    rw [←ball_prod_same]
    refine ⟨hs,?_⟩
    simp only [mem_insert_iff,mem_singleton_iff] at hr
    rcases hr with rfl | rfl <;> assumption
  have hKI : K ⊆ I := fun s hs => (hpairmem s hs r₀ (by simp)).2.1
  have hrr : r₀ < r₁ := by dsimp [r₀,r₁]; linarith
  obtain ⟨a,ha⟩ := pinning_factor_gradient F isOpen_ball (convex_ball (f x) ε).isPreconnected
    (hF.mono hKI) hΛ hrr (fun s hs r hr => by
      obtain ⟨y,hy,hyr⟩ := (hpairmem s hs r hr).1
      have hs' : f y = s := congrArg Prod.fst hyr
      have hr' : R (chart.symm y) = r := congrArg Prod.snd hyr
      simpa only [hs',hr'] using hPDE y hy)
  refine ⟨a,chart_germ_of_pullback p (hUt hx) ?_⟩
  have hnx : f ⁻¹' K ∈ 𝓝 x :=
    ((hf x hx).contDiffAt (hU.mem_nhds hx)).continuousAt (isOpen_ball.mem_nhds (mem_ball_self hε))
  filter_upwards [hVo.mem_nhds hxV,hnx] with y hy hyK
  exact (hVF hy).trans (ha (f y) hyK)

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_TransverseZeroKernel
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace YauCounterexamples

open Set Filter Function Manifold
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma transverse_zero_kernel (g : SmoothMetric E M) (u v : M → ℝ) (x : M)
    (hp : bundleTransverse g u x (metricGradient g v x) = 0)
    (w : TangentSpace 𝓘(ℝ,E) x) (hw : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) u x w = 0) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) v x w = 0 := by
  have hv : metricGradient g v x =
      (g.inner x (metricGradient g u x) (metricGradient g u x))⁻¹ •
        (g.inner x (metricGradient g u x) (metricGradient g v x) • metricGradient g u x) := by
    simpa only [bundleTransverse,sub_apply,ContinuousLinearMap.id_apply,
      smul_apply,bundleRankOne,ContinuousLinearMap.smulRight_apply,
      sub_eq_zero] using hp
  have hzero : g.inner x (metricGradient g u x) w = 0 :=
    (metricGradient_pairing g u x w).trans hw
  rw [←metricGradient_pairing g v x w,hv]
  erw [map_smul, smul_apply, map_smul, smul_apply, hzero]
  simp only [smul_zero]
  rfl
lemma transverse_zero_chart_kernel (g : SmoothMetric E M) {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target)
    (hp : bundleTransverse g u ((chartAt E p).symm y)
      (metricGradient g v ((chartAt E p).symm y)) = 0) :
    ∀ w, fderiv ℝ (u ∘ (chartAt E p).symm) y w = 0 →
      fderiv ℝ (v ∘ (chartAt E p).symm) y w = 0 := by
  intro w hw
  have hd := (contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) p) hy).mdifferentiableAt (by simp)
  have he (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ f) :
      fderiv ℝ (f ∘ (chartAt E p).symm) y w =
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f ((chartAt E p).symm y)
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y w) := by
    have hh := mfderiv_comp y (hf.mdifferentiable (by simp)).mdifferentiableAt hd
    rw [mfderiv_eq_fderiv] at hh
    exact congrArg (fun L => L w) hh
  rw [he u hu] at hw
  rw [he v hv]
  exact transverse_zero_kernel g u v _ hp _ hw



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_AnnularOrthogonalTransverseNonzero
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff InnerProductSpace
section Orthogonality
variable {M : Type*} [TopologicalSpace M] [CompactSpace M]
  [MeasurableSpace M] [OpensMeasurableSpace M]
lemma proportional_orthogonal_zero (μ : Measure M) [Measure.IsOpenPosMeasure μ]
    [IsFiniteMeasureOnCompacts μ] {u v : M → ℝ} (hv : Continuous v)
    (ht : ∃ t : ℝ, v = fun x => t*u x) (ho : ∫ x, v x*u x ∂μ = 0) : v = 0 := by
  by_contra hn
  obtain ⟨x,hx⟩ : ∃ x, v x ≠ 0 := by
    by_contra hn'; push Not at hn'; exact hn (funext hn')
  have hp : 0 < ∫ x, v x*v x ∂μ :=
    (hv.mul hv).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) (fun x => mul_self_nonneg (v x))
      (mul_self_pos.mpr hx).ne'
  obtain ⟨t,ht⟩ := ht
  have he : (fun x => v x*v x) = fun x => t*(v x*u x) := by
    funext x
    rw [congrFun ht x]
    ring
  rw [he, integral_const_mul, ho, mul_zero] at hp
  exact (lt_irrefl 0) hp
end Orthogonality
section Gradient
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma metricGradient_ne_zero_of_chart (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target)
    (hd : fderiv ℝ (u ∘ (chartAt E p).symm) y ≠ 0) :
    metricGradient g u ((chartAt E p).symm y) ≠ 0 := by
  intro hz
  apply hd
  have hf := (contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) p) hy).mdifferentiableAt (by simp)
  have hh := mfderiv_comp y (hu.mdifferentiable (by simp)).mdifferentiableAt hf
  rw [mfderiv_eq_fderiv] at hh
  ext w
  have he : fderiv ℝ (u ∘ (chartAt E p).symm) y w =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) u ((chartAt E p).symm y)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y w) :=
    congrArg (fun L => L w) hh
  rw [he,←metricGradient_pairing g u _ _,hz]
  simp
end Gradient

end

open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff InnerProductSpace




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
lemma three_chart_symm_continuous (p : ThreeManifold) : Continuous (chartAt ThreeModel p).symm := by
  exact continuousOn_univ.mp (by simpa only [OpenPartialHomeomorph.symm_source,three_chart_target] using
    (chartAt ThreeModel p).symm.continuousOn)
end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeFixedFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
attribute [local instance] OAI.YauCounterexamples.instMeasurableSpaceThreeManifold
local instance instBorelSpaceThreeManifold : BorelSpace ThreeManifold := ⟨rfl⟩
lemma threeManifold_preconnected : PreconnectedSpace ThreeManifold := by
  let : PreconnectedSpace (Sphere 2) := Subtype.preconnectedSpace
    (isPreconnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num [Euclidean,finrank_euclideanSpace]) (0:Euclidean 3) 1)
  let : PreconnectedSpace Circle := inferInstance
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
lemma three_rank_separating_tensor_oai
    (μ : Measure ThreeManifold) [Measure.IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ]
    (g : SmoothMetric ThreeModel ThreeManifold) {u v : ThreeManifold → ℝ}
    (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v)
    {Λ : ℝ} (hΛ : 0<Λ) (hue : ∀ p, -laplaceBeltrami g u p=Λ*u p)
    (hve : ∀ p, -laplaceBeltrami g v p=Λ*v p)
    {S : Set ThreeManifold} (hS : IsOpen S)
    (hG : ∀ p∈S, 0 < coordinateGradientPair g u u p)
    (hrank : ∃ x : ThreeModel, (chartAt ThreeModel threeProfileCenter).symm x∈S ∧
      Function.Surjective (fderiv ℝ (fun y => (u ((chartAt ThreeModel threeProfileCenter).symm y),
        coordinateGradientPair g u u ((chartAt ThreeModel threeProfileCenter).symm y))) x))
    (hv0 : v≠0) (ho : ∫ x, v x*u x ∂μ=0) :
    ∃ χ : ThreeManifold → ℝ, tsupport χ⊆S ∧
      ContMDiff 𝓘(ℝ,ThreeModel) (𝓘(ℝ,ThreeModel).prod 𝓘(ℝ,ThreeModel →L[ℝ] ThreeModel)) ∞
        (fun y => TotalSpace.mk' (ThreeModel →L[ℝ] ThreeModel) y (supportedPinningTensor g u v χ y)) ∧
      (∀ y, LinearMap.trace ℝ (TangentSpace 𝓘(ℝ,ThreeModel) y)
        (supportedPinningTensor g u v χ y).toLinearMap=0) ∧
      (∀ y, supportedPinningTensor g u v χ y (metricGradient g u y)=0) ∧
      0<∫ y, g.inner y (metricGradient g v y)
        (supportedPinningTensor g u v χ y (metricGradient g v y)) ∂μ := by
  have hn (p : ThreeManifold) (hp : p∈S) : metricGradient g u p≠0 := by
    have he := metricGradient_ne_zero_of_chart g hu p
      ((chartAt ThreeModel p).map_source (mem_chart_source ThreeModel p))
      (by intro hz; have hh := hG p hp; simp [coordinateGradientPair,hz] at hh)
    change (fun q : ThreeManifold => metricGradient g u q≠0) ((chartAt ThreeModel p).symm (chartAt ThreeModel p p)) at he
    rw [(chartAt ThreeModel p).left_inv (mem_chart_source ThreeModel p)] at he
    exact he
  suffices hex : ∃ p∈S, bundleTransverse g u p (metricGradient g v p)≠0 by
    obtain ⟨p,hp,ht⟩ := hex
    exact exists_supported_separating_tensor μ g hu hv hS hn hp ht threeModel_finrank
  by_contra hnone
  have hzero (p : ThreeManifold) (hp : p∈S) : bundleTransverse g u p (metricGradient g v p)=0 := by
    by_contra hh
    exact hnone ⟨p,hp,hh⟩
  apply hv0
  apply proportional_orthogonal_zero μ hv.continuous _ ho
  let chart := chartAt ThreeModel threeProfileCenter
  let O := chart.symm ⁻¹' S
  have hO : IsOpen O := hS.preimage (three_chart_symm_continuous threeProfileCenter)
  obtain ⟨x,hx,hr⟩ := hrank
  have hOt : O⊆chart.target := by rw [three_chart_target]; exact subset_univ _
  have hdu : fderiv ℝ (u ∘ chart.symm) x≠0 := by
    intro hz
    have hp := hG _ hx
    rw [←localGradientPair_eq_global hu g threeProfileCenter (hOt hx)] at hp
    change fderiv ℝ (u ∘ (chartAt ThreeModel threeProfileCenter).symm) x=0 at hz
    simp [localGradientPair,hz] at hp
  have hpair : ContDiffAt ℝ 1 (fun y => (u (chart.symm y),coordinateGradientPair g u u (chart.symm y))) x :=
    ((contDiffAt_inChart hu threeProfileCenter (hOt hx)).prodMk
      (contDiffAt_inChart (contMDiff_coordinateGradientPair hu hu g) threeProfileCenter (hOt hx))).of_le
      (by simp)
  obtain ⟨c,hc⟩ := local_eigen_proportional_of_gradient_rank g threeProfileCenter hO hx hOt
    (hu.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    (hv.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) hdu
    (fun y hy => transverse_zero_chart_kernel g hu hv threeProfileCenter (hOt hy) (hzero _ hy))
    hpair hr (hG _ hx) hΛ (fun y _ => by linarith [hue (chart.symm y)])
    (fun y _ => by linarith [hve (chart.symm y)]) (fun _ _ => rfl)
  let := threeManifold_preconnected
  exact ⟨c,proportional_eigen_global g hu hv Λ c hue hve ⟨chart.symm x,hc⟩⟩
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.three_rank_separating_tensor_oai := @OAI.YauCounterexamples.three_rank_separating_tensor_oai
