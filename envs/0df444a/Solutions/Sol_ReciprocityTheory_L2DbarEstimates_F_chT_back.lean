-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.chT_back
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:30:03.858595+00:00
-- url     : https://prove2.me/submissions/65ea59e3-89b5-48c8-bd30-e4c88b1f5bd4

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_lint
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (hExt : ExtendStatement n M) (hz : IsLocalHomeomorph z) (he : IsChart n z e)
    (G : M → V n) (D : M → ℂ) (S : M → Fin n → Fin n → ℂ)
    (hG : AEStronglyMeasurable G (vol n z)) (hD : AEStronglyMeasurable D (vol n z))
    (hS : AEStronglyMeasurable S (vol n z))
    (hGs : tsupport G ⊆ e.source) (hDs : tsupport D ⊆ e.source) (hSs : tsupport S ⊆ e.source)
    (K₀ : Set (V n)) (hK₀c : IsCompact K₀) (hK₀t : K₀ ⊆ e.target) (G' : V n → V n)
    (hG'd : ContDiff ℝ ∞ G') (hG'0 : ∀ y, y ∉ K₀ → G' y = 0) (δ : ℝ≥0∞)
    (h1 : ∫⁻ y, ‖G' y - e.target.indicator (G ∘ e.symm) y‖ₑ ^ 2 < δ)
    (h2 : ∫⁻ y, ‖(∑ j, wd n j (fun u => G' u j) y) - e.target.indicator (D ∘ e.symm) y‖ₑ ^ 2 < δ)
    (h3 : ∫⁻ y, ENNReal.ofReal (sq2 n (fun j k =>
        wdb n j (fun u => G' u k) y - wdb n k (fun u => G' u j) y -
          e.target.indicator (S ∘ e.symm) y j k)) < δ) :
    ∃ g : M → V n, IsTestForm n z g ∧ (∀ x, x ∉ e.symm '' K₀ → g x = 0) ∧
      nV n z (fun x => g x - G x) (fun _ => 0) < δ ∧
      wint n z (fun x => divF n z g x - D x) (fun _ => 0) < δ ∧
      n2 n z (fun x => sbar n z g x - S x) (fun _ => 0) < δ := by
  classical
  have hms : MeasurableSet e.source := e.open_source.measurableSet
  have hmt : MeasurableSet e.target := e.open_target.measurableSet
  have hK₀cl : IsClosed K₀ := hK₀c.isClosed

  have hfz : ∀ (f : V n → ℂ) (y : V n), f =ᶠ[𝓝 y] (fun _ => (0 : ℂ)) → ∀ i,
      wd n i f y = 0 ∧ wdb n i f y = 0 := by
    intro f y hf i
    simp [wd, wdb, hf.fderiv_eq]
  have hdz : ∀ (f : M → ℂ) (x : M), x ∉ tsupport f → ∀ i, d n z i f x = 0 ∧ db n z i f x = 0 := by
    intro f x hx i
    by_cases h : ∃ e' : OpenPartialHomeomorph M (V n), IsChart n z e' ∧ x ∈ e'.source
    · have hev : (f ∘ (Classical.choose h).symm) =ᶠ[𝓝 (z x)] (fun _ => (0 : ℂ)) := by
        obtain ⟨hc, hxs⟩ := Classical.choose_spec h
        rw [hc hxs]
        have hW := (Classical.choose h).continuousOn_symm.isOpen_inter_preimage
          (Classical.choose h).open_target (isClosed_tsupport f).isOpen_compl
        have hmem : (Classical.choose h) x ∈
            (Classical.choose h).target ∩ (Classical.choose h).symm ⁻¹' (tsupport f)ᶜ := by
          refine ⟨(Classical.choose h).map_source hxs, ?_⟩
          show (Classical.choose h).symm ((Classical.choose h) x) ∉ tsupport f
          rw [(Classical.choose h).left_inv hxs]
          exact hx
        filter_upwards [hW.mem_nhds hmem] with y hy
        show f ((Classical.choose h).symm y) = 0
        by_contra hne
        exact hy.2 (subset_tsupport _ (Function.mem_support.2 hne))
      simp only [d, db, dif_pos h]
      exact hfz _ _ hev i
    · simp [d, db, dif_neg h]
  have hG'0j : ∀ j, ∀ y, y ∉ K₀ → G' y j = 0 := fun j y hy => by
    rw [hG'0 y hy]
    simp
  have hG'j : ∀ j, ContDiff ℝ ∞ (fun u => G' u j) := fun j => by
    have := ((EuclideanSpace.proj j : V n →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hG'd
    exact this
  have hcs : ∀ j, HasCompactSupport (fun u => G' u j) := fun j =>
    HasCompactSupport.intro hK₀c (fun y hy => hG'0j j y hy)
  have hts : ∀ j, tsupport (fun u => G' u j) ⊆ e.target := fun j =>
    (closure_minimal (fun y hy => by by_contra h; exact hy (hG'0j j y h)) hK₀cl).trans hK₀t
  have hE := fun j => hExt z hz e (fun u => G' u j) he (hG'j j) (hcs j) (hts j)
  have hwz : ∀ j, ∀ y, y ∉ K₀ → ∀ i, wd n i (fun u => G' u j) y = 0 ∧ wdb n i (fun u => G' u j) y = 0 :=
    fun j y hy i => hfz _ y (by
      filter_upwards [hK₀cl.isOpen_compl.mem_nhds hy] with u hu
      exact hG'0j j u hu) i
  have hcf : ∀ (f : V n → ℂ), ContDiff ℝ ∞ f → ∀ i, Continuous (wd n i f) ∧ Continuous (wdb n i f) := by
    intro f hf i
    have h := hf.continuous_fderiv (by simp)
    exact ⟨((h.clm_apply continuous_const).sub (continuous_const.mul (h.clm_apply continuous_const))).div_const 2,
      ((h.clm_apply continuous_const).add (continuous_const.mul (h.clm_apply continuous_const))).div_const 2⟩
  have hind : ∀ {E : Type} [NormedAddCommGroup E] (w : V n → E), Continuous w →
      AEStronglyMeasurable (e.source.indicator (fun x => w (e x))) (vol n z) :=
    fun w hw => (aestronglyMeasurable_indicator_iff hms).2
      ((hw.comp_continuousOn e.continuousOn).aestronglyMeasurable hms)
  have hGz : ∀ x, x ∉ e.source → G x = 0 := fun x hx => by
    by_contra h
    exact hx (hGs (subset_tsupport _ (Function.mem_support.2 h)))
  have hDz : ∀ x, x ∉ e.source → D x = 0 := fun x hx => by
    by_contra h
    exact hx (hDs (subset_tsupport _ (Function.mem_support.2 h)))
  have hSz : ∀ x, x ∉ e.source → S x = 0 := fun x hx => by
    by_contra h
    exact hx (hSs (subset_tsupport _ (Function.mem_support.2 h)))

  have htr : ∀ (F : M → ℝ≥0∞) (H : V n → ℝ≥0∞), AEMeasurable F (vol n z) →
      (∀ x, x ∉ e.source → F x = 0) → (∀ y ∈ e.target, F (e.symm y) = H y) →
      (∀ y, y ∉ e.target → H y = 0) → ∫⁻ x, F x ∂vol n z = ∫⁻ y, H y := by
    intro F H hF hs hon hoff
    rw [chT_lint hz he F hF hs, ← lintegral_indicator hmt]
    congr 1
    funext y
    by_cases hy : y ∈ e.target
    · rw [Set.indicator_of_mem hy, hon y hy]
    · rw [Set.indicator_apply, if_neg hy, hoff y hy]
  set g : M → V n := e.source.indicator (G' ∘ e) with hgdef
  have hgj : ∀ j, (fun x => g x j) = e.source.indicator ((fun u => G' u j) ∘ e) := fun j => by
    funext x
    by_cases hx : x ∈ e.source <;> simp [hgdef, Set.indicator_apply, hx]
  have hdiv : ∀ x, divF n z g x =
      e.source.indicator (fun x => ∑ i, wd n i (fun u => G' u i) (e x)) x := by
    intro x
    show ∑ i, d n z i (fun y => g y i) x = _
    by_cases hx : x ∈ e.source
    · rw [Set.indicator_of_mem hx]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hgj i]
      exact ((hE i).2.2.2 i x hx).1
    · rw [Set.indicator_apply, if_neg hx]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hgj i]
      exact (hdz _ x (fun h => hx ((hE i).2.2.1 h)) i).1
  have hsb : ∀ x, sbar n z g x - S x = fun j k =>
      e.source.indicator (fun x => wdb n j (fun u => G' u k) (e x) - wdb n k (fun u => G' u j) (e x)) x -
        S x j k := by
    intro x
    funext j k
    show db n z j (fun y => g y k) x - db n z k (fun y => g y j) x - S x j k = _
    rw [hgj k, hgj j]
    by_cases hx : x ∈ e.source
    · rw [Set.indicator_of_mem hx, ((hE k).2.2.2 j x hx).2, ((hE j).2.2.2 k x hx).2]
    · rw [Set.indicator_apply, if_neg hx, (hdz _ x (fun h => hx ((hE k).2.2.1 h)) j).2,
        (hdz _ x (fun h => hx ((hE j).2.2.1 h)) k).2, sub_zero]
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hgj j]
    exact ⟨fun e' he' => ((hE j).1 e' he').of_le (by first | (simp; done) | (norm_num; done) | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.2 le_top | exact le_top), (hE j).2.1⟩
  · intro x hx
    by_cases hxs : x ∈ e.source
    · rw [hgdef, Set.indicator_of_mem hxs, Function.comp_apply]
      exact hG'0 _ (fun h => hx ⟨e x, h, e.left_inv hxs⟩)
    · rw [hgdef, Set.indicator_apply, if_neg hxs]
  · have heq : nV n z (fun x => g x - G x) (fun _ => 0) =
        ∫⁻ y, ‖G' y - e.target.indicator (G ∘ e.symm) y‖ₑ ^ 2 := by
      simp only [nV, neg_zero, Real.exp_zero, mul_one]
      apply htr
      · exact (((hind G' hG'd.continuous).sub hG).norm.pow 2).aemeasurable.ennreal_ofReal
      · intro x hx
        simp [hgdef, Set.indicator_apply, hx, hGz x hx]
      · intro y hy
        rw [hgdef, Set.indicator_of_mem (e.map_target hy), Function.comp_apply, e.right_inv hy,
          Set.indicator_of_mem hy, Function.comp_apply, ENNReal.ofReal_pow (norm_nonneg _),
          ofReal_norm_eq_enorm]
      · intro y hy
        rw [hG'0 y (fun h => hy (hK₀t h)), Set.indicator_apply, if_neg hy]
        simp
    rw [heq]
    exact h1
  · have hcs' : Continuous (fun y => ∑ i, wd n i (fun u => G' u i) y) :=
      continuous_finset_sum _ fun i _ => (hcf _ (hG'j i) i).1
    have heq : wint n z (fun x => divF n z g x - D x) (fun _ => 0) =
        ∫⁻ y, ‖(∑ j, wd n j (fun u => G' u j) y) - e.target.indicator (D ∘ e.symm) y‖ₑ ^ 2 := by
      simp only [wint, neg_zero, Real.exp_zero, mul_one, hdiv]
      apply htr
      · exact (((hind _ hcs').sub hD).norm.pow 2).aemeasurable.ennreal_ofReal
      · intro x hx
        simp [Set.indicator_apply, hx, hDz x hx]
      · intro y hy
        rw [Set.indicator_of_mem (e.map_target hy), e.right_inv hy, Set.indicator_of_mem hy, Function.comp_apply,
          ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
      · intro y hy
        have hyK : y ∉ K₀ := fun h => hy (hK₀t h)
        rw [Finset.sum_eq_zero fun i _ => (hwz i y hyK i).1, Set.indicator_apply, if_neg hy]
        simp
    rw [heq]
    exact h2
  · have hSjk : ∀ j k, AEStronglyMeasurable (fun x => S x j k) (vol n z) := fun j k =>
      (continuous_apply k).comp_aestronglyMeasurable ((continuous_apply j).comp_aestronglyMeasurable hS)
    have heq : n2 n z (fun x => sbar n z g x - S x) (fun _ => 0) =
        ∫⁻ y, ENNReal.ofReal (sq2 n (fun j k =>
          wdb n j (fun u => G' u k) y - wdb n k (fun u => G' u j) y -
            e.target.indicator (S ∘ e.symm) y j k)) := by
      simp only [n2, neg_zero, Real.exp_zero, mul_one, hsb]
      apply htr
      · refine (AEStronglyMeasurable.aemeasurable ?_).ennreal_ofReal
        simp only [sq2, div_eq_mul_inv]
        refine AEStronglyMeasurable.mul_const ?_ _
        refine Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
          Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
        exact ((hind _ ((hcf _ (hG'j k) j).2.sub (hcf _ (hG'j j) k).2)).sub (hSjk j k)).norm.pow 2
      · intro x hx
        simp [sq2, Set.indicator_apply, hx, hSz x hx]
      · intro y hy
        simp only [sq2, Set.indicator_of_mem (e.map_target hy), Set.indicator_of_mem hy,
          e.right_inv hy, Function.comp_apply]
      · intro y hy
        have hyK : y ∉ K₀ := fun h => hy (hK₀t h)
        have h0 : ∀ i j, wdb n i (fun u => G' u j) y = 0 := fun i j => (hwz j y hyK i).2
        simp [sq2, h0, Set.indicator_apply, hy]
    rw [heq]
    exact h3
end ReciprocityTheory.L2DbarEstimates.F
