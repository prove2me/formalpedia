-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.splitTest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:42:48.052497+00:00
-- url     : https://prove2.me/submissions/1e99e2de-d3c7-4011-9a5d-0464869aff7c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_SplitTest
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_splitT_ac
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_splitT_ae
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_splitT_fin
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_splitT_memLp_iff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_splitT_inner
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_splitT_inner2
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_splitT_hcs
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_splitT_cont
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_splitT_weakS
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_ck
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
section SplitHelpers
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}
end SplitHelpers
private theorem d_db_eq_zero_of_not_mem_compact_support {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n)
    (K0 : Set M) (hK0 : IsCompact K0) (u : M → ℂ) (hu : ∀ x, x ∉ K0 → u x = 0) (x : M)
    (hx : x ∉ K0) (j : Fin n) : d n z j u x = 0 ∧ db n z j u x = 0 := by
  have key : ∀ h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source,
      fderiv ℝ (u ∘ (Classical.choose h).symm) (z x) = 0 := by
    intro h
    obtain ⟨he, hx'⟩ := Classical.choose_spec h
    set e := Classical.choose h
    have hzx : z x = e x := he hx'
    have hev : (u ∘ e.symm) =ᶠ[𝓝 (z x)] fun _ => (0 : ℂ) := by
      rw [hzx]
      have hopen : IsOpen K0ᶜ := hK0.isClosed.isOpen_compl
      have hc : ContinuousAt e.symm (e x) := e.continuousAt_symm (e.map_source hx')
      have hmem : K0ᶜ ∈ 𝓝 (e.symm (e x)) := by
        rw [e.left_inv hx']
        exact hopen.mem_nhds hx
      filter_upwards [hc.preimage_mem_nhds hmem] with y hy
      exact hu _ hy
    rw [hev.fderiv_eq]
    exact fderiv_const_apply _
  unfold d db wd wdb
  constructor
  · split_ifs with h
    · rw [key h]
      simp
    · rfl
  · split_ifs with h
    · rw [key h]
      simp
    · rfl
private theorem smooth_exp_ofReal_of_smooth {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (u : M → ℝ)
    (hu : Smooth n z (fun y => (u y : ℂ))) : Smooth n z (fun y => (Real.exp (u y) : ℂ)) := by
  unfold Smooth at hu ⊢
  intro e he
  have hg : ContDiff ℝ ∞ (fun w : ℂ => ((Real.exp w.re : ℝ) : ℂ)) := by
    first
    | fun_prop
    | exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp Complex.reCLM.contDiff)
  refine (hg.comp_contDiffOn (hu e he)).congr fun p _ => ?_
  simp [Function.comp]
end
end ReciprocityTheory.L2DbarEstimates.F
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hK : KSubStatement n M) (hWS : WeakSSmoothStatement n M)
    (hSD : SbarDbarStatement n M) (hTI : TStarIbpStatement n M) : SplitTestStatement n M := by
  unfold SplitTestStatement
  unfold KSubStatement at hK
  unfold WeakSSmoothStatement at hWS
  unfold SbarDbarStatement at hSD
  unfold TStarIbpStatement at hTI
  intro z hz ph₁ ph₂ v f hph₁ hph₂ hv hvS hf
  have hc1 : Continuous ph₁ :=
    Complex.continuous_re.comp (Smooth.continuous n z hz (fun x => (ph₁ x : ℂ)) hph₁)
  have hc2 : Continuous ph₂ :=
    Complex.continuous_re.comp (Smooth.continuous n z hz (fun x => (ph₂ x : ℂ)) hph₂)
  haveI hfin2 : IsFiniteMeasureOnCompacts (wvol n z ph₂) := splitT_fin hz ph₂ hc2
  haveI hfin1 : IsFiniteMeasureOnCompacts (wvol n z ph₁) := splitT_fin hz ph₁ hc1
  obtain ⟨K, hKc, hKiff⟩ := hK z hz ph₂ hc2
  haveI : CompleteSpace K := hKc.completeSpace_coe
  unfold IsTestForm at hf
  have hfcont : Continuous f := splitT_cont f fun j => Ck.continuous n z hz 2 _ (hf j).1
  have hfsupp : HasCompactSupport f := by
    refine splitT_hcs f (fun j => tsupport fun x => f x j) (fun j => (hf j).2) fun x hx => ?_
    ext j
    have h0 := image_eq_zero_of_notMem_tsupport (hx j)
    simpa using h0
  have hfL : MemLp f 2 (wvol n z ph₂) := hfcont.memLp_of_hasCompactSupport hfsupp

  have hE1 : Smooth n z (fun y => (Real.exp (ph₁ y) : ℂ)) := smooth_exp_ofReal_of_smooth n z ph₁ hph₁
  have hE2 : Smooth n z (fun y => (Real.exp (-ph₂ y) : ℂ)) := by
    apply smooth_exp_ofReal_of_smooth n z (fun y => -ph₂ y)
    show Smooth n z (fun y => ((-ph₂ y : ℝ) : ℂ))
    have h := Smooth.mul n z (fun _ => (-1 : ℂ)) (fun y => (ph₂ y : ℂ)) (Smooth.const n z (-1)) hph₂
    have he : (fun y => ((-ph₂ y : ℝ) : ℂ)) = fun y => (-1 : ℂ) * (ph₂ y : ℂ) := by
      funext y
      push_cast
      ring
    rw [he]
    exact h
  have hprod : ∀ j, Ck n z 2 (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) := fun j =>
    Ck.mul n z 2 _ _ (Smooth.ck n z 2 _ hE2) (hf j).1
  have hdj : ∀ j, Continuous (d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j)) := fun j =>
    Ck.continuous n z hz 1 _ (Ck.d n z 1 j _ (hprod j))
  have htc : Continuous (tstar n z ph₁ ph₂ f) := by
    unfold tstar
    exact ((Smooth.continuous n z hz _ hE1).mul (continuous_finset_sum _ fun j _ => hdj j)).neg
  have hoff : ∀ j x, x ∉ tsupport (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) →
      d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x = 0 := fun j x hx =>
    (d_db_eq_zero_of_not_mem_compact_support n z (tsupport fun y => (Real.exp (-ph₂ y) : ℂ) * f y j)
      ((hf j).2.mul_left (f := fun y => (Real.exp (-ph₂ y) : ℂ))) _
      (fun y hy => image_eq_zero_of_notMem_tsupport hy) x hx j).1
  have htsupp : HasCompactSupport (tstar n z ph₁ ph₂ f) := by
    refine splitT_hcs _ (fun j => tsupport fun y => (Real.exp (-ph₂ y) : ℂ) * f y j)
      (fun j => (hf j).2.mul_left (f := fun y => (Real.exp (-ph₂ y) : ℂ))) fun x hx => ?_
    have h0 : ∀ j, d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x = 0 := fun j =>
      hoff j x (hx j)
    unfold tstar
    simp only [h0, Finset.sum_const_zero, mul_zero, neg_zero]
  have hMF : MemWeightedL2 n z (tstar n z ph₁ ph₂ f) ph₁ := by
    have hm : MemLp (tstar n z ph₁ ph₂ f) 2 (wvol n z ph₁) := htc.memLp_of_hasCompactSupport htsupp
    unfold MemWeightedL2 wint
    exact ⟨htc.aestronglyMeasurable,
      (splitT_memLp_iff ph₁ hc1 _ htc.aestronglyMeasurable).1 hm⟩

  unfold MemWeightedL2OneForm nV at hv
  have hv' : MemLp v 2 (wvol n z ph₂) := (splitT_memLp_iff ph₂ hc2 v hv.1).2 hv.2
  have hVK : hv'.toLp v ∈ K :=
    (hKiff _).2 (splitT_weakS v _ (splitT_ae ph₂ hc2 hv'.coeFn_toLp).symm 0 hvS)

  obtain ⟨F₁, hF₁K, G, hGperp, hdec⟩ := K.exists_add_mem_mem_orthogonal (hfL.toLp f)
  have hoffg : ∀ g : M → ℂ, HasCompactSupport g → ∀ j x, x ∉ tsupport g → db n z j g x = 0 :=
    fun g hg j x hx =>
      (d_db_eq_zero_of_not_mem_compact_support n z (tsupport g) hg g (fun y hy => image_eq_zero_of_notMem_tsupport hy) x hx j).2
  refine ⟨hMF, fun x => F₁ x, ?_, (hKiff F₁).1 hF₁K, ?_, ?_⟩
  · unfold MemWeightedL2OneForm nV
    have ha : AEStronglyMeasurable (fun x => F₁ x) (vol n z) :=
      (Lp.aestronglyMeasurable F₁).mono_ac (splitT_ac ph₂ hc2)
    exact ⟨ha, (splitT_memLp_iff ph₂ hc2 _ ha).1 (Lp.memLp F₁)⟩
  · unfold IsWeakAdj
    intro g hg
    unfold IsTest at hg
    have hDc : Continuous (dbarF n z g) :=
      splitT_cont _ fun j => Smooth.continuous n z hz _ (Smooth.db n z j g hg.1)
    have hDs : HasCompactSupport (dbarF n z g) := by
      refine splitT_hcs _ (fun _ : Fin n => tsupport g) (fun _ => hg.2) fun x hx => ?_
      first
      | exact PiLp.ext fun j => hoffg g hg.2 j x (hx j)
      | (ext j; exact hoffg g hg.2 j x (hx j))
    have hDg : MemLp (dbarF n z g) 2 (wvol n z ph₂) := hDc.memLp_of_hasCompactSupport hDs
    have hW := hWS z hz (dbarF n z g) fun j => Smooth.ck n z 1 _ (Smooth.db n z j g hg.1)
    have hsbar : sbar n z (dbarF n z g) = 0 := funext fun x => hSD z hz g (Smooth.ck n z 2 g hg.1) x
    rw [hsbar] at hW
    have hDK : hDg.toLp (dbarF n z g) ∈ K :=
      (hKiff _).2 (splitT_weakS _ _ (splitT_ae ph₂ hc2 hDg.coeFn_toLp).symm 0 hW)
    have hck1 : CkR n z 1 ph₁ := Smooth.ck n z 1 _ hph₁
    have hck2 : CkR n z 1 ph₂ := Smooth.ck n z 1 _ hph₂
    have hfc : ∀ j, Ck n z 1 (fun x => f x j) ∧ HasCompactSupport (fun x => f x j) := fun j =>
      ⟨Ck.mono n z 1 2 (by norm_num) _ (hf j).1, (hf j).2⟩
    calc ∫ x, ⟪dbarF n z g x, F₁ x⟫_ℂ * (Real.exp (-ph₂ x) : ℂ) ∂vol n z
        = ⟪hDg.toLp (dbarF n z g), F₁⟫_ℂ := (splitT_inner ph₂ hc2 _ hDg F₁).symm
      _ = ⟪hDg.toLp (dbarF n z g), hfL.toLp f⟫_ℂ := by
          rw [hdec, inner_add_right, Submodule.inner_right_of_mem_orthogonal hDK hGperp, add_zero]
      _ = ∫ x, ⟪dbarF n z g x, f x⟫_ℂ * (Real.exp (-ph₂ x) : ℂ) ∂vol n z :=
          splitT_inner2 ph₂ hc2 _ _ hDg hfL
      _ = ∫ x, conj ((∑ j, db n z j g x * conj (f x j)) * (Real.exp (-ph₂ x) : ℂ)) ∂vol n z := by
          congr 1
          funext x
          rw [map_mul, Complex.conj_ofReal, map_sum, PiLp.inner_apply]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul, Complex.conj_conj]
          show ⟪db n z j g x, f x j⟫_ℂ = _
          first
          | rfl
          | (simp only [RCLike.inner_apply]; ring)
          | (simp only [RCLike.inner_apply])
          | (simp [mul_comm])
      _ = conj (∫ x, (∑ j, db n z j g x * conj (f x j)) * (Real.exp (-ph₂ x) : ℂ) ∂vol n z) :=
          integral_conj
      _ = conj (∫ x, g x * conj (tstar n z ph₁ ph₂ f x) * (Real.exp (-ph₁ x) : ℂ) ∂vol n z) := by
          rw [hTI z hz ph₁ ph₂ g f hck1 hck2 (Smooth.ck n z 1 g hg.1) hfc]
      _ = ∫ x, conj (g x) * tstar n z ph₁ ph₂ f x * (Real.exp (-ph₁ x) : ℂ) ∂vol n z := by
          rw [← integral_conj]
          congr 1
          funext x
          rw [map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  · have e1 : ipV n z v f ph₂ = ⟪hv'.toLp v, hfL.toLp f⟫_ℂ := by
      unfold ipV
      exact (splitT_inner2 ph₂ hc2 v f hv' hfL).symm
    have e2 : ipV n z v (fun x => F₁ x) ph₂ = ⟪hv'.toLp v, F₁⟫_ℂ := by
      unfold ipV
      exact (splitT_inner ph₂ hc2 v hv' F₁).symm
    rw [e1, e2, hdec, inner_add_right, Submodule.inner_right_of_mem_orthogonal hVK hGperp, add_zero]
end ReciprocityTheory.L2DbarEstimates.F
