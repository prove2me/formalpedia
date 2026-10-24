-- Prove2me | solution 1 for StochasticOrders.MonotoneConvex.icv_supermartingale_coupling_iff_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T21:10:51.981667+00:00
-- url     : https://prove2.me/submissions/c7298fe6-5988-4b5b-846f-d9c71270555d

import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcvOrder
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder
import Theorems.Thm_StochasticOrders_MonotoneConvex_icx_submartingale_coupling_iff_v2
open MeasureTheory ProbabilityTheory
namespace CPL97ICV

noncomputable def negK (κ : Kernel ℝ ℝ) : Kernel ℝ ℝ :=
  (Kernel.comap κ (fun y : ℝ => -y) measurable_neg).map (fun x : ℝ => -x)

lemma negK_apply' (κ : Kernel ℝ ℝ) (y : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    negK κ y s = κ (-y) ((fun x : ℝ => -x) ⁻¹' s) := by
  rw [negK, Kernel.map_apply' _ measurable_neg _ hs, Kernel.comap_apply]

instance negK_markov (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] : IsMarkovKernel (negK κ) :=
  Kernel.IsMarkovKernel.map _ measurable_neg

lemma Iic_le_of {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : ∀ s, P (Set.Ioi s) ≤ Q (Set.Ioi s)) (s : ℝ) : Q (Set.Iic s) ≤ P (Set.Iic s) := by
  have hP := prob_compl_eq_one_sub (μ := P) (measurableSet_Ioi (a := s))
  have hQ := prob_compl_eq_one_sub (μ := Q) (measurableSet_Ioi (a := s))
  rw [Set.compl_Ioi] at hP hQ
  rw [hP, hQ]
  exact tsub_le_tsub_left (h s) 1

lemma Iio_le_of {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : ∀ s, P (Set.Ioi s) ≤ Q (Set.Ioi s)) (c : ℝ) : Q (Set.Iio c) ≤ P (Set.Iio c) := by
  have hU : Set.Iio c = ⋃ n : ℕ, Set.Iic (c - 1 / ((n:ℝ) + 1)) := by
    ext x
    simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Iic]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith
  have hm : Monotone (fun n : ℕ => Set.Iic (c - 1 / ((n:ℝ) + 1))) := by
    intro m n hmn
    apply Set.Iic_subset_Iic.mpr
    have : ((m:ℝ) + 1) ≤ (n:ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    have : 1 / ((n:ℝ) + 1) ≤ 1 / ((m:ℝ) + 1) := one_div_le_one_div_of_le (by positivity) this
    linarith
  rw [hU, hm.measure_iUnion, hm.measure_iUnion]
  exact iSup_mono fun n => Iic_le_of h _

lemma negK_mono (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (hmono : ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → ∀ t : ℝ, κ x₁ {y : ℝ | t < y} ≤ κ x₂ {y : ℝ | t < y}) :
    ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → ∀ t : ℝ, negK κ x₁ {y : ℝ | t < y} ≤ negK κ x₂ {y : ℝ | t < y} := by
  intro x₁ x₂ hx t
  change negK κ x₁ (Set.Ioi t) ≤ negK κ x₂ (Set.Ioi t)
  rw [negK_apply' _ _ (measurableSet_Ioi (a := t)), negK_apply' _ _ (measurableSet_Ioi (a := t))]
  have e : ((fun x : ℝ => -x) ⁻¹' Set.Ioi t) = Set.Iio (-t) := by
    ext x; simp
  rw [e]
  exact Iio_le_of (P := κ (-x₂)) (Q := κ (-x₁)) (fun s => hmono _ _ (neg_le_neg hx) s) _

lemma compProd_neg (m : Measure ℝ) [IsFiniteMeasure m] (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] :
    (m ⊗ₘ κ).map (Prod.map (fun x : ℝ => -x) (fun x : ℝ => -x))
      = (m.map (fun x : ℝ => -x)) ⊗ₘ negK κ := by
  have hpm : Measurable (Prod.map (fun x : ℝ => -x) (fun x : ℝ => -x)) :=
    measurable_neg.prodMap measurable_neg
  ext s hs
  rw [Measure.map_apply hpm hs, Measure.compProd_apply (hpm hs), Measure.compProd_apply hs,
    lintegral_map _ measurable_neg]
  · congr 1
    funext a
    rw [negK_apply' _ _ (measurable_prodMk_left hs), neg_neg]
    rfl
  · exact Kernel.measurable_kernel_prodMk_left hs


lemma convexOn_comp_neg {φ : ℝ → ℝ} (h : ConvexOn ℝ Set.univ φ) :
    ConvexOn ℝ Set.univ (fun x => φ (-x)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have e : -(a • x + b • y) = a • (-x) + b • (-y) := by simp only [smul_eq_mul]; ring
  simp only
  rw [e]
  exact h.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

lemma concaveOn_comp_neg {φ : ℝ → ℝ} (h : ConcaveOn ℝ Set.univ φ) :
    ConcaveOn ℝ Set.univ (fun x => φ (-x)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have e : -(a • x + b • y) = a • (-x) + b • (-y) := by simp only [smul_eq_mul]; ring
  simp only
  rw [e]
  exact h.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

open StochasticOrders.MonotoneConvex in
lemma icv_iff_icx {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) :
    IcvOrder μ ν X Y ↔ IcxOrder ν μ (-Y) (-X) := by
  constructor
  · intro h φ hm hc hiY hiX
    have hψm : Monotone (fun x => -φ (-x)) := fun a b hab => neg_le_neg (hm (neg_le_neg hab))
    have hψc : ConcaveOn ℝ Set.univ (fun x => -φ (-x)) := by
      have := neg_concaveOn_iff.mpr (convexOn_comp_neg hc)
      exact this
    have h1 := h _ hψm hψc (by simpa [Function.comp_def] using hiX.neg)
      (by simpa [Function.comp_def] using hiY.neg)
    rw [integral_neg, integral_neg] at h1
    simpa using h1
  · intro h φ hm hc hiX hiY
    have hψm : Monotone (fun x => -φ (-x)) := fun a b hab => neg_le_neg (hm (neg_le_neg hab))
    have hψc : ConvexOn ℝ Set.univ (fun x => -φ (-x)) := by
      have := neg_convexOn_iff.mpr (concaveOn_comp_neg hc)
      exact this
    have h1 := h _ hψm hψc (by simpa [Function.comp_def] using hiY.neg)
      (by simpa [Function.comp_def] using hiX.neg)
    simp only [Pi.neg_apply, neg_neg] at h1
    rw [integral_neg, integral_neg] at h1
    simpa using h1

lemma comap_neg {Ω : Type*} (A : Ω → ℝ) :
    MeasurableSpace.comap (-A) (inferInstance : MeasurableSpace ℝ)
      = MeasurableSpace.comap A inferInstance := by
  apply le_antisymm
  · exact (measurable_neg.comp (comap_measurable A)).comap_le
  · have : Measurable[MeasurableSpace.comap (-A) inferInstance] (-(-A)) :=
      measurable_neg.comp (comap_measurable (-A))
    rw [neg_neg] at this
    exact this.comap_le

lemma transfer_map {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (A B : Ω → ℝ) (hA : Measurable A) (hB : Measurable B) (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (h : ρ.map (fun ω => (A ω, B ω)) = ρ.map A ⊗ₘ κ) :
    ρ.map (fun ω => ((-A) ω, (-B) ω)) = ρ.map (-A) ⊗ₘ negK κ := by
  have e1 : (fun ω => ((-A) ω, (-B) ω))
      = Prod.map (fun x : ℝ => -x) (fun x : ℝ => -x) ∘ (fun ω => (A ω, B ω)) := rfl
  have e2 : (-A) = (fun x : ℝ => -x) ∘ A := rfl
  rw [e1, e2, ← Measure.map_map (measurable_neg.prodMap measurable_neg) (hA.prodMk hB),
    ← Measure.map_map measurable_neg hA, h, compProd_neg]

end CPL97ICV

open StochasticOrders.MonotoneConvex in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXint : Integrable X μ) (hYint : Integrable Y ν) :
    IcvOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → ℝ),
        Measurable Xhat ∧ Measurable Yhat ∧
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧
        ρ[Xhat | MeasurableSpace.comap Yhat inferInstance] ≤ᵐ[ρ] Yhat ∧
        ∃ κ : Kernel ℝ ℝ, IsMarkovKernel κ ∧
          ρ.map (fun ω => (Yhat ω, Xhat ω)) = (ρ.map Yhat) ⊗ₘ κ ∧
          ∀ y₁ y₂ : ℝ, y₁ ≤ y₂ → ∀ t : ℝ, κ y₁ {x : ℝ | t < x} ≤ κ y₂ {x : ℝ | t < x} := by
  rw [CPL97ICV.icv_iff_icx, icx_submartingale_coupling_iff_v2 ν μ (-Y) (-X) hY.neg hX.neg
    hYint.neg hXint.neg]
  constructor
  · rintro ⟨Ω'', _, ρ, _, A, B, hA, hB, hAid, hBid, hce, κ, hκ, hmap, hmono⟩
    refine ⟨Ω'', inferInstance, ρ, inferInstance, -B, -A, hB.neg, hA.neg, ?_, ?_, ?_,
      CPL97ICV.negK κ, inferInstance, CPL97ICV.transfer_map ρ A B hA hB κ hmap,
      CPL97ICV.negK_mono κ hmono⟩
    · have := hBid.comp measurable_neg
      convert this using 1
      all_goals (funext ω; simp)
    · have := hAid.comp measurable_neg
      convert this using 1
      all_goals (funext ω; simp)
    · rw [CPL97ICV.comap_neg]
      filter_upwards [condExp_neg B (MeasurableSpace.comap A inferInstance), hce] with ω h1 h2
      rw [h1]
      simpa using h2
  · rintro ⟨Ω'', _, ρ, _, Xh, Yh, hXh, hYh, hXid, hYid, hce, κ, hκ, hmap, hmono⟩
    refine ⟨Ω'', inferInstance, ρ, inferInstance, -Yh, -Xh, hYh.neg, hXh.neg,
      hYid.comp measurable_neg, hXid.comp measurable_neg, ?_,
      CPL97ICV.negK κ, inferInstance, CPL97ICV.transfer_map ρ Yh Xh hYh hXh κ hmap,
      CPL97ICV.negK_mono κ hmono⟩
    rw [CPL97ICV.comap_neg]
    filter_upwards [condExp_neg Xh (MeasurableSpace.comap Yh inferInstance), hce] with ω h1 h2
    rw [h1]
    simpa using h2
