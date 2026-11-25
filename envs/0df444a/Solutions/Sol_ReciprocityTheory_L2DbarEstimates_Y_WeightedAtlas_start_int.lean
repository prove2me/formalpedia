-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.start_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:41:36.783432+00:00
-- url     : https://prove2.me/submissions/57313e95-7884-44ac-80f8-6251afa919ed

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZLocLower
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_SetLIntegralBiUnionLe
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_sqn_pos_of_ne
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_sqn_pos_of_notMem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_setLIntegral_biUnion_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_local_int
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_nsq_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution (A : WeightedAtlas n Y ι La) (hMVI : MVIntStatement n) (hn : 2 ≤ n) {L : La}
    {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ}
    (hD : A.D0 L w w0 s) {la : La} {f : ι → Y → ℂ} (hf : A.IsSec la f) {T : ℕ}
    (hT : n + 1 ≤ T)
    (hint : ∫⁻ y, ENNReal.ofReal (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) ∂A.mu < ⊤)
    (hvan : ∀ P ∈ A.zeroSet s, A.VanishOrd f P (T - n)) :
    ∫⁻ y, ENNReal.ofReal (A.nsq la f y * A.sqn L s y ^ (-((T : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤ := by
  classical
  set G : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (A.nsq la f y * A.sqn L s y ^ (-((T : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) with hG
  have hloc : ∀ P ∈ A.zeroSet s, ∃ U : Set Y, IsOpen U ∧ P ∈ U ∧ ∫⁻ y in U, G y ∂A.mu < ⊤ :=
    fun P hP => A.local_int hMVI hn hD hf hT hP (hvan P hP)
  choose! U hUo hPU hUint using hloc
  set F := hD.finite_S.toFinset
  set V := ⋃ P ∈ F, U P with hV
  have hVo : IsOpen V := isOpen_biUnion (fun P hP => hUo P ((Set.Finite.mem_toFinset _).1 hP))
  have hSV : A.zeroSet s ⊆ V := fun P hP =>
    Set.mem_biUnion ((Set.Finite.mem_toFinset _).2 hP) (hPU P hP)
  obtain ⟨C, hC⟩ := hD.family_le_coords V hVo hSV
  set a : ℝ := (T : ℝ) - 1 / 2 with ha
  have hpt : ∀ y ∈ Vᶜ, G y ≤ ENNReal.ofReal (C ^ a) *
      ENNReal.ofReal (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) := by
    intro y hy
    have hyS : y ∉ A.zeroSet s := fun h => hy (hSV h)
    have hs := A.sqn_pos_of_notMem (la := L) hyS
    have hw := A.sqn_pos_of_ne (la := L) (hD.no_common_zero y)
    have hCy := hC y hy
    have hCpos : 0 < C := by
      by_contra hc
      have hc' := not_lt.1 hc
      nlinarith
    have h1 : A.sqn L s y ^ (-a) ≤ (A.sqn L w y / C) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by rw [div_le_iff₀ hCpos]; linarith)
        (by have : (1:ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
            linarith)
    have h2 : (A.sqn L w y / C) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ)) =
        C ^ a * A.sqn L w y ^ (-(T : ℝ)) := by
      rw [Real.div_rpow hw.le hCpos.le, Real.rpow_neg hCpos.le, div_inv_eq_mul, mul_comm _ (C ^ a),
        mul_assoc, ← Real.rpow_add hw]
      congr 2
      ring
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn0 := A.nsq_nonneg la f y
    calc A.nsq la f y * A.sqn L s y ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))
        ≤ A.nsq la f y * (A.sqn L w y / C) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ)) := by
          have := Real.rpow_nonneg hw.le (-(1 / 2 : ℝ))
          gcongr
      _ = C ^ a * (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) := by
          rw [mul_assoc, h2]; ring
  calc ∫⁻ y, G y ∂A.mu = ∫⁻ y in V ∪ Vᶜ, G y ∂A.mu := by
        rw [Set.union_compl_self, Measure.restrict_univ]
    _ ≤ ∫⁻ y in V, G y ∂A.mu + ∫⁻ y in Vᶜ, G y ∂A.mu := lintegral_union_le _ _ _
    _ ≤ ∑ P ∈ F, ∫⁻ y in U P, G y ∂A.mu + ∫⁻ y in Vᶜ, ENNReal.ofReal (C ^ a) *
          ENNReal.ofReal (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) ∂A.mu :=
        add_le_add (setLIntegral_biUnion_le _ _ _ _) (setLIntegral_mono' hVo.measurableSet.compl hpt)
    _ ≤ ∑ P ∈ F, ∫⁻ y in U P, G y ∂A.mu + ∫⁻ y, ENNReal.ofReal (C ^ a) *
          ENNReal.ofReal (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) ∂A.mu :=
        add_le_add le_rfl (setLIntegral_le_lintegral _ _)
    _ < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine ENNReal.add_lt_top.2 ⟨ENNReal.sum_lt_top.2 (fun P hP => hUint P
          ((Set.Finite.mem_toFinset _).1 hP)), ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint⟩
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
