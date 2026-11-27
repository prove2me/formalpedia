-- Prove2me | solution 1 for PositivityTheory.ThKG.Fub.tate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:22:18.799692+00:00
-- url     : https://prove2.me/submissions/bbb07694-a4b1-4c93-b0aa-81da327f8134

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_FubTate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Fub
open MeasureTheory Topology Filter
namespace PositivityTheory.ThKG.Fub
theorem _root_.solution {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (γ : Measure H) [γ.IsMulLeftInvariant] (o : H → ℤ) (ho : ∀ x y, o (x * y) = o x + o y) (hU : IsOpen {x | o x = 0})
    (h1 : γ {x | o x = 0} = 1) (ϖ : H) (hϖ : o ϖ = 1) (χ : H →* ℂ) (hχ : ∀ x, o x = 0 → χ x = 1) (ht : ‖χ ϖ‖ < 1) (m : ℤ) :
    Integrable (fun x => (if m ≤ o x then (1 : ℂ) else 0) * χ x) γ ∧
      ∫ x, (if m ≤ o x then (1 : ℂ) else 0) * χ x ∂γ = χ ϖ ^ m * (1 - χ ϖ)⁻¹ := by
  let O : H →* Multiplicative ℤ := MonoidHom.mk' (fun x => Multiplicative.ofAdd (o x)) fun x y => by rw [ho]; rfl
  have oz : ∀ (k : ℤ) x, o (ϖ ^ k * x) = k + o x := fun k x => by
    have := map_zpow O ϖ k
    have h2 : o (ϖ ^ k) = k := by
      have h3 := congrArg Multiplicative.toAdd this
      simpa [O, hϖ] using h3
    rw [ho, h2]
  have h0 : χ ϖ ≠ 0 := fun e => by
    have := map_mul χ ϖ ϖ⁻¹
    rw [mul_inv_cancel, map_one, e, zero_mul] at this
    exact one_ne_zero this
  let A : ℕ → Set H := fun k => {x | o x = m + k}
  have hA : ∀ k, A k = (fun x => ϖ ^ (-(m + k)) * x) ⁻¹' {x | o x = 0} := fun k => Set.ext fun x => by
    simp only [A, Set.mem_setOf_eq, Set.mem_preimage, oz]; omega
  have mA : ∀ k, MeasurableSet (A k) := fun k => by
    rw [hA]; exact (hU.preimage (continuous_const.mul continuous_id)).measurableSet
  have vA : ∀ k, γ (A k) = 1 := fun k => by rw [hA, measure_preimage_mul, h1]
  have cA : ∀ k, ∀ x ∈ A k, χ x = χ ϖ ^ m * χ ϖ ^ k := fun k x hx => by
    have := hχ _ ((hA k ▸ hx : x ∈ (fun x => ϖ ^ (-(m + k)) * x) ⁻¹' {x | o x = 0}))
    rw [map_mul, map_zpow, zpow_neg, inv_mul_eq_one₀ (zpow_ne_zero _ h0)] at this
    rw [← this, zpow_add₀ h0, zpow_natCast]
  have dA : Pairwise (Function.onFun Disjoint A) := fun i j hij => Set.disjoint_left.2 fun x h h' => hij (by
    simp only [A, Set.mem_setOf_eq] at h h'; omega)
  have eU : (fun x => (if m ≤ o x then (1 : ℂ) else 0) * χ x) = (⋃ k, A k).indicator χ := funext fun x => by
    by_cases h : m ≤ o x
    · rw [if_pos h, one_mul, Set.indicator_of_mem (Set.mem_iUnion.2 ⟨(o x - m).toNat, by simp only [A, Set.mem_setOf_eq]; omega⟩)]
    · rw [if_neg h, zero_mul, Set.indicator_of_notMem fun h' => by
        obtain ⟨k, hk⟩ := Set.mem_iUnion.1 h'
        simp only [A, Set.mem_setOf_eq] at hk; omega]
  have iA : ∀ k, IntegrableOn χ (A k) γ := fun k =>
    (integrableOn_const (C := χ ϖ ^ m * χ ϖ ^ k) (by rw [vA]; simp)).congr_fun (fun x hx => (cA k x hx).symm) (mA k)
  have sA : ∀ k, ∫ x in A k, χ x ∂γ = χ ϖ ^ m * χ ϖ ^ k := fun k => by
    rw [setIntegral_congr_fun (mA k) (cA k), setIntegral_const, Measure.real, vA]; simp
  have nA : ∀ k, ∫ x in A k, ‖χ x‖ ∂γ = ‖χ ϖ ^ m‖ * ‖χ ϖ‖ ^ k := fun k => by
    rw [setIntegral_congr_fun (mA k) (g := fun _ => ‖χ ϖ ^ m‖ * ‖χ ϖ‖ ^ k) fun x hx => by simp only [cA k x hx, norm_mul, norm_pow],
      setIntegral_const, Measure.real, vA]; simp
  have iU : IntegrableOn χ (⋃ k, A k) γ := integrableOn_iUnion_of_summable_integral_norm iA (by
    simp only [nA]; exact (summable_geometric_of_lt_one (norm_nonneg _) ht).mul_left _)
  rw [eU, integrable_indicator_iff (MeasurableSet.iUnion mA), integral_indicator (MeasurableSet.iUnion mA)]
  refine ⟨iU, (hasSum_integral_iUnion mA dA iU).unique ?_⟩
  simp only [sA]
  exact (hasSum_geometric_of_norm_lt_one ht).mul_left _
end PositivityTheory.ThKG.Fub
