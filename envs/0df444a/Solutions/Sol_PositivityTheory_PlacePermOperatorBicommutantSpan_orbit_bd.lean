-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.orbit_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:31:45.045221+00:00
-- url     : https://prove2.me/submissions/441d908d-481e-4b14-9e47-efa2a6ebb7db

import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_SqPosOfNe
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_CO_inf
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_co_perp
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_ind_add
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_ind_of_mem
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_ind_of_not
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_sb_ind
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_sb_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set Matrix
open scoped ENNReal ComplexConjugate MatrixGroups
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι]
variable [TopologicalSpace R] [MeasurableSpace R] {ψ : AddChar R ℂ} {h : R} {B : Matrix ι ι R} {μ : Measure (ι → R)}
variable (H : NAQuad ψ h B μ)
include H
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (O : Set R) {L : AddSubgroup (ι → R)} (hL : CO L) (hst : ∀ a ∈ O, ∀ x ∈ L, a • x ∈ L)
    {φ : (ι → R) → ℂ} (hφ : SB φ) (hfix : ∀ x ∈ L, ∀ y ∈ L, Heisenberg₂ ψ h B x y φ = φ) :
    ∃ (L' : AddSubgroup (ι → R)) (s : Finset (ι → R)) (C : ℝ), CO L' ∧ ∀ k : SL(2, R), (∀ i j, k i j ∈ O) →
      ∀ T, Impl ψ h B μ k T → (∀ u, ‖T φ u‖ ≤ C) ∧ ∃ c : (ι → R) → ℂ, (∀ a, ‖c a‖ ≤ C) ∧ T φ = ∑ a ∈ s, c a • ind a L' := by
  have hD := H.2.2.2.2.2
  have hh := hD
  obtain ⟨_, _, _, _, _, _, -⟩ := hh
  have hP := co_perp hD hL
  have hL' := hL.inf hP.2
  obtain ⟨s, hs⟩ := sb_span (sb_ind 0 hP) hL'.2 fun x l hl => ind_add x hl.2
  have hpos : 0 < μ.real L := ENNReal.toReal_pos (hL.2.measure_ne_zero μ ⟨0, L.zero_mem⟩) hL.1.measure_lt_top.ne
  refine ⟨_, s, Real.sqrt ((∫ u, ‖φ u‖ ^ 2 ∂μ) / μ.real L), hL', fun k hk T hT => ?_⟩
  have hfT : ∀ x ∈ L, ∀ y ∈ L, Heisenberg₂ ψ h B x y (T φ) = T φ := fun x hx y hy => by
    rw [hT.2.2.2.2.2 x y φ hφ, hfix _ (L.add_mem (hst _ (hk _ _) _ hx) (hst _ (hk _ _) _ hy)) _
      (L.add_mem (hst _ (hk _ _) _ hx) (hst _ (hk _ _) _ hy))]
  have hinv : ∀ u, ∀ l ∈ L, T φ (u + l) = T φ u := fun u l hl => by
    simpa [Heisenberg₂] using congrFun (hfT l hl 0 L.zero_mem) u
  have hsupp : ∀ u, u ∉ perpG hD L → T φ u = 0 := fun u hu => by
    by_contra hne
    refine hu fun y hy => ?_
    have := congrFun (hfT 0 L.zero_mem y hy) u
    simp only [Heisenberg₂, zero_dotProduct, mul_zero, add_zero] at this
    rw [chi_sym hD]
    exact mul_right_cancel₀ hne (this.trans (one_mul _).symm)
  have hTs := hT.1 φ hφ
  have hbd : ∀ u, ‖T φ u‖ ≤ Real.sqrt ((∫ u, ‖φ u‖ ^ 2 ∂μ) / μ.real L) := fun u => by
    refine Real.le_sqrt_of_sq_le ?_
    rw [le_div_iff₀ hpos, ← hT.2.2.2.2.1 φ hφ, ← integral_add_left_eq_self _ u, mul_comm, ← smul_eq_mul,
      ← integral_indicator_const _ hL.2.measurableSet]
    have hc : Continuous fun v => ‖T φ v‖ ^ 2 := hTs.1.continuous.norm.pow 2
    refine integral_mono_of_nonneg (ae_of_all _ fun v => Set.indicator_nonneg (fun _ _ => sq_nonneg _) v)
      ((hc.integrable_of_hasCompactSupport (hTs.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))).comp_add_left u)
      (ae_of_all _ fun v => ?_)
    by_cases hv : v ∈ L
    · simp only [Set.indicator_of_mem (s := (L : Set (ι → R))) hv, hinv u v hv, le_refl]
    · simp only [Set.indicator_of_notMem (s := (L : Set (ι → R))) hv, sq_nonneg]
  refine ⟨hbd, fun a => ind 0 (perpG hD L) a * T φ a, fun a => ?_, funext fun u => ?_⟩
  · rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hbd a)
    by_cases ha : a - 0 ∈ perpG hD L
    · rw [ind_of_mem ha, norm_one]
    · rw [ind_of_not ha, norm_zero]; exact zero_le_one
  · have e : T φ u = ind 0 (perpG hD L) u * T φ u := by
      by_cases hu : u ∈ perpG hD L
      · rw [ind_of_mem (by simpa using hu), one_mul]
      · rw [hsupp u hu, mul_zero]
    rw [e, congrFun hs u]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : u - a ∈ L ⊓ perpG hD L
    · have := hinv a _ ha.1
      rw [add_sub_cancel] at this
      rw [this]; ring
    · rw [ind_of_not ha]; ring
end PositivityTheory.PlacePermOperatorBicommutantSpan
