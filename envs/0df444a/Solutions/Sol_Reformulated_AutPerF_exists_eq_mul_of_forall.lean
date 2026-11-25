-- Prove2me | solution 1 for Reformulated.AutPerF.exists_eq_mul_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:31:11.86733+00:00
-- url     : https://prove2.me/submissions/b7e9686f-7402-4951-872f-21813f8b373c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Envelope
import Theorems.Thm_Reformulated_AutPerF_pow_dvd_dp
import Theorems.Thm_Reformulated_AutPerF_dpSpan_mono
import Theorems.Thm_Reformulated_AutPerF_dp_mem_dpSpan
import Theorems.Thm_Reformulated_AutPerF_natCast_mul_mem
import Theorems.Thm_Reformulated_AutPerF_exists_eq_of_mem_dpSpan
import Theorems.Thm_Reformulated_AutPerF_pow_dvd_of_mem_dpSpan
import Theorems.Thm_Reformulated_AutPerF_exists_mem_dpSpan_Ico
import Theorems.Thm_Reformulated_AutPerF_smul_dp_of_eq
import Theorems.Thm_Reformulated_AutPerF_dvd_of_pow_succ_dvd_smul_dp
import Theorems.Thm_Reformulated_AutPerF_mem_dpSpan_Ici
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap



set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
variable {B : Type*} [CommRing B] [Algebra ℚ B]
variable {A : Type*} [CommRing A] [Algebra A B]
variable {ξ : A}
variable [IsDomain B] (h0 : algebraMap A B ξ ≠ 0)
  (hξ : ∀ a : A, algebraMap A B ξ ∣ algebraMap A B a → ξ ∣ a)
include h0 hξ
namespace Reformulated.AutPerF
theorem _root_.solution {q : ℕ} (hq0 : 0 < q) (hq : IsUnit (q : B)) {x : B}
    (hx : x ∈ dpSpan B ξ Set.univ)
    (h : ∀ n, ∃ z ∈ dpSpan B ξ Set.univ, algebraMap A B ξ ^ n ∣ x - q * z) :
    ∃ z ∈ dpSpan B ξ Set.univ, x = q * z := by
  obtain ⟨M, hM⟩ := exists_mem_dpSpan_Ico hx
  have key : ∀ m ≤ q * M, ∃ z ∈ dpSpan B ξ Set.univ, x - q * z ∈ dpSpan B ξ (Set.Ico m (q * M)) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨0, zero_mem _, by
        simpa using dpSpan_mono (Set.Ico_subset_Ico_right (Nat.le_mul_of_pos_left M hq0)) hM⟩
    | succ m ih =>
      intro hm
      obtain ⟨z, hz, hz'⟩ := ih (by omega)
      obtain ⟨a, w, hw, e⟩ := exists_eq_of_mem_dpSpan (m := m) (t := Set.Ico (m + 1) (q * M))
        (fun k hk => by simp at hk ⊢; omega) hz'
      have hw' := pow_dvd_of_mem_dpSpan (n := m + 1) (fun _ hk => hk.1) hw
      obtain ⟨y, hy, hy'⟩ := h (m + 1)
      have h1 : algebraMap A B ξ ^ (m + 1) ∣ a • dp m (algebraMap A B ξ) - q * (y - z) := by
        have : a • dp m (algebraMap A B ξ) - q * (y - z) = (x - q * y) - w := by
          linear_combination -e
        rw [this]; exact dvd_sub hy' hw'
      have h2 : algebraMap A B ξ ^ m ∣ y - z := by
        have h3 : algebraMap A B ξ ^ m ∣ a • dp m (algebraMap A B ξ) := by
          rw [Algebra.smul_def]; exact (pow_dvd_dp le_rfl _).mul_left _
        have := dvd_sub h3 ((pow_dvd_pow _ m.le_succ).trans h1)
        rw [sub_sub_cancel] at this
        exact (hq.dvd_mul_left).1 this
      obtain ⟨c, v, hv, e2⟩ := exists_eq_of_mem_dpSpan (m := m) (t := Set.Ici (m + 1))
        (fun k hk => by simp at hk ⊢; omega) (mem_dpSpan_Ici h0 hξ (sub_mem hy hz) h2)
      have hv' := pow_dvd_of_mem_dpSpan (n := m + 1) (fun _ hk => hk) hv
      have h4 : algebraMap A B ξ ^ (m + 1) ∣ (a - q * c) • dp m (algebraMap A B ξ) := by
        have : (a - q * c) • dp m (algebraMap A B ξ) =
            (a • dp m (algebraMap A B ξ) - q * (y - z)) + q * v := by
          rw [e2]; simp only [Algebra.smul_def, map_sub, map_mul, map_natCast]; ring
        rw [this]; exact dvd_add h1 (hv'.mul_left _)
      obtain ⟨d, hd⟩ := dvd_of_pow_succ_dvd_smul_dp h0 hξ h4
      have e3 : x - q * (z + c • dp m (algebraMap A B ξ)) =
          ((m + 1 : ℕ) : B) * (d • dp (m + 1) (algebraMap A B ξ)) + w := by
        rw [← smul_dp_of_eq, ← hd]
        simp only [Algebra.smul_def, map_sub, map_mul, map_natCast] at e ⊢
        linear_combination e
      have hc : z + c • dp m (algebraMap A B ξ) ∈ dpSpan B ξ Set.univ :=
        add_mem hz (Submodule.smul_mem _ _ (dp_mem_dpSpan trivial))
      rcases hm.lt_or_eq with hlt | heq
      · refine ⟨_, hc, ?_⟩
        rw [e3]
        exact add_mem (natCast_mul_mem _ (Submodule.smul_mem _ _ (dp_mem_dpSpan ⟨le_rfl, hlt⟩))) hw
      · refine ⟨_, add_mem hc (natCast_mul_mem M (Submodule.smul_mem _ d
          (dp_mem_dpSpan (m := m + 1) trivial))), ?_⟩
        have : x - q * (z + c • dp m (algebraMap A B ξ) + M * d • dp (m + 1) (algebraMap A B ξ))
            = w := by
          rw [show ((m + 1 : ℕ) : B) = q * M by rw [heq]; push_cast; rfl] at e3
          linear_combination e3
        rw [this]; exact hw
  obtain ⟨z, hz, hz'⟩ := key _ le_rfl
  refine ⟨z, hz, sub_eq_zero.1 ?_⟩
  simpa [dpSpan] using hz'
end Reformulated.AutPerF
