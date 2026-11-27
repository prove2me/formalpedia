-- Prove2me | solution 1 for UpperTheory.Ram.Fun.sum_ceil_off_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:33:37.334001+00:00
-- url     : https://prove2.me/submissions/57073cdc-0a51-401b-a7c0-e0644196c31d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_VpBounds
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FunKit
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FunDen
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ClassZetaValuationBounds_ToricDenominatorLevel_exact
import Theorems.Thm_UpperTheory_Ram_Fun_sum_ceil_nl_le
import Theorems.Thm_UpperTheory_Ram_Fun_sum_delta_log_le
import Theorems.Thm_UpperTheory_Ram_Fun_sum_log_le_of_dvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain Finset
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (betaBound_vp cE_vp n_vp c_vp a0 delta_vp)
noncomputable section
open UpperTheory UpperTheory.Ram UpperTheory.Ram.Fun
namespace UpperTheory.Ram.Fun
theorem _root_.solution {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ)
    (𝔣 : Ideal (GlobalTheory.CMVal.OF E)) (z : ClassGroup (GlobalTheory.CMVal.OF E) → ℚ) (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime)
    (ha : ∀ l ∈ S, a0 𝔣 l = 0) {N : ℕ} (hN : N ≠ 0) (hd : ∀ l : ℕ, l.Prime → (l : ℤ) ∣ discr E → l ∣ N) {A : ℝ}
    (h1 : Real.log (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ≤ A) (h2 : Real.log N ≤ A) :
    ∑ l ∈ S, ((⌈betaBound_vp d s κ 𝔣 z l / 12⌉₊ : ℕ) : ℝ) * Real.log l ≤ ∑ l ∈ S, (cE_vp l z : ℝ) * Real.log l +
      (((2 * s * Fintype.card I : ℕ) : ℝ) + 5 * (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) + 1) * A := by
  classical
  have hK0 : (0 : ℝ) ≤ ((2 * s * Fintype.card I : ℕ) : ℝ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) := Nat.cast_nonneg _
  have hA : 0 ≤ A := le_trans (Real.log_natCast_nonneg N) h2
  have hlog : ∀ l ∈ S, 0 ≤ Real.log (l : ℝ) := fun l hl =>
    Real.log_nonneg (by exact_mod_cast (hS l hl).one_lt.le)
  have hdl : ∀ l, 0 ≤ delta_vp E l := by
    intro l
    unfold delta_vp
    positivity
  have hc0 : ∀ l, 0 ≤ c_vp 𝔣 l := by
    intro l
    unfold c_vp
    split_ifs
    · positivity
    · exact hdl l
  have hcle : ∀ l ∈ S, c_vp 𝔣 l ≤ delta_vp E l := by
    intro l hl
    unfold c_vp
    split_ifs
    · rw [ha l hl]
      simpa using hdl l
    · exact le_rfl
  have ht : ∀ l : ℕ, ((if l = 2 then (1 : ℝ) else 0) + if l = d then (1 / 2 : ℝ) else 0) ≤ 3 / 2 := by
    intro l
    split_ifs <;> norm_num
  have hn_eq : ∀ l, n_vp d s κ 𝔣 l = 0 ∨ n_vp d s κ 𝔣 l =
      ((2 * s * Fintype.card I : ℕ) : ℝ) * c_vp 𝔣 l + (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) *
        (2 * c_vp 𝔣 l + 1 + ((if l = 2 then (1 : ℝ) else 0) + if l = d then (1 / 2 : ℝ) else 0)) := by
    intro l
    by_cases h : c_vp 𝔣 l = 0
    · left
      unfold n_vp
      rw [if_pos h]
    · right
      unfold n_vp
      rw [if_neg h]
      rfl
  have hn0 : ∀ l, 0 ≤ n_vp d s κ 𝔣 l := by
    intro l
    rcases hn_eq l with h | h
    · rw [h]
    · rw [h]
      have h1 := mul_nonneg hK0 (hc0 l)
      have h3 : (0 : ℝ) ≤ (if l = 2 then (1 : ℝ) else 0) + if l = d then (1 / 2 : ℝ) else 0 := by
        split_ifs <;> norm_num
      have h2 := mul_nonneg hk0 (by linarith [hc0 l] : (0 : ℝ) ≤ 2 * c_vp 𝔣 l + 1 +
        ((if l = 2 then (1 : ℝ) else 0) + if l = d then (1 / 2 : ℝ) else 0))
      linarith
  have hceil : ∀ l ∈ S, ((⌈betaBound_vp d s κ 𝔣 z l / 12⌉₊ : ℕ) : ℝ) =
      (cE_vp l z : ℝ) + (⌈n_vp d s κ 𝔣 l⌉₊ : ℝ) := by
    intro l hl
    have e : betaBound_vp d s κ 𝔣 z l / 12 = n_vp d s κ 𝔣 l + ((cE_vp l z : ℕ) : ℝ) := by
      unfold betaBound_vp
      rw [ha l hl]
      push_cast
      ring
    rw [e, Nat.ceil_add_natCast (hn0 l)]
    push_cast
    ring
  have hsplit : ∑ l ∈ S, ((⌈n_vp d s κ 𝔣 l⌉₊ : ℕ) : ℝ) * Real.log l =
      ∑ l ∈ S.filter (fun l => c_vp 𝔣 l ≠ 0), ((⌈n_vp d s κ 𝔣 l⌉₊ : ℕ) : ℝ) * Real.log l := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro l _
    split_ifs with h
    · rfl
    · have h0 : n_vp d s κ 𝔣 l = 0 := by
        unfold n_vp
        rw [if_pos (not_not.mp h)]
      simp [h0]
  have hsubS : S.filter (fun l => c_vp 𝔣 l ≠ 0) ⊆ S := Finset.filter_subset _ _
  have hcA : ∑ l ∈ S.filter (fun l => c_vp 𝔣 l ≠ 0), c_vp 𝔣 l * Real.log l ≤ A := by
    calc ∑ l ∈ S.filter (fun l => c_vp 𝔣 l ≠ 0), c_vp 𝔣 l * Real.log l
        ≤ ∑ l ∈ S, c_vp 𝔣 l * Real.log l := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubS
          intro l hl _
          exact mul_nonneg (hc0 l) (hlog l hl)
      _ ≤ ∑ l ∈ S, delta_vp E l * Real.log l := by
          apply Finset.sum_le_sum
          intro l hl
          exact mul_le_mul_of_nonneg_right (hcle l hl) (hlog l hl)
      _ ≤ Real.log (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) := by
          have := sum_delta_log_le E S hS
          simpa [delta_vp] using this
      _ ≤ A := h1
  have hlA : ∑ l ∈ S.filter (fun l => c_vp 𝔣 l ≠ 0), Real.log (l : ℝ) ≤ A := by
    refine le_trans (sum_log_le_of_dvd hN _ ?_) h2
    intro l hl
    rw [Finset.mem_filter] at hl
    obtain ⟨hlS, hne⟩ := hl
    refine ⟨hS l hlS, ?_⟩
    apply hd l (hS l hlS)
    by_contra hnd
    apply hne
    unfold c_vp
    split_ifs
    · rw [ha l hlS]
      simp
    · unfold delta_vp
      haveI : Fact l.Prime := ⟨hS l hlS⟩
      rw [padicValInt.eq_zero_of_not_dvd hnd]
      simp
  have hmain := sum_ceil_nl_le (S.filter (fun l => c_vp 𝔣 l ≠ 0)) (n_vp d s κ 𝔣) (c_vp 𝔣)
    (fun l => (if l = 2 then (1 : ℝ) else 0) + if l = d then (1 / 2 : ℝ) else 0)
    hK0 hk0 (fun l _ => hc0 l) (fun l _ => ht l)
    (fun l _ => hn0 l) (fun l _ => hn_eq l) hcA hlA
  calc ∑ l ∈ S, ((⌈betaBound_vp d s κ 𝔣 z l / 12⌉₊ : ℕ) : ℝ) * Real.log l
      = ∑ l ∈ S, (cE_vp l z : ℝ) * Real.log l +
          ∑ l ∈ S, ((⌈n_vp d s κ 𝔣 l⌉₊ : ℕ) : ℝ) * Real.log l := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro l hl
        rw [hceil l hl]
        ring
    _ ≤ ∑ l ∈ S, (cE_vp l z : ℝ) * Real.log l +
          (((2 * s * Fintype.card I : ℕ) : ℝ) + 5 * (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) + 1) * A := by
        rw [hsplit]
        have hkA := mul_nonneg hk0 hA
        nlinarith [hmain]
end UpperTheory.Ram.Fun
