-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.card_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:13:16.477209+00:00
-- url     : https://prove2.me/submissions/7f502fd6-2ac2-436b-9077-fc904c8cb5da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedHalf
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedCardG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CardG_card_ker
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CardG_mem_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CardG_co_spec
import Theorems.Thm_Formalism_L2_Th1_F_Cm1_mem_iff
import Theorems.Thm_Formalism_L2_Th1_F_Ker_matrix_data


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open CardG
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (L : PeriodPair) (β : ℂ) (hβ : MulStable L β) (p M : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : Complex.normSq β = ((p * M : ℕ) : ℝ)) (hM : ¬ p ∣ M) (T : Finset ℂ)
    (hT : IsHalfReps L (p : ℂ) T) :
    2 * (T.filter (fun P => β * P ∈ L.lattice)).card + 1 = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨hS1, hS2, hS3⟩, hdisj⟩ := hT.kerReps
  obtain ⟨a, b, c, d, h1, h2, -, hn⟩ := Ker.matrix_data L β hβ
  have hpc : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hdetZ : a * d - b * c = (p : ℤ) * M := by
    have : ((a * d - b * c : ℤ) : ℝ) = (((p : ℤ) * M : ℤ) : ℝ) := by
      rw [← hn, hN]; push_cast; ring
    exact_mod_cast this
  have hdet : (a : ZMod p) * d - b * c = 0 := by
    have := congrArg (fun k : ℤ => (k : ZMod p)) hdetZ
    simpa using this
  have hne : ¬ ((a : ZMod p) = 0 ∧ (b : ZMod p) = 0 ∧ (c : ZMod p) = 0 ∧ (d : ZMod p) = 0) := by
    simp only [ZMod.intCast_zmod_eq_zero_iff_dvd]
    rintro ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩, ⟨d', rfl⟩⟩
    apply hM
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have : (M : ℤ) = p * (a' * d' - b' * c') := by
      apply mul_left_cancel₀ hp0
      rw [← hdetZ]; ring
    exact Int.natCast_dvd_natCast.mp ⟨_, this⟩

  have hmul : ∀ {z : ℂ} {m n : ℤ}, (m : ℂ) * L.ω₁ + n * L.ω₂ = p * z →
      (β * z ∈ L.lattice ↔ (a : ZMod p) * m + b * n = 0 ∧ (c : ZMod p) * m + d * n = 0) := by
    intro z m n e
    have := mem_iff L p hp.ne_zero (z := β * z) (m := a * m + b * n) (n := c * m + d * n) (by
      push_cast
      linear_combination β * e - (m : ℂ) * h1 - (n : ℂ) * h2)
    rw [this]; push_cast; rfl
  set S := T ∪ T.image (fun P => -P) with hSdef
  set K := Finset.univ.filter (fun w : ZMod p × ZMod p =>
    (a : ZMod p) * w.1 + b * w.2 = 0 ∧ (c : ZMod p) * w.1 + d * w.2 = 0) with hK
  have hKcard : K.card = p := by
    have := card_ker (a : ZMod p) b c d hdet hne
    rw [ZMod.card] at this
    rw [hK]
    convert this
  have h0K : (0 : ZMod p × ZMod p) ∈ K := by simp [hK]
  have hcardS : (S.filter (fun P => β * P ∈ L.lattice)).card
      = 2 * (T.filter (fun P => β * P ∈ L.lattice)).card := by
    have himg : (T.image (fun P => -P)).filter (fun P => β * P ∈ L.lattice)
        = (T.filter (fun P => β * P ∈ L.lattice)).image (fun P => -P) := by
      ext Q
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨P, hP, rfl⟩, hQ⟩
        refine ⟨P, ⟨hP, ?_⟩, rfl⟩
        have := neg_mem hQ
        simpa using this
      · rintro ⟨P, ⟨hP, hQ⟩, rfl⟩
        refine ⟨⟨P, hP, rfl⟩, ?_⟩
        have := neg_mem hQ
        simpa using this
    rw [hSdef, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj), himg,
      Finset.card_image_of_injective _ neg_injective]
    ring
  have hbij : (S.filter (fun P => β * P ∈ L.lattice)).card = (K.erase 0).card := by
    apply Finset.card_nbij
      (fun z => (((co L (p * z)).1 : ZMod p), ((co L (p * z)).2 : ZMod p)))
    · intro P hP
      obtain ⟨hPS, hPβ⟩ := Finset.mem_filter.mp hP
      have e := co_spec L (hS1 P hPS).1
      rw [Finset.mem_coe, Finset.mem_erase]
      constructor
      · intro h0
        apply (hS1 P hPS).2
        rw [mem_iff L p hp.ne_zero e]
        exact Prod.mk.inj h0
      · rw [hK, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (hmul e).mp hPβ⟩
    · intro P hP Q hQ hPQ
      have hPS := (Finset.mem_filter.mp (Finset.mem_coe.mp hP)).1
      have hQS := (Finset.mem_filter.mp (Finset.mem_coe.mp hQ)).1
      have eP := co_spec L (hS1 P hPS).1
      have eQ := co_spec L (hS1 Q hQS).1
      apply hS2 P hPS Q hQS
      rw [mem_iff L p hp.ne_zero (m := (co L (p * P)).1 - (co L (p * Q)).1)
        (n := (co L (p * P)).2 - (co L (p * Q)).2) (by push_cast; linear_combination eP - eQ)]
      obtain ⟨e1, e2⟩ := Prod.mk.inj hPQ
      push_cast
      exact ⟨sub_eq_zero.mpr e1, sub_eq_zero.mpr e2⟩
    · rintro ⟨x, y⟩ hxy
      obtain ⟨hxy0, hxyK⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp hxy)
      obtain ⟨m, rfl⟩ := ZMod.intCast_surjective x
      obtain ⟨n, rfl⟩ := ZMod.intCast_surjective y
      set z : ℂ := ((m : ℂ) * L.ω₁ + n * L.ω₂) / p with hz
      have ez : (m : ℂ) * L.ω₁ + n * L.ω₂ = p * z := by rw [hz]; field_simp
      have hzp : (p : ℂ) * z ∈ L.lattice := PeriodPair.mem_lattice.mpr ⟨m, n, ez⟩
      have hzL : z ∉ L.lattice := by
        rw [mem_iff L p hp.ne_zero ez]
        rintro ⟨e1, e2⟩
        exact hxy0 (by rw [e1, e2]; rfl)
      have hzβ : β * z ∈ L.lattice := (hmul ez).mpr (Finset.mem_filter.mp hxyK).2
      obtain ⟨P, hPS, hzP⟩ := hS3 z hzp hzL
      have eP := co_spec L (hS1 P hPS).1
      refine ⟨P, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hPS, ?_⟩), ?_⟩
      · have : β * P = β * z - β * (z - P) := by ring
        rw [this]
        exact sub_mem hzβ (hβ _ hzP)
      · have := (mem_iff L p hp.ne_zero (m := m - (co L (p * P)).1)
          (n := n - (co L (p * P)).2) (by push_cast; linear_combination ez - eP)).mp hzP
        push_cast at this
        exact Prod.ext (sub_eq_zero.mp this.1).symm (sub_eq_zero.mp this.2).symm
  rw [← hcardS, hbij, Finset.card_erase_of_mem h0K, hKcard]
  have := hp.pos
  omega
end ReciprocityTheory.ChartRestriction.L1
