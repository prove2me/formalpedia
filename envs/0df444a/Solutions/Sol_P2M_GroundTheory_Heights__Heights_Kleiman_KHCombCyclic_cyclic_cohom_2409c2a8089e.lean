-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_cyclic_cohom_2409c2a8089e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:46.830484+00:00
-- url     : https://prove2.me/submissions/2efebe0f-112e-4a86-b936-28d42a49788f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombCyclicSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombCyclic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_cell_ext_28ea0425c440
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_contract_cocycle_0f3cdad47278

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
namespace GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
theorem _root_.solution (hC : KHCombContract.Statement) (J : ∀ k, Finset (ι k)) (n : ℕ)
    (hJ : ∀ k, J k = ∅ ∨ J k = Finset.univ) (f : CombC S J n) (hf : combD S J n f = 0) :
    ∃ s : S, f - s • singOne S J n ∈ combB S J n := by
  classical
  by_cases hcell : Nonempty (CombCell ι J n)
  swap
  · refine ⟨0, ?_⟩
    have : f - (0 : S) • singOne S J n = 0 := funext fun I => (hcell ⟨I⟩).elim
    rw [this]
    exact Submodule.zero_mem _
  obtain ⟨I₀⟩ := hcell
  let i₀ : ∀ k, ι k := fun k => (I₀.1.2.1 k).choose
  have key : ∀ T : Finset K, (∀ k ∈ T, J k = ∅) → ∃ φ : CombC S J n, combD S J n φ = 0 ∧
      f - φ ∈ combB S J n ∧ ∀ I : CombCell ι J n,
        ((∀ k ∈ T, (I.1.1 k).card = 1) → ∃ I' : CombCell ι J n, (∀ k ∈ T, I'.1.1 k = {i₀ k}) ∧
          (∀ l, l ∉ T → I'.1.1 l = I.1.1 l) ∧ φ I = f I') ∧
        (¬ (∀ k ∈ T, (I.1.1 k).card = 1) → φ I = 0) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨f, hf, by rw [sub_self]; exact Submodule.zero_mem _, fun I => ⟨fun _ => ⟨I, fun k hk =>
        absurd hk (Finset.notMem_empty k), fun _ _ => rfl, rfl⟩, fun h => absurd (fun k hk =>
        absurd hk (Finset.notMem_empty k)) h⟩⟩
    | insert k T hk ih =>
      intro hT
      obtain ⟨φ, hφ, hfφ, hφI⟩ := ih fun m hm => hT m (Finset.mem_insert_of_mem hm)
      have hJk : J k = ∅ := hT k (Finset.mem_insert_self k T)
      obtain ⟨g, hφg, hg⟩ := hC S K ι J n k (i₀ k) (by rw [hJk]; exact Finset.notMem_empty _) φ hφ
      refine ⟨g, contract_cocycle J n k (i₀ k) hJk φ g hφ (fun I h1 => (hg I).1 ⟨hJk, h1⟩)
        (fun I h1 => (hg I).2 fun h => h1 h.2), ?_, fun I => ⟨?_, ?_⟩⟩
      · have := Submodule.add_mem _ hfφ hφg
        rwa [sub_add_sub_cancel] at this
      · intro hI
        obtain ⟨I₁, hI₁k, hI₁o, hgI⟩ := (hg I).1 ⟨hJk, hI k (Finset.mem_insert_self k T)⟩
        have hne : ∀ m ∈ T, m ≠ k := fun m hm h => hk (h ▸ hm)
        have hI₁T : ∀ m ∈ T, (I₁.1.1 m).card = 1 := fun m hm => by
          rw [hI₁o m (hne m hm)]
          exact hI m (Finset.mem_insert_of_mem hm)
        obtain ⟨I', hI'T, hI'o, hφI₁⟩ := (hφI I₁).1 hI₁T
        refine ⟨I', fun m hm => ?_, fun l hl => ?_, hgI.trans hφI₁⟩
        · rcases Finset.mem_insert.mp hm with h | hm
          · rw [h, hI'o k hk, hI₁k]
          · exact hI'T m hm
        · have hlk : l ≠ k := fun h => hl (by rw [h]; exact Finset.mem_insert_self k T)
          rw [hI'o l (fun h => hl (Finset.mem_insert_of_mem h)), hI₁o l hlk]
      · intro hI
        by_cases h1 : (I.1.1 k).card = 1
        · obtain ⟨I₁, hI₁k, hI₁o, hgI⟩ := (hg I).1 ⟨hJk, h1⟩
          rw [hgI]
          refine (hφI I₁).2 fun hall => hI fun m hm => ?_
          rcases Finset.mem_insert.mp hm with h | hm
          · rw [h]; exact h1
          · rw [← hI₁o m (fun h => hk (h ▸ hm))]
            exact hall m hm
        · exact (hg I).2 fun h => h1 h.2
  obtain ⟨E, hE⟩ : ∃ E : Finset K, ∀ k, k ∈ E ↔ J k = ∅ :=
    ⟨Finset.univ.filter fun k => J k = ∅, fun k => by simp⟩
  obtain ⟨φ, -, hfφ, hφI⟩ := key E fun k hk => (hE k).mp hk
  have hval : ∀ I₁ I₂ : CombCell ι J n, (∀ k ∈ E, (I₁.1.1 k).card = 1) → (∀ k ∈ E, (I₂.1.1 k).card = 1) →
      φ I₁ = φ I₂ := by
    intro I₁ I₂ h₁ h₂
    obtain ⟨I₁', hk₁, ho₁, hφ₁⟩ := (hφI I₁).1 h₁
    obtain ⟨I₂', hk₂, ho₂, hφ₂⟩ := (hφI I₂).1 h₂
    have huniv : ∀ I : CombCell ι J n, ∀ l, l ∉ E → I.1.1 l = Finset.univ := fun I l hl => by
      have hJl : J l = Finset.univ := (hJ l).resolve_left fun h => hl ((hE l).mpr h)
      have := I.2 l
      rw [hJl] at this
      exact Finset.univ_subset_iff.mp this
    rw [hφ₁, hφ₂]
    refine congrArg f (cell_ext (funext fun l => ?_))
    by_cases hl : l ∈ E
    · rw [hk₁ l hl, hk₂ l hl]
    · rw [ho₁ l hl, ho₂ l hl, huniv I₁ l hl, huniv I₂ l hl]
  refine ⟨if h : ∃ I : CombCell ι J n, ∀ k ∈ E, (I.1.1 k).card = 1 then φ h.choose else 0, ?_⟩
  have hφs : φ = (if h : ∃ I : CombCell ι J n, ∀ k ∈ E, (I.1.1 k).card = 1 then φ h.choose else 0) •
      singOne S J n := by
    funext I
    simp only [Pi.smul_apply, singOne, smul_eq_mul]
    by_cases hI : ∀ k ∈ E, (I.1.1 k).card = 1
    · have h : ∃ I : CombCell ι J n, ∀ k ∈ E, (I.1.1 k).card = 1 := ⟨I, hI⟩
      rw [dif_pos h, if_pos (fun k hk => hI k ((hE k).mpr hk)), mul_one]
      exact hval I h.choose hI h.choose_spec
    · rw [if_neg (fun h => hI fun k hk => h k ((hE k).mp hk)), mul_zero]
      exact (hφI I).2 hI
  rw [← hφs]
  exact hfφ
end GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
