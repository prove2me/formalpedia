-- Prove2me | solution 1 for OddOrder.Isaacs.Ch05.APrime_index_isPGroup
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:30:03.382817+00:00
-- url     : https://prove2.me/submissions/ded6c89f-0b0d-4866-8fc9-bcf4cada1319

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch05_Transfer/Basic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_CyclicSubgroupUniqueness
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Main
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Basic
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Focal
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.SpecificGroups.ZGroup

-- ===== OddOrder/Isaacs/Ch05_Transfer/Basic.lean =====
open scoped commutatorElement

open scoped IsMulCommutative

namespace OddOrder.Isaacs.Ch05

open Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

section

/-- For finite `G`, `APrime p G` has `p`-power index (same proof as `OPrime_index_isPGroup`,
since the family is closed under `⊓` and each member has `p`-power index). -/
theorem _root_.solution (p : ℕ) (G : Type*) [Group G] [Finite G] [Fact p.Prime] :
    ∃ k : ℕ, (APrime p G).index = p ^ k := by
  classical
  let ι : Type _ :=
    {K : Subgroup G // K.Normal ∧ commutator G ≤ K ∧ ∃ k : ℕ, K.index = p ^ k}
  have : Finite ι := Subtype.finite
  have : Fintype ι := Fintype.ofFinite ι
  let φ : G →* (∀ i : ι, G ⧸ (i.val : Subgroup G)) :=
    MonoidHom.pi fun i : ι => QuotientGroup.mk' i.val
  have h_ker : φ.ker = APrime p G := by
    ext g
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [APrime, Subgroup.mem_iInf]
      intro i
      have hg_i : φ g i = (1 : G ⧸ (i.val : Subgroup G)) := by
        rw [MonoidHom.mem_ker] at h; exact congrFun h i
      simpa [φ, MonoidHom.pi_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] using hg_i
    · rw [MonoidHom.mem_ker]
      ext i
      simp only [φ, MonoidHom.pi_apply, QuotientGroup.mk'_apply, Pi.one_apply,
        QuotientGroup.eq_one_iff]
      rw [APrime, Subgroup.mem_iInf] at h
      exact h i
  have : Finite (∀ i : ι, G ⧸ (i.val : Subgroup G)) := Pi.finite
  have h_card_range : Nat.card φ.range ∣ Nat.card (∀ i : ι, G ⧸ (i.val : Subgroup G)) :=
    Subgroup.card_subgroup_dvd_card _
  have h_card_quot : Nat.card (G ⧸ APrime p G) = Nat.card φ.range := by
    rw [← h_ker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have h_card_pi : Nat.card (∀ i : ι, G ⧸ (i.val : Subgroup G)) = ∏ i : ι, i.val.index := by
    rw [Nat.card_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Subgroup.index_eq_card]
  let k_fun : ι → ℕ := fun i => Classical.choose i.property.2.2
  have hk_fun : ∀ i : ι, i.val.index = p ^ k_fun i :=
    fun i => Classical.choose_spec i.property.2.2
  have h_prod_pow : (∏ i : ι, i.val.index) = p ^ (∑ i : ι, k_fun i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i _ => hk_fun i
  have h_idx_dvd : (APrime p G).index ∣ p ^ (∑ i : ι, k_fun i) := by
    rw [Subgroup.index_eq_card, h_card_quot]
    calc Nat.card φ.range
        ∣ Nat.card (∀ i : ι, G ⧸ (i.val : Subgroup G)) := h_card_range
      _ = ∏ i : ι, i.val.index := h_card_pi
      _ = p ^ (∑ i : ι, k_fun i) := h_prod_pow
  obtain ⟨a, _, ha⟩ := (Nat.dvd_prime_pow Fact.out).mp h_idx_dvd
  exact ⟨a, ha⟩

end

end OddOrder.Isaacs.Ch05
