-- Prove2me | solution 1 for TokenComplexity.Tradeoff.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T14:32:37.558428+00:00
-- url     : https://prove2.me/submissions/aba0c446-028a-435c-80ae-2ab1a98919c9

import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_TokenComplexity_Tradeoff_Model
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace TokenComplexity.Selection

/-- Among subsets of a prescribed size, one has least total cost. If all costs
are distinct, every such minimum contains every cheaper available item. -/
theorem minimum_downward_subset {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (c : ι → ℕ) (hc : Set.InjOn c (↑F : Set ι))
    (m : ℕ) (hm : m ≤ F.card) :
    ∃ S : Finset ι, S ⊆ F ∧ S.card = m ∧
      (∀ i ∈ S, ∀ j ∈ F, c j ≤ c i → j ∈ S) ∧
      (∀ R : Finset ι, R ⊆ F → R.card = m →
        (∑ i ∈ S, c i) ≤ ∑ i ∈ R, c i) := by
  classical
  obtain ⟨R, hRF, hRm⟩ := Finset.exists_subset_card_eq hm
  have hnonempty : (F.powersetCard m).Nonempty :=
    ⟨R, Finset.mem_powersetCard.mpr ⟨hRF, hRm⟩⟩
  obtain ⟨S, hS, hmin⟩ :=
    Finset.exists_min_image (F.powersetCard m) (fun S => ∑ i ∈ S, c i) hnonempty
  obtain ⟨hSF, hSm⟩ := Finset.mem_powersetCard.mp hS
  refine ⟨S, hSF, hSm, ?_, ?_⟩
  · intro i hi j hj hle
    by_contra hjnot
    have hne : c j ≠ c i := by
      intro heq
      have hji : j = i := hc hj (hSF hi) heq
      exact hjnot (hji.symm ▸ hi)
    have hlt : c j < c i := lt_of_le_of_ne hle hne
    have hjE : j ∉ S.erase i := fun h => hjnot (Finset.mem_of_mem_erase h)
    have hRF' : insert j (S.erase i) ⊆ F := by
      intro k hk
      obtain rfl | hk := Finset.mem_insert.mp hk
      · exact hj
      · exact hSF (Finset.mem_of_mem_erase hk)
    have hRm' : (insert j (S.erase i)).card = m := by
      rw [Finset.card_insert_of_notMem hjE, Finset.card_erase_add_one hi, hSm]
    have hcost := hmin (insert j (S.erase i))
      (Finset.mem_powersetCard.mpr ⟨hRF', hRm'⟩)
    rw [Finset.sum_insert hjE] at hcost
    have hsum := Finset.sum_erase_add S c hi
    omega
  · intro R hRF hRm
    exact hmin R (Finset.mem_powersetCard.mpr ⟨hRF, hRm⟩)


end TokenComplexity.Selection

open scoped BigOperators

namespace TokenComplexity.Selection

variable {ι : Type*}

def lowerSet (F : Finset ι) (c : ι → ℕ) (j : ι) : Finset ι :=
  F.filter (fun i => c i ≤ c j)

noncomputable def cost (c : ι → ℕ) (S : Finset ι) : ℝ :=
  ∑ i ∈ S, (c i : ℝ)

noncomputable def budgetSet (F : Finset ι) (c : ι → ℕ) (b : ℝ) : Finset ι := by
  classical
  exact F.filter (fun i => ∃ j ∈ F, cost c (lowerSet F c j) ≤ b ∧ c i ≤ c j)

noncomputable def quantileSet (F : Finset ι) (c : ι → ℕ) (a : ℝ) : Finset ι := by
  classical
  exact F.filter (fun i => ∃ j ∈ F, a ≤ ((lowerSet F c j).card : ℝ) ∧
    (∀ k ∈ F, a ≤ ((lowerSet F c k).card : ℝ) → c j ≤ c k) ∧ c i ≤ c j)

@[simp] theorem mem_lowerSet (F : Finset ι) (c : ι → ℕ) (i j : ι) :
    i ∈ lowerSet F c j ↔ i ∈ F ∧ c i ≤ c j := by
  simp [lowerSet]

theorem lowerSet_subset (F : Finset ι) (c : ι → ℕ) (j : ι) :
    lowerSet F c j ⊆ F := Finset.filter_subset _ _

theorem lowerSet_mono (F : Finset ι) (c : ι → ℕ) {i j : ι} (h : c i ≤ c j) :
    lowerSet F c i ⊆ lowerSet F c j := by
  intro k hk
  obtain ⟨hkF, hki⟩ := (mem_lowerSet F c k i).mp hk
  exact (mem_lowerSet F c k j).mpr ⟨hkF, hki.trans h⟩

theorem cost_eq_nat (c : ι → ℕ) (S : Finset ι) :
    cost c S = ((∑ i ∈ S, c i : ℕ) : ℝ) := by
  simp [cost]

theorem cost_mono (c : ι → ℕ) {S R : Finset ι} (h : S ⊆ R) :
    cost c S ≤ cost c R := by
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => Nat.cast_nonneg (c i))

theorem downward_eq_lowerSet (F S : Finset ι) (c : ι → ℕ)
    (hSF : S ⊆ F)
    (hdown : ∀ i ∈ S, ∀ j ∈ F, c j ≤ c i → j ∈ S)
    {j : ι} (hj : j ∈ S) (hmax : ∀ i ∈ S, c i ≤ c j) :
    S = lowerSet F c j := by
  ext i
  constructor
  · intro hi
    exact (mem_lowerSet F c i j).mpr ⟨hSF hi, hmax i hi⟩
  · intro hi
    obtain ⟨hiF, hij⟩ := (mem_lowerSet F c i j).mp hi
    exact hdown j hj i hiF hij

theorem budgetSet_feasible (F : Finset ι) (c : ι → ℕ) (b : ℝ) (hb : 0 ≤ b) :
    cost c (budgetSet F c b) ≤ b := by
  classical
  let H := F.filter (fun j => cost c (lowerSet F c j) ≤ b)
  by_cases hH : H.Nonempty
  · obtain ⟨j, hjH, hmax⟩ := Finset.exists_max_image H c hH
    obtain ⟨hjF, hjb⟩ := Finset.mem_filter.mp hjH
    have heq : budgetSet F c b = lowerSet F c j := by
      ext i
      simp only [budgetSet, Finset.mem_filter, mem_lowerSet]
      constructor
      · rintro ⟨hiF, k, hkF, hkb, hik⟩
        exact ⟨hiF, hik.trans (hmax k (Finset.mem_filter.mpr ⟨hkF, hkb⟩))⟩
      · rintro ⟨hiF, hij⟩
        exact ⟨hiF, j, hjF, hjb, hij⟩
    exact heq ▸ hjb
  · have heq : budgetSet F c b = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨_, j, hjF, hjb, _⟩ := Finset.mem_filter.mp hi
      exact hH ⟨j, Finset.mem_filter.mpr ⟨hjF, hjb⟩⟩
    simpa [heq, cost] using hb

theorem budgetSet_max_card (F : Finset ι) (c : ι → ℕ)
    (hc : Set.InjOn c (↑F : Set ι)) (b : ℝ)
    (R : Finset ι) (hRF : R ⊆ F) (hRb : cost c R ≤ b) :
    R.card ≤ (budgetSet F c b).card := by
  classical
  obtain ⟨S, hSF, hSm, hdown, hmin⟩ :=
    minimum_downward_subset F c hc R.card (Finset.card_le_card hRF)
  have hcost : cost c S ≤ cost c R := by
    rw [cost_eq_nat, cost_eq_nat]
    exact Nat.cast_le.mpr (hmin R hRF rfl)
  by_cases hS : S.Nonempty
  · obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image S c hS
    have heq := downward_eq_lowerSet F S c hSF hdown hj hmax
    have hSB : S ⊆ budgetSet F c b := by
      intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨hSF hi, j, hSF hj, ?_, hmax i hi⟩
      rw [← heq]
      exact hcost.trans hRb
    simpa only [hSm] using Finset.card_le_card hSB
  · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hRzero : R.card = 0 := by simpa [hz] using hSm.symm
    simp [hRzero]

theorem budget_frontier (F : Finset ι) (c : ι → ℕ)
    (hc : Set.InjOn c (↑F : Set ι)) (b : ℝ) (hb : 0 ≤ b) :
    cost c (budgetSet F c b) ≤ b ∧
      ∀ R : Finset ι, R ⊆ F → cost c R ≤ b →
        R.card ≤ (budgetSet F c b).card :=
  ⟨budgetSet_feasible F c b hb, fun R hRF hRb => budgetSet_max_card F c hc b R hRF hRb⟩

theorem quantileSet_spec (F : Finset ι) (c : ι → ℕ) (a : ℝ)
    (ha : 0 < a) (hA : a ≤ (F.card : ℝ)) :
    ∃ j ∈ F, a ≤ ((lowerSet F c j).card : ℝ) ∧
      (∀ k ∈ F, a ≤ ((lowerSet F c k).card : ℝ) → c j ≤ c k) ∧
      quantileSet F c a = lowerSet F c j := by
  classical
  have hF : F.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (ha.trans_le hA))
  obtain ⟨k, hkF, hkmax⟩ := Finset.exists_max_image F c hF
  have hFk : lowerSet F c k = F := by
    ext i
    constructor
    · exact fun hi => ((mem_lowerSet F c i k).mp hi).1
    · exact fun hi => (mem_lowerSet F c i k).mpr ⟨hi, hkmax i hi⟩
  let H := F.filter (fun j => a ≤ ((lowerSet F c j).card : ℝ))
  have hH : H.Nonempty := by
    refine ⟨k, Finset.mem_filter.mpr ⟨hkF, ?_⟩⟩
    simpa only [hFk] using hA
  obtain ⟨j, hjH, hjmin⟩ := Finset.exists_min_image H c hH
  obtain ⟨hjF, hja⟩ := Finset.mem_filter.mp hjH
  have hjmin' : ∀ k ∈ F, a ≤ ((lowerSet F c k).card : ℝ) → c j ≤ c k := by
    intro k hk hka
    exact hjmin k (Finset.mem_filter.mpr ⟨hk, hka⟩)
  refine ⟨j, hjF, hja, hjmin', ?_⟩
  ext i
  simp only [quantileSet, Finset.mem_filter, mem_lowerSet]
  constructor
  · rintro ⟨hiF, k, hkF, hka, hkmin, hik⟩
    exact ⟨hiF, hik.trans (hkmin j hjF hja)⟩
  · rintro ⟨hiF, hij⟩
    exact ⟨hiF, j, hjF, hja, hjmin', hij⟩

theorem quantileSet_attains (F : Finset ι) (c : ι → ℕ) (a : ℝ)
    (ha : 0 < a) (hA : a ≤ (F.card : ℝ)) :
    a ≤ ((quantileSet F c a).card : ℝ) := by
  obtain ⟨j, _, hja, _, heq⟩ := quantileSet_spec F c a ha hA
  simpa only [heq] using hja

theorem quantileSet_min_cost (F : Finset ι) (c : ι → ℕ)
    (hc : Set.InjOn c (↑F : Set ι)) (a : ℝ)
    (ha : 0 < a) (hA : a ≤ (F.card : ℝ))
    (R : Finset ι) (hRF : R ⊆ F) (hRa : a ≤ (R.card : ℝ)) :
    cost c (quantileSet F c a) ≤ cost c R := by
  classical
  obtain ⟨j, hjF, hja, hjmin, hQeq⟩ := quantileSet_spec F c a ha hA
  obtain ⟨S, hSF, hSm, hdown, hmin⟩ :=
    minimum_downward_subset F c hc R.card (Finset.card_le_card hRF)
  have hcost : cost c S ≤ cost c R := by
    rw [cost_eq_nat, cost_eq_nat]
    exact Nat.cast_le.mpr (hmin R hRF rfl)
  have hSpos : 0 < (S.card : ℝ) := by
    rw [hSm]
    exact ha.trans_le hRa
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hSpos)
  obtain ⟨k, hkS, hkmax⟩ := Finset.exists_max_image S c hS
  have hSeq := downward_eq_lowerSet F S c hSF hdown hkS hkmax
  have hka : a ≤ ((lowerSet F c k).card : ℝ) := by
    rw [← hSeq, hSm]
    exact hRa
  have hQsub : quantileSet F c a ⊆ S := by
    rw [hQeq, hSeq]
    exact lowerSet_mono F c (hjmin k (hSF hkS) hka)
  exact (cost_mono c hQsub).trans hcost

theorem quantile_frontier (F : Finset ι) (c : ι → ℕ)
    (hc : Set.InjOn c (↑F : Set ι)) (a : ℝ)
    (ha : 0 < a) (hA : a ≤ (F.card : ℝ)) :
    a ≤ ((quantileSet F c a).card : ℝ) ∧
      ∀ R : Finset ι, R ⊆ F → a ≤ (R.card : ℝ) →
        cost c (quantileSet F c a) ≤ cost c R :=
  ⟨quantileSet_attains F c a ha hA,
    fun R hRF hRa => quantileSet_min_cost F c hc a ha hA R hRF hRa⟩


end TokenComplexity.Selection

open scoped BigOperators

namespace TokenComplexity.Tradeoff

variable {n : ℕ}

noncomputable def finiteSet (τ : Fin n → ℕ∞) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => τ i ≠ ⊤)

noncomputable def budgetThreshold (τ : Fin n → ℕ∞) (T : ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => τ i ≠ ⊤ ∧ BelowTT τ T i)

noncomputable def quantileThreshold (τ : Fin n → ℕ∞) (α : ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => τ i ≠ ⊤ ∧ BelowQα τ α i)

@[simp] theorem mem_finiteSet (τ : Fin n → ℕ∞) (i : Fin n) :
    i ∈ finiteSet τ ↔ τ i ≠ ⊤ := by simp [finiteSet]

@[simp] theorem mem_budgetThreshold (τ : Fin n → ℕ∞) (T : ℝ) (i : Fin n) :
    i ∈ budgetThreshold τ T ↔ τ i ≠ ⊤ ∧ BelowTT τ T i := by
  simp [budgetThreshold]

@[simp] theorem mem_quantileThreshold (τ : Fin n → ℕ∞) (α : ℝ) (i : Fin n) :
    i ∈ quantileThreshold τ α ↔ τ i ≠ ⊤ ∧ BelowQα τ α i := by
  simp [quantileThreshold]

theorem budgetThreshold_subset (τ : Fin n → ℕ∞) (T : ℝ) :
    budgetThreshold τ T ⊆ finiteSet τ := by
  intro i hi
  exact (mem_finiteSet τ i).mpr ((mem_budgetThreshold τ T i).mp hi).1

theorem quantileThreshold_subset (τ : Fin n → ℕ∞) (α : ℝ) :
    quantileThreshold τ α ⊆ finiteSet τ := by
  intro i hi
  exact (mem_finiteSet τ i).mpr ((mem_quantileThreshold τ α i).mp hi).1

theorem finite_toNat_le_iff (τ : Fin n → ℕ∞) {i j : Fin n}
    (hi : τ i ≠ ⊤) (hj : τ j ≠ ⊤) :
    τ i ≤ τ j ↔ (τ i).toNat ≤ (τ j).toNat := by
  constructor
  · exact fun h => ENat.toNat_le_toNat h hj
  · intro h
    simpa only [ENat.natCast_toNat hi, ENat.natCast_toNat hj] using
      (ENat.natCast_le_natCast.mpr h)

theorem finite_toNat_injective (τ : Fin n → ℕ∞)
    (hdist : ∀ i j, τ i ≠ ⊤ → τ i = τ j → i = j) :
    Set.InjOn (fun i => (τ i).toNat) (↑(finiteSet τ) : Set (Fin n)) := by
  intro i hi j hj heq
  have hi' : τ i ≠ ⊤ := (mem_finiteSet τ i).mp hi
  have hj' : τ j ≠ ⊤ := (mem_finiteSet τ j).mp hj
  apply hdist i j hi'
  calc
    τ i = ((τ i).toNat : ℕ∞) := (ENat.natCast_toNat hi').symm
    _ = ((τ j).toNat : ℕ∞) := congrArg (fun a : ℕ => (a : ℕ∞)) heq
    _ = τ j := ENat.natCast_toNat hj'

theorem real_threshold_filter (τ : Fin n → ℕ∞) (j : Fin n) :
    (Finset.univ.filter (fun i => τ i ≠ ⊤ ∧ ((τ i).toNat : ℝ) ≤ (τ j).toNat)) =
      Selection.lowerSet (finiteSet τ) (fun i => (τ i).toNat) j := by
  classical
  ext i
  simp [Selection.lowerSet, finiteSet]

theorem En_eq_cost_lowerSet (τ : Fin n → ℕ∞) (j : Fin n) :
    En τ ((τ j).toNat : ℝ) =
      Selection.cost (fun i => (τ i).toNat)
        (Selection.lowerSet (finiteSet τ) (fun i => (τ i).toNat) j) / n := by
  simp only [En, Selection.cost, real_threshold_filter]

theorem Fn_eq_card_lowerSet (τ : Fin n → ℕ∞) (j : Fin n) :
    Fn τ ((τ j).toNat : ℝ) =
      ((Selection.lowerSet (finiteSet τ) (fun i => (τ i).toNat) j).card : ℝ) / n := by
  simp only [Fn, real_threshold_filter]

theorem alphaClosed_eq_threshold (τ : Fin n → ℕ∞) (T : ℝ) :
    alphaClosed τ T = ((budgetThreshold τ T).card : ℝ) / n := rfl

theorem TClosed_eq_threshold (τ : Fin n → ℕ∞) (α : ℝ) :
    TClosed τ α = Selection.cost (fun i => (τ i).toNat) (quantileThreshold τ α) / n := rfl

theorem Astar_eq_finiteSet (τ : Fin n → ℕ∞) :
    Astar τ = ((finiteSet τ).card : ℝ) / n := rfl

theorem budgetThreshold_eq_budgetSet (hn : 0 < n) (τ : Fin n → ℕ∞) (T : ℝ) :
    budgetThreshold τ T =
      Selection.budgetSet (finiteSet τ) (fun i => (τ i).toNat) (T * n) := by
  classical
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  ext i
  simp only [mem_budgetThreshold, BelowTT, Selection.budgetSet, Finset.mem_filter,
    mem_finiteSet]
  constructor
  · rintro ⟨hi, j, hj, hjT, hij⟩
    refine ⟨hi, j, hj, ?_, (finite_toNat_le_iff τ hi hj).mp hij⟩
    rw [En_eq_cost_lowerSet] at hjT
    exact (div_le_iff₀ hnR).mp hjT
  · rintro ⟨hi, j, hj, hjT, hij⟩
    refine ⟨hi, j, hj, ?_, (finite_toNat_le_iff τ hi hj).mpr hij⟩
    rw [En_eq_cost_lowerSet]
    exact (div_le_iff₀ hnR).mpr hjT

theorem quantileThreshold_eq_quantileSet (hn : 0 < n) (τ : Fin n → ℕ∞) (α : ℝ) :
    quantileThreshold τ α =
      Selection.quantileSet (finiteSet τ) (fun i => (τ i).toNat) (α * n) := by
  classical
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  ext i
  simp only [mem_quantileThreshold, BelowQα, Selection.quantileSet, Finset.mem_filter,
    mem_finiteSet]
  constructor
  · rintro ⟨hi, j, hj, hjα, hjmin, hij⟩
    refine ⟨hi, j, hj, ?_, ?_, (finite_toNat_le_iff τ hi hj).mp hij⟩
    · rw [Fn_eq_card_lowerSet] at hjα
      exact (le_div_iff₀ hnR).mp hjα
    · intro k hk hkα
      apply (finite_toNat_le_iff τ hj hk).mp
      apply hjmin k hk
      rw [Fn_eq_card_lowerSet]
      exact (le_div_iff₀ hnR).mpr hkα
  · rintro ⟨hi, j, hj, hjα, hjmin, hij⟩
    refine ⟨hi, j, hj, ?_, ?_, (finite_toNat_le_iff τ hi hj).mpr hij⟩
    · rw [Fn_eq_card_lowerSet]
      exact (le_div_iff₀ hnR).mpr hjα
    · intro k hk hkα
      apply (finite_toNat_le_iff τ hj hk).mpr
      apply hjmin k hk
      rw [Fn_eq_card_lowerSet] at hkα
      exact (le_div_iff₀ hnR).mp hkα

theorem budget_threshold_frontier (hn : 0 < n) (τ : Fin n → ℕ∞)
    (hdist : ∀ i j, τ i ≠ ⊤ → τ i = τ j → i = j)
    (T : ℝ) (hT : 0 ≤ T) :
    Selection.cost (fun i => (τ i).toNat) (budgetThreshold τ T) / n ≤ T ∧
      ∀ R : Finset (Fin n), R ⊆ finiteSet τ →
        Selection.cost (fun i => (τ i).toNat) R / n ≤ T →
        (R.card : ℝ) / n ≤ alphaClosed τ T := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  obtain ⟨hbudget, hmax⟩ := Selection.budget_frontier (finiteSet τ)
    (fun i => (τ i).toNat) (finite_toNat_injective τ hdist) (T * n)
    (mul_nonneg hT (Nat.cast_nonneg n))
  rw [← budgetThreshold_eq_budgetSet hn τ T] at hbudget hmax
  refine ⟨(div_le_iff₀ hnR).mpr hbudget, ?_⟩
  intro R hRF hRT
  rw [alphaClosed_eq_threshold]
  apply div_le_div_of_nonneg_right _ (le_of_lt hnR)
  exact Nat.cast_le.mpr (hmax R hRF ((div_le_iff₀ hnR).mp hRT))

theorem quantile_threshold_frontier (hn : 0 < n) (τ : Fin n → ℕ∞)
    (hdist : ∀ i j, τ i ≠ ⊤ → τ i = τ j → i = j)
    (α : ℝ) (hα : 0 < α) (hA : α ≤ Astar τ) :
    α ≤ ((quantileThreshold τ α).card : ℝ) / n ∧
      ∀ R : Finset (Fin n), R ⊆ finiteSet τ → α ≤ (R.card : ℝ) / n →
        TClosed τ α ≤ Selection.cost (fun i => (τ i).toNat) R / n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hA' : α * n ≤ ((finiteSet τ).card : ℝ) := by
    apply (le_div_iff₀ hnR).mp
    simpa only [Astar_eq_finiteSet] using hA
  obtain ⟨hquantile, hmin⟩ := Selection.quantile_frontier (finiteSet τ)
    (fun i => (τ i).toNat) (finite_toNat_injective τ hdist) (α * n)
    (mul_pos hα hnR) hA'
  rw [← quantileThreshold_eq_quantileSet hn τ α] at hquantile hmin
  refine ⟨(le_div_iff₀ hnR).mpr hquantile, ?_⟩
  intro R hRF hRα
  rw [TClosed_eq_threshold]
  apply div_le_div_of_nonneg_right _ (le_of_lt hnR)
  exact hmin R hRF ((le_div_iff₀ hnR).mp hRα)


end TokenComplexity.Tradeoff

-- Accepted Prove2Me implementation by shivm, submission 915fc9cc-b000-4c98-855a-ca2abd55cf4d

open Finset

open TokenComplexity.Tradeoff in
theorem prompt_vector_equiv {n : ℕ} {Prompt : Type} (B : Benchmark n Prompt) (τ : Fin n → ℕ∞)
    (hA1 : TokenComplexityHyp B τ) (hRich : Rich B) :
    (∀ T v : ℝ, IsOptAccuracy B T v ↔
      IsGreatest {a | ∃ t : Fin n → ℕ, (∑ i, (t i : ℝ)) / n ≤ T ∧
        a = ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n} v) ∧
    (∀ α v : ℝ, IsMinAvgLen B α v ↔
      IsLeast {L | ∃ t : Fin n → ℕ,
        α ≤ ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n ∧
        L = (∑ i, (t i : ℝ)) / n} v) := by
  have hacc : ∀ P, accuracy B P
      = ((univ.filter (fun i => τ i ≤ (B.len P i : ℕ∞))).card : ℝ) / n := by
    intro P
    unfold accuracy
    rw [Finset.filter_congr (fun i _ => hA1 P i)]
  have hlen : ∀ P, avgLen B P = (∑ i, (B.len P i : ℝ)) / n := fun P => rfl
  refine ⟨fun T v => ?_, fun α v => ?_⟩
  · unfold IsOptAccuracy
    have hS : {a | ∃ P, avgLen B P ≤ T ∧ accuracy B P = a}
        = {a | ∃ t : Fin n → ℕ, (∑ i, (t i : ℝ)) / n ≤ T ∧
          a = ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n} := by
      ext a
      constructor
      · rintro ⟨P, h1, h2⟩
        exact ⟨B.len P, by rw [← hlen]; exact h1, by rw [← h2, hacc]⟩
      · rintro ⟨t, h1, h2⟩
        obtain ⟨P, hP⟩ := hRich t
        have ht : B.len P = t := funext hP
        subst ht
        exact ⟨P, by rw [hlen]; exact h1, by rw [h2, hacc]⟩
    rw [hS]
  · unfold IsMinAvgLen
    have hS : {L | ∃ P, α ≤ accuracy B P ∧ avgLen B P = L}
        = {L | ∃ t : Fin n → ℕ,
          α ≤ ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n ∧
          L = (∑ i, (t i : ℝ)) / n} := by
      ext L
      constructor
      · rintro ⟨P, h1, h2⟩
        exact ⟨B.len P, by rw [← hacc]; exact h1, by rw [← h2, hlen]⟩
      · rintro ⟨t, h1, h2⟩
        obtain ⟨P, hP⟩ := hRich t
        have ht : B.len P = t := funext hP
        subst ht
        exact ⟨P, by rw [hacc]; exact h1, by rw [h2, hlen]⟩
    rw [hS]

-- Accepted Prove2Me implementation by shivm, submission a6214de1-9daf-45f3-8bd6-0ef1e1d81b94

namespace Aux_TC_1112

open Finset

lemma mapA {n : ℕ} (τ : Fin n → ℕ∞) (t : Fin n → ℕ) :
    ∃ x : Fin n → Bool, (∀ i, x i = true → τ i ≠ ⊤) ∧
      ((univ.filter (fun i => x i = true)).card : ℝ) =
        ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) ∧
      (∑ i ∈ univ.filter (fun i => x i = true), ((τ i).toNat : ℝ)) ≤ ∑ i, (t i : ℝ) := by
  refine ⟨fun i => decide (τ i ≤ (t i : ℕ∞)), fun i hi => ?_, ?_, ?_⟩
  · simp only [decide_eq_true_eq] at hi
    exact ne_top_of_le_ne_top (ENat.coe_ne_top _) hi
  · congr 2
    ext i; simp
  · have hf : univ.filter (fun i => decide (τ i ≤ (t i : ℕ∞)) = true) =
        univ.filter (fun i => τ i ≤ (t i : ℕ∞)) := by ext i; simp
    rw [hf]
    calc ∑ i ∈ univ.filter (fun i => τ i ≤ (t i : ℕ∞)), ((τ i).toNat : ℝ)
        ≤ ∑ i ∈ univ.filter (fun i => τ i ≤ (t i : ℕ∞)), (t i : ℝ) := by
          refine Finset.sum_le_sum fun i hi => ?_
          simp only [mem_filter, mem_univ, true_and] at hi
          have := ENat.toNat_le_toNat hi (ENat.coe_ne_top _)
          rw [ENat.toNat_coe] at this
          exact_mod_cast this
      _ ≤ ∑ i, (t i : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun i _ _ => Nat.cast_nonneg _)

lemma mapB {n : ℕ} (τ : Fin n → ℕ∞) (x : Fin n → Bool) (hx : ∀ i, x i = true → τ i ≠ ⊤) :
    ∃ t : Fin n → ℕ, (∑ i, (t i : ℝ)) =
        ∑ i ∈ univ.filter (fun i => x i = true), ((τ i).toNat : ℝ) ∧
      ((univ.filter (fun i => x i = true)).card : ℝ) ≤
        ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) := by
  refine ⟨fun i => if x i = true then (τ i).toNat else 0, ?_, ?_⟩
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Nat.cast_ite, Nat.cast_zero]
  · have : univ.filter (fun i => x i = true) ⊆
        univ.filter (fun i => τ i ≤ ((if x i = true then (τ i).toNat else 0 : ℕ) : ℕ∞)) := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      rw [if_pos hi, ENat.coe_toNat (hx i hi)]
    exact_mod_cast Finset.card_le_card this

end Aux_TC_1112

open Finset Aux_TC_1112 in
theorem vector_knapsack_equiv {n : ℕ} (τ : Fin n → ℕ∞) :
    (∀ T v : ℝ,
      IsGreatest {a | ∃ t : Fin n → ℕ, (∑ i, (t i : ℝ)) / n ≤ T ∧
        a = ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n} v ↔
      IsGreatest {a | ∃ x : Fin n → Bool, (∀ i, x i = true → τ i ≠ ⊤) ∧
        (∑ i ∈ univ.filter (fun i => x i = true), ((τ i).toNat : ℝ)) / n ≤ T ∧
        a = ((univ.filter (fun i => x i = true)).card : ℝ) / n} v) ∧
    (∀ α v : ℝ,
      IsLeast {L | ∃ t : Fin n → ℕ,
        α ≤ ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n ∧
        L = (∑ i, (t i : ℝ)) / n} v ↔
      IsLeast {L | ∃ x : Fin n → Bool, (∀ i, x i = true → τ i ≠ ⊤) ∧
        α ≤ ((univ.filter (fun i => x i = true)).card : ℝ) / n ∧
        L = (∑ i ∈ univ.filter (fun i => x i = true), ((τ i).toNat : ℝ)) / n} v) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨fun T v => ⟨?_, ?_⟩, fun α v => ⟨?_, ?_⟩⟩
  · rintro ⟨⟨t, ht, rfl⟩, hmax⟩
    obtain ⟨x, hx, hacc, hcost⟩ := mapA τ t
    refine ⟨⟨x, hx, le_trans (div_le_div_of_nonneg_right hcost hn) ht, by rw [hacc]⟩, ?_⟩
    rintro a ⟨x', hx', hc', rfl⟩
    obtain ⟨t', hct, hat⟩ := mapB τ x' hx'
    refine le_trans (div_le_div_of_nonneg_right hat hn) (hmax ⟨t', ?_, rfl⟩)
    rw [hct]; exact hc'
  · rintro ⟨⟨x, hx, hc, rfl⟩, hmax⟩
    obtain ⟨t, hct, hat⟩ := mapB τ x hx
    have ht : (∑ i, (t i : ℝ)) / n ≤ T := by rw [hct]; exact hc
    obtain ⟨x', hx', hacc', hcost'⟩ := mapA τ t
    have hle : ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n ≤
        ((univ.filter (fun i => x i = true)).card : ℝ) / n := by
      refine hmax ⟨x', hx', le_trans (div_le_div_of_nonneg_right hcost' hn) ht, ?_⟩
      rw [hacc']
    have heq : ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n =
        ((univ.filter (fun i => x i = true)).card : ℝ) / n :=
      le_antisymm hle (div_le_div_of_nonneg_right hat hn)
    refine ⟨⟨t, ht, heq.symm⟩, ?_⟩
    rintro a ⟨t'', ht'', rfl⟩
    obtain ⟨x'', hx'', hacc'', hcost''⟩ := mapA τ t''
    refine hmax ⟨x'', hx'', le_trans (div_le_div_of_nonneg_right hcost'' hn) ht'', ?_⟩
    rw [hacc'']
  · rintro ⟨⟨t, ht, rfl⟩, hmin⟩
    obtain ⟨x, hx, hacc, hcost⟩ := mapA τ t
    have hxa : α ≤ ((univ.filter (fun i => x i = true)).card : ℝ) / n := by rw [hacc]; exact ht
    obtain ⟨t', hct, hat⟩ := mapB τ x hx
    have h1 : (∑ i, (t i : ℝ)) / n ≤ (∑ i ∈ univ.filter (fun i => x i = true),
        ((τ i).toNat : ℝ)) / n := by
      refine hmin ⟨t', le_trans hxa (div_le_div_of_nonneg_right hat hn), ?_⟩
      rw [hct]
    have heq := le_antisymm (div_le_div_of_nonneg_right hcost hn) h1
    refine ⟨⟨x, hx, hxa, heq.symm⟩, ?_⟩
    rintro L ⟨x', hx', ha', rfl⟩
    obtain ⟨t'', hct'', hat''⟩ := mapB τ x' hx'
    refine hmin ⟨t'', le_trans ha' (div_le_div_of_nonneg_right hat'' hn), ?_⟩
    rw [hct'']
  · rintro ⟨⟨x, hx, ha, rfl⟩, hmin⟩
    obtain ⟨t, hct, hat⟩ := mapB τ x hx
    refine ⟨⟨t, le_trans ha (div_le_div_of_nonneg_right hat hn), by rw [hct]⟩, ?_⟩
    rintro L ⟨t', ht', rfl⟩
    obtain ⟨x', hx', hacc', hcost'⟩ := mapA τ t'
    refine le_trans (hmin ⟨x', hx', by rw [hacc']; exact ht', rfl⟩)
      (div_le_div_of_nonneg_right hcost' hn)

open Finset

namespace TokenComplexity.Tradeoff

lemma selection_maximum {n : ℕ} (τ : Fin n → ℕ∞) (S : Finset (Fin n)) (T : ℝ)
    (hfinite : ∀ i ∈ S, τ i ≠ ⊤)
    (hfeasible : (∑ i ∈ S, ((τ i).toNat : ℝ)) / n ≤ T)
    (hmax : ∀ R : Finset (Fin n), (∀ i ∈ R, τ i ≠ ⊤) →
      (∑ i ∈ R, ((τ i).toNat : ℝ)) / n ≤ T →
      (R.card : ℝ) / n ≤ (S.card : ℝ) / n) :
    IsGreatest {a | ∃ x : Fin n → Bool, (∀ i, x i = true → τ i ≠ ⊤) ∧
      (∑ i ∈ univ.filter (fun i => x i = true), ((τ i).toNat : ℝ)) / n ≤ T ∧
      a = ((univ.filter (fun i => x i = true)).card : ℝ) / n}
      ((S.card : ℝ) / n) := by
  classical
  have hfilter : univ.filter (fun i : Fin n => decide (i ∈ S) = true) = S := by
    ext i
    simp
  constructor
  · refine ⟨fun i => decide (i ∈ S), ?_, ?_, ?_⟩
    · intro i hi
      exact hfinite i (of_decide_eq_true hi)
    · simpa only [hfilter] using hfeasible
    · rw [hfilter]
  · rintro a ⟨x, hx, hcost, rfl⟩
    exact hmax _ (fun i hi => hx i (mem_filter.mp hi).2) hcost

lemma selection_minimum {n : ℕ} (τ : Fin n → ℕ∞) (S : Finset (Fin n)) (α : ℝ)
    (hfinite : ∀ i ∈ S, τ i ≠ ⊤)
    (hfeasible : α ≤ (S.card : ℝ) / n)
    (hmin : ∀ R : Finset (Fin n), (∀ i ∈ R, τ i ≠ ⊤) →
      α ≤ (R.card : ℝ) / n →
      (∑ i ∈ S, ((τ i).toNat : ℝ)) / n ≤ (∑ i ∈ R, ((τ i).toNat : ℝ)) / n) :
    IsLeast {L | ∃ x : Fin n → Bool, (∀ i, x i = true → τ i ≠ ⊤) ∧
      α ≤ ((univ.filter (fun i => x i = true)).card : ℝ) / n ∧
      L = (∑ i ∈ univ.filter (fun i => x i = true), ((τ i).toNat : ℝ)) / n}
      ((∑ i ∈ S, ((τ i).toNat : ℝ)) / n) := by
  classical
  have hfilter : univ.filter (fun i : Fin n => decide (i ∈ S) = true) = S := by
    ext i
    simp
  constructor
  · refine ⟨fun i => decide (i ∈ S), ?_, ?_, ?_⟩
    · intro i hi
      exact hfinite i (of_decide_eq_true hi)
    · simpa only [hfilter] using hfeasible
    · rw [hfilter]
  · rintro L ⟨x, hx, hcard, rfl⟩
    exact hmin _ (fun i hi => hx i (mem_filter.mp hi).2) hcard

end TokenComplexity.Tradeoff

open Finset TokenComplexity.Tradeoff

theorem solution {n : ℕ} (hn : 0 < n) {Prompt : Type} (B : Benchmark n Prompt)
    (τ : Fin n → ℕ∞) (hA1 : TokenComplexityHyp B τ) (hRich : Rich B)
    (hdist : ∀ i j, τ i ≠ ⊤ → τ i = τ j → i = j) :
    (∀ T : ℝ, 0 ≤ T → IsOptAccuracy B T (alphaClosed τ T)) ∧
    (∀ α : ℝ, 0 < α → α ≤ Astar τ → IsMinAvgLen B α (TClosed τ α)) := by
  classical
  have hp := prompt_vector_equiv B τ hA1 hRich
  have hk := vector_knapsack_equiv τ
  constructor
  · intro T hT
    apply (hp.1 T _).mpr
    apply (hk.1 T _).mpr
    have hf := budget_threshold_frontier hn τ hdist T hT
    apply selection_maximum τ (budgetThreshold τ T) T
    · intro i hi
      exact (mem_filter.mp hi).2.1
    · exact hf.1
    · intro R hR hcost
      apply hf.2 R _ hcost
      intro i hi
      simp only [finiteSet, mem_filter, mem_univ, true_and]
      exact hR i hi
  · intro α hα hA
    apply (hp.2 α _).mpr
    apply (hk.2 α _).mpr
    have hf := quantile_threshold_frontier hn τ hdist α hα hA
    apply selection_minimum τ (quantileThreshold τ α) α
    · intro i hi
      exact (mem_filter.mp hi).2.1
    · exact hf.1
    · intro R hR hcard
      apply hf.2 R _ hcard
      intro i hi
      simp only [finiteSet, mem_filter, mem_univ, true_and]
      exact hR i hi

#print axioms solution
