-- Prove2me | solution 1 for compression_bounds_vcdim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:44:31.894297+00:00
-- url     : https://prove2.me/submissions/e23f5b7d-4606-4852-9e07-f5d39538393d

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Data
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Ordinal
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Bayesian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Bridge
public import Theorems.Thm_compress_injective_on_labelings


set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u)
    (C : ConceptClass X Bool) (cs : CompressionScheme X Bool C)
    (hcs : 0 < cs.size) :
    VCDim X C ≤ ↑(2 * (cs.size + 1) * (cs.size + 1) - 1) := by
  set k := cs.size with hk_def
  set N := 2 * (k + 1) * (k + 1) with hN_def
  -- Suffices: every shattered set has card < N, i.e., card ≤ N - 1
  unfold VCDim
  apply iSup₂_le
  intro S hS
  -- Show S.card ≤ N - 1 by contradiction: assume S.card ≥ N
  by_contra h_big
  push Not at h_big
  -- h_big : ↑(N - 1) < ↑S.card, so N ≤ S.card
  have hN_le : N ≤ S.card := by
    have : (N - 1 : ℕ) < S.card := by exact_mod_cast h_big
    omega
  -- Classical reasoning for DecidableEq
  have : DecidableEq X := Classical.decEq X
  -- Take subset T ⊆ S with |T| = N
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hN_le
  -- T is shattered (subset of shattered set)
  have hT_shatt : Shatters X C T := by
    intro f
    -- Extend f to a labeling on S
    let g : ↥S → Bool := fun ⟨x, hx⟩ => if h : x ∈ T then f ⟨x, h⟩ else false
    obtain ⟨c, hcC, hcg⟩ := hS g
    refine ⟨c, hcC, ?_⟩
    intro ⟨x, hx⟩
    have hxS : x ∈ S := hT_sub hx
    simpa only [g, hx, dite_true] using hcg ⟨x, hxS⟩
  set n := T.card with hn_def
  have hn_eq : n = N := hT_card
  -- Enumerate T injectively
  let eqv := T.equivFin.symm
  let pts : Fin n → X := fun i => (eqv i : X)
  have hpts_inj : Function.Injective pts :=
    fun _ _ h => eqv.injective (Subtype.val_injective h)
  -- Build sample from labeling
  let mkSample : (Fin n → Bool) → (Fin n → X × Bool) := fun f i => (pts i, f i)
  -- Every labeling of T is C-realizable (T is shattered)
  have h_realizable : ∀ f : Fin n → Bool, ∃ c ∈ C, ∀ i : Fin n, c (pts i) = f i := by
    intro f
    let f' : ↥T → Bool := fun ⟨x, hx⟩ => f (T.equivFin ⟨x, hx⟩)
    obtain ⟨c, hcC, hcf'⟩ := hT_shatt f'
    refine ⟨c, hcC, fun i => ?_⟩
    have := hcf' (eqv i)
    simp only [f', pts] at this ⊢
    rwa [show T.equivFin (eqv i) = i from T.equivFin.apply_symm_apply i] at this
  -- compress ∘ mkSample is injective
  have h_inj : Function.Injective (cs.compress ∘ mkSample) := by
    intro f g hfg
    exact compress_injective_on_labelings cs pts hpts_inj f g
      (h_realizable f) (h_realizable g) hfg
  -- Target: subsets of T ×ˢ {true,false} of size ≤ k
  set A := T ×ˢ (Finset.univ : Finset Bool) with hA_def
  set target := A.powerset.filter (fun S => S.card ≤ k) with htarget_def
  -- Each compressed set lands in target
  have h_maps_to : ∀ f : Fin n → Bool, (cs.compress ∘ mkSample) f ∈ target := by
    intro f
    simp only [Function.comp, htarget_def, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro p hp
      have hsub := cs.compress_sub (mkSample f)
      have hp_range : (p : X × Bool) ∈ Set.range (mkSample f) :=
        hsub (Finset.mem_coe.mpr hp)
      obtain ⟨i, hi⟩ := hp_range
      simp only [mkSample] at hi
      rw [Finset.mem_product]
      exact ⟨by rw [show p.1 = pts i from (congr_arg Prod.fst hi).symm]; exact (eqv i).2,
             Finset.mem_univ _⟩
    · have := cs.compress_small (mkSample f); omega
  -- Source cardinality: 2^n
  have h_source_card : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    simp [Fintype.card_fin, Fintype.card_bool]
  -- Target bound: |target| ≤ (k+1)·(2n)^k
  have hA_card : A.card = 2 * n := by
    simp [hA_def, Finset.card_product]; ring
  have h_target_le : target.card ≤ (k + 1) * (2 * n) ^ k := by
    calc target.card
        ≤ (Finset.range (k + 1)).sum (fun j => (A.powersetCard j).card) := by
          have : target ⊆ (Finset.range (k + 1)).biUnion (fun j => A.powersetCard j) := by
            intro S' hS'
            simp_all
          exact (Finset.card_le_card this).trans Finset.card_biUnion_le
      _ = (Finset.range (k + 1)).sum (fun j => (2 * n).choose j) := by
          simp [Finset.card_powersetCard, hA_card]
      _ ≤ (Finset.range (k + 1)).sum (fun _ => (2 * n) ^ k) := by
          apply Finset.sum_le_sum; intro j hj
          simp only [Finset.mem_range] at hj
          calc (2 * n).choose j ≤ (2 * n) ^ j := Nat.choose_le_pow _ _
            _ ≤ (2 * n) ^ k := by
                exact Nat.pow_le_pow_right
                  (by rw [hn_eq, hN_def]; positivity) (by omega)
      _ = (k + 1) * (2 * n) ^ k := by simp [Finset.sum_const, Finset.card_range]
  -- Key inequality: (k+1)·(2n)^k < 2^n at n = 2(k+1)²
  -- Inline exp_beats_poly_at: (k+1)·(4(k+1)²)^k < 2^(2(k+1)²)
  have h_exp_beats : (k + 1) * (2 * (2 * (k + 1) * (k + 1))) ^ k <
      2 ^ (2 * (k + 1) * (k + 1)) := by
    have h1 : k + 1 ≤ 2 ^ k := by
      induction k with
      | zero => omega
      | succ k ih => calc k + 1 + 1 ≤ 2 ^ k + 2 ^ k := by omega
                       _ = 2 ^ (k + 1) := by ring
    have hsimp : 2 * (2 * (k + 1) * (k + 1)) = 4 * (k + 1) ^ 2 := by ring
    rw [hsimp]
    have hpow : (4 * (k + 1) ^ 2) ^ k = 2 ^ (2 * k) * (k + 1) ^ (2 * k) := by
      rw [show (4 : ℕ) = 2 ^ 2 from by norm_num]
      rw [mul_pow, ← pow_mul, ← pow_mul]
    rw [hpow]
    rw [show (k + 1) * (2 ^ (2 * k) * (k + 1) ^ (2 * k)) =
      2 ^ (2 * k) * (k + 1) ^ (2 * k + 1) from by ring]
    have hrhs : 2 * (k + 1) * (k + 1) = 2 * (k + 1) ^ 2 := by ring
    rw [hrhs]
    have h2 : (k + 1) ^ (2 * k + 1) ≤ (2 ^ k) ^ (2 * k + 1) :=
      Nat.pow_le_pow_left h1 _
    rw [← pow_mul] at h2
    calc 2 ^ (2 * k) * (k + 1) ^ (2 * k + 1)
        ≤ 2 ^ (2 * k) * 2 ^ (k * (2 * k + 1)) := Nat.mul_le_mul_left _ h2
      _ = 2 ^ (2 * k + k * (2 * k + 1)) := by rw [← pow_add]
      _ = 2 ^ (2 * k ^ 2 + 3 * k) := by ring_nf
      _ < 2 ^ (2 * (k + 1) ^ 2) := by
          apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
          nlinarith
  have h_target_lt : target.card < 2 ^ n := by
    calc target.card ≤ (k + 1) * (2 * n) ^ k := h_target_le
      _ = (k + 1) * (2 * (2 * (k + 1) * (k + 1))) ^ k := by rw [hn_eq]
      _ < 2 ^ (2 * (k + 1) * (k + 1)) := h_exp_beats
      _ = 2 ^ n := by rw [hn_eq]
  -- Pigeonhole: more labelings (2^n) than target slots → contradiction with injectivity
  have h_card_lt : target.card < (Finset.univ : Finset (Fin n → Bool)).card := by
    rw [h_source_card]; exact h_target_lt
  exact absurd h_inj (by
    intro h_inj_false
    obtain ⟨f, _, g, _, hne, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_card_lt
        (fun x _ => h_maps_to x)
    exact absurd heq (fun h => hne (h_inj_false h)))
