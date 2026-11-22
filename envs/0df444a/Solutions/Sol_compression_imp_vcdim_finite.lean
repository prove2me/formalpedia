-- Prove2me | solution 1 for compression_imp_vcdim_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:56.89619+00:00
-- url     : https://prove2.me/submissions/450ca871-9816-411e-b9bb-b559cbc6ef4c

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Theorems.Thm_compress_injective_on_labelings
section
@[expose] public section
universe u v
section ERM_section
end ERM_section
section TrueError
end TrueError
section EmpiricalMeasureError
end EmpiricalMeasureError
section Consistency
end Consistency
section ConcentrationInfrastructure
end ConcentrationInfrastructure
section UniformConvergence
end UniformConvergence
section ConcentrationBridge
end ConcentrationBridge
section NFLCounting
end NFLCounting
section NFLInfrastructure
private lemma succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => calc k + 1 + 1 ≤ 2 ^ k + 2 ^ k := by omega
                   _ = 2 ^ (k + 1) := by ring
private lemma shatters_subset {X : Type u} {C : ConceptClass X Bool}
    {S T : Finset X} (hST : T ⊆ S) (hS : Shatters X C S) : Shatters X C T := by
  intro f
  -- Extend f to a labeling on S
  classical
  let g : ↥S → Bool := fun ⟨x, hx⟩ => if h : x ∈ T then f ⟨x, h⟩ else false
  obtain ⟨c, hcC, hcg⟩ := hS g
  refine ⟨c, hcC, ?_⟩
  intro ⟨x, hx⟩
  have hxS : x ∈ S := hST hx
  simpa only [g, hx, dite_true] using hcg ⟨x, hxS⟩
private lemma exp_beats_poly_at (k : ℕ) :
    (k + 1) * (2 * (2 * (k + 1) * (k + 1))) ^ k < 2 ^ (2 * (k + 1) * (k + 1)) := by
  -- Simplify: 2 * (2 * (k+1) * (k+1)) = 4 * (k+1)²
  -- LHS = (k+1) * (4*(k+1)²)^k = (k+1) * 4^k * (k+1)^(2k) = (k+1)^(2k+1) * 2^(2k)
  -- RHS = 2^(2*(k+1)²) = 2^(2k²+4k+2)
  -- Chain: (k+1)^(2k+1) ≤ (2^k)^(2k+1) = 2^(k(2k+1)) = 2^(2k²+k) [by succ_le_two_pow]
  -- So LHS ≤ 2^(2k²+k) * 2^(2k) = 2^(2k²+3k)
  -- And 2k²+3k < 2k²+4k+2 [by omega]
  -- So LHS < 2^(2k²+4k+2) = RHS
  have h1 : k + 1 ≤ 2 ^ k := succ_le_two_pow k
  -- (k+1) * (4*(k+1)^2)^k = (k+1) * (4^k * (k+1)^(2*k))
  have hsimp : 2 * (2 * (k + 1) * (k + 1)) = 4 * (k + 1) ^ 2 := by ring
  rw [hsimp]
  -- (4 * (k+1)^2)^k = 4^k * ((k+1)^2)^k = 4^k * (k+1)^(2*k) = 2^(2k) * (k+1)^(2k)
  have hpow : (4 * (k + 1) ^ 2) ^ k = 2 ^ (2 * k) * (k + 1) ^ (2 * k) := by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num]
    rw [mul_pow, ← pow_mul, ← pow_mul]
  rw [hpow]
  -- LHS = (k+1) * (2^(2k) * (k+1)^(2k)) = 2^(2k) * (k+1)^(2k+1)
  rw [show (k + 1) * (2 ^ (2 * k) * (k + 1) ^ (2 * k)) =
    2 ^ (2 * k) * (k + 1) ^ (2 * k + 1) from by ring]
  -- RHS: 2 * (k+1) * (k+1) = (k+1)^2 + ... well, 2*(k+1)*(k+1) = 2*(k+1)^2
  have hrhs : 2 * (k + 1) * (k + 1) = 2 * (k + 1) ^ 2 := by ring
  rw [hrhs]
  -- Bound (k+1)^(2k+1) ≤ (2^k)^(2k+1) = 2^(k*(2k+1))
  have h2 : (k + 1) ^ (2 * k + 1) ≤ (2 ^ k) ^ (2 * k + 1) :=
    Nat.pow_le_pow_left h1 _
  rw [← pow_mul] at h2
  -- So LHS ≤ 2^(2k) * 2^(k*(2k+1)) = 2^(2k + k*(2k+1)) = 2^(2k²+3k)
  calc 2 ^ (2 * k) * (k + 1) ^ (2 * k + 1)
      ≤ 2 ^ (2 * k) * 2 ^ (k * (2 * k + 1)) := Nat.mul_le_mul_left _ h2
    _ = 2 ^ (2 * k + k * (2 * k + 1)) := by rw [← pow_add]
    _ = 2 ^ (2 * k ^ 2 + 3 * k) := by ring_nf
    _ < 2 ^ (2 * (k + 1) ^ 2) := by
        apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
        nlinarith
end NFLInfrastructure
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u)
    (C : ConceptClass X Bool)
    (hcomp : ∃ (k : ℕ) (cs : CompressionScheme X Bool C), cs.size = k) :
    VCDim X C < ⊤ := by
  -- Proof by contradiction: assume VCDim X C = ⊤.
  by_contra h_top
  push Not at h_top
  rw [top_le_iff] at h_top
  obtain ⟨k, cs, hk⟩ := hcomp
  -- VCDim = ⊤ ⟹ arbitrarily large shattered sets
  have h_large : ∀ n : ℕ, ∃ S : Finset X, Shatters X C S ∧ n ≤ S.card := by
    intro n
    by_contra h_neg
    push Not at h_neg
    have : VCDim X C ≤ ↑n := by
      apply iSup₂_le; intro S hS
      exact_mod_cast Nat.le_of_lt_succ (Nat.lt_succ_of_lt (h_neg S hS))
    exact absurd h_top (ne_of_lt (lt_of_le_of_lt this (WithTop.coe_lt_top _)))
  -- Set N = 2(k+1)² — the exact size we'll use
  set N := 2 * (k + 1) * (k + 1) with hN_def
  -- Get shattered T₀ with |T₀| ≥ N
  obtain ⟨T₀, hT₀_shatt, hT₀_card⟩ := h_large N
  have : DecidableEq X := Classical.decEq X
  -- Take subset T ⊆ T₀ with |T| = N exactly (by Finset.exists_subset_card_eq)
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hT₀_card
  -- T is shattered (subset of shattered set)
  have hT_shatt : Shatters X C T := shatters_subset hT_sub hT₀_shatt
  set n := T.card with hn_def
  have hn_eq : n = N := hT_card
  -- Enumerate T injectively
  let eqv := T.equivFin.symm
  let pts : Fin n → X := fun i => (eqv i : X)
  have hpts_inj : Function.Injective pts :=
    fun _ _ h => eqv.injective (Subtype.val_injective h)
  -- Build sample from labeling: f ↦ (pts(i), f(i))
  let mkSample : (Fin n → Bool) → (Fin n → X × Bool) := fun f i => (pts i, f i)
  -- Shatters X C T → every labeling f is C-realizable on pts
  have h_realizable : ∀ f : Fin n → Bool, ∃ c ∈ C, ∀ i : Fin n, c (pts i) = f i := by
    intro f
    -- Convert f : Fin n → Bool to a labeling of T via eqv
    let f' : ↥T → Bool := fun ⟨x, hx⟩ => f (T.equivFin ⟨x, hx⟩)
    obtain ⟨c, hcC, hcf'⟩ := hT_shatt f'
    refine ⟨c, hcC, fun i => ?_⟩
    have := hcf' (eqv i)
    simp only [f', pts] at this ⊢
    rwa [show T.equivFin (eqv i) = i from T.equivFin.apply_symm_apply i] at this
  -- compress ∘ mkSample is injective (core pigeonhole step)
  -- Shatters gives C-realizability for each labeling, firing correctness
  have h_inj : Function.Injective (cs.compress ∘ mkSample) := by
    intro f g hfg
    exact compress_injective_on_labelings cs pts hpts_inj f g
      (h_realizable f) (h_realizable g) hfg
  -- Counting contradiction via pigeonhole principle.
  -- Target: all subsets of T ×ˢ {true, false} of size ≤ k
  set A := T ×ˢ (Finset.univ : Finset Bool) with hA_def
  set target := A.powerset.filter (fun S => S.card ≤ k) with htarget_def
  -- Each compressed set lands in target
  have h_maps_to : ∀ f : Fin n → Bool, (cs.compress ∘ mkSample) f ∈ target := by
    intro f
    simp only [Function.comp, htarget_def, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro p hp
      have hsub := cs.compress_sub (mkSample f)
      have hp_set : (p : X × Bool) ∈ (↑(cs.compress (mkSample f)) : Set (X × Bool)) :=
        Finset.mem_coe.mpr hp
      have hp_range : p ∈ Set.range (mkSample f) := hsub hp_set
      obtain ⟨i, hi⟩ := hp_range
      simp only [mkSample] at hi
      rw [Finset.mem_product]
      constructor
      · have : p.1 = pts i := (congr_arg Prod.fst hi).symm
        rw [this]; exact (eqv i).2
      · exact Finset.mem_univ _
    · have := cs.compress_small (mkSample f); omega
  -- Source cardinality: 2^n
  have h_source_card : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    simp [Fintype.card_fin, Fintype.card_bool]
  -- Target cardinality: |target| ≤ (k+1)·(2n)^k
  have hA_card : A.card = 2 * n := by
    simp [hA_def, Finset.card_product]; ring
  have h_target_le : target.card ≤ (k + 1) * (2 * n) ^ k := by
    calc target.card
        ≤ (Finset.range (k + 1)).sum (fun j => (A.powersetCard j).card) := by
          have : target ⊆ (Finset.range (k + 1)).biUnion (fun j => A.powersetCard j) := by
            intro S hS
            simp_all
          exact (Finset.card_le_card this).trans Finset.card_biUnion_le
      _ = (Finset.range (k + 1)).sum (fun j => (2 * n).choose j) := by
          simp [Finset.card_powersetCard, hA_card]
      _ ≤ (Finset.range (k + 1)).sum (fun _ => (2 * n) ^ k) := by
          apply Finset.sum_le_sum; intro j hj
          simp only [Finset.mem_range] at hj
          have hj_le : j ≤ k := by omega
          calc (2 * n).choose j ≤ (2 * n) ^ j := Nat.choose_le_pow _ _
            _ ≤ (2 * n) ^ k := by
                have hn_pos : 0 < n := by
                  rw [hn_eq, hN_def]; positivity
                have h2n_pos : 0 < 2 * n := by omega
                exact Nat.pow_le_pow_right h2n_pos hj_le
      _ = (k + 1) * (2 * n) ^ k := by simp [Finset.sum_const, Finset.card_range]
  -- Key inequality: (k+1)·(2n)^k < 2^n, using n = 2(k+1)² exactly
  have h_target_lt : target.card < 2 ^ n := by
    have hn_val : n = 2 * (k + 1) * (k + 1) := hn_eq.trans hN_def
    calc target.card ≤ (k + 1) * (2 * n) ^ k := h_target_le
      _ = (k + 1) * (2 * (2 * (k + 1) * (k + 1))) ^ k := by rw [hn_val]
      _ < 2 ^ (2 * (k + 1) * (k + 1)) := exp_beats_poly_at k
      _ = 2 ^ n := by rw [hn_val]
  -- Pigeonhole: more labelings than target slots → collision contradicts injectivity
  have h_card_lt : target.card < (Finset.univ : Finset (Fin n → Bool)).card := by
    rw [h_source_card]; exact h_target_lt
  exact absurd h_inj (by
    intro h_inj_false
    obtain ⟨f, _, g, _, hne, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_card_lt
        (fun x _ => h_maps_to x)
    exact absurd heq (fun h => hne (h_inj_false h)))
