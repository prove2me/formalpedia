-- Prove2me | solution 1 for compression_with_info_imp_vcdim_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:39:23.504794+00:00
-- url     : https://prove2.me/submissions/9d381c03-c1d9-43fe-b164-139aa7da1a35

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_FiniteSupportUC
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Compression
public import Theorems.Thm_compress_with_info_injective_on_labelings
section
@[expose] public section
open Finset
noncomputable section
universe u
attribute [local instance] Classical.propDecidable
private lemma shatters_subset_compression {X : Type u} {C : ConceptClass X Bool}
    {S T : Finset X} (hST : T ⊆ S) (hS : Shatters X C S) : Shatters X C T := by
  intro f
  let g : ↥S → Bool := fun ⟨x, hx⟩ => if h : x ∈ T then f ⟨x, h⟩ else false
  obtain ⟨c, hcC, hcg⟩ := hS g
  exact ⟨c, hcC, fun ⟨x, hx⟩ => by
    have := hcg ⟨x, hST hx⟩; simp only [g, hx, dite_true] at this; exact this⟩
private lemma succ_le_two_pow_compression (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => calc k + 1 + 1 ≤ 2 ^ k + 2 ^ k := by omega
                   _ = 2 ^ (k + 1) := by ring
private lemma exp_beats_poly_compression (s : ℕ) :
    (s + 1) ^ 2 * (4 * (s + 1) ^ 2) ^ s < 2 ^ (2 * (s + 1) * (s + 1)) := by
  -- (s+1)^2 * (4(s+1)^2)^s = (s+1)^(2s+2) * 4^s
  have h1 : (s + 1) ^ 2 * (4 * (s + 1) ^ 2) ^ s =
    (s + 1) ^ (2 * s + 2) * 4 ^ s := by rw [mul_pow, ← pow_mul]; ring_nf
  rw [h1]
  -- (s+1)^(2s+2) ≤ (2^s)^(2s+2)
  have h2 : (s + 1) ^ (2 * s + 2) ≤ (2 ^ s) ^ (2 * s + 2) :=
    Nat.pow_le_pow_left (succ_le_two_pow_compression s) _
  -- 4^s = 2^(2s)
  have h3 : (4 : ℕ) ^ s = 2 ^ (2 * s) := by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul]
  rw [h3]
  calc (s + 1) ^ (2 * s + 2) * 2 ^ (2 * s)
      ≤ (2 ^ s) ^ (2 * s + 2) * 2 ^ (2 * s) := Nat.mul_le_mul_right _ h2
    _ = 2 ^ (s * (2 * s + 2) + 2 * s) := by rw [← pow_mul, ← pow_add]
    _ = 2 ^ (2 * s ^ 2 + 4 * s) := by ring_nf
    _ < 2 ^ (2 * (s + 1) * (s + 1)) := by
        apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
        nlinarith
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
universe u
attribute [local instance] Classical.propDecidable
theorem _root_.solution
    (X : Type u) (C : ConceptClass X Bool)
    (hcomp : ∃ (k : ℕ) (cs : CompressionSchemeWithInfo X Bool C), cs.size = k) :
    VCDim X C < ⊤ := by
  by_contra h_top
  push Not at h_top; rw [top_le_iff] at h_top
  obtain ⟨k, cs, hk⟩ := hcomp
  have h_large : ∀ n : ℕ, ∃ S : Finset X, Shatters X C S ∧ n ≤ S.card := by
    intro n; by_contra h_neg; push Not at h_neg
    have : VCDim X C ≤ ↑n := by
      apply iSup₂_le; intro S hS
      exact_mod_cast Nat.le_of_lt_succ (Nat.lt_succ_of_lt (h_neg S hS))
    exact absurd h_top (ne_of_lt (lt_of_le_of_lt this (WithTop.coe_lt_top _)))
  set K := cs.kernelSize with hK_def
  set I := @Fintype.card cs.Info cs.infoFinite with hI_def
  set s := K + I with hs_def
  set N := 2 * (s + 1) * (s + 1) with hN_def
  obtain ⟨T₀, hT₀_shatt, hT₀_card⟩ := h_large N
  have : DecidableEq X := Classical.decEq X
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hT₀_card
  have hT_shatt : Shatters X C T := shatters_subset_compression hT_sub hT₀_shatt
  set n := T.card with hn_def
  have hn_eq : n = N := hT_card
  let eqv := T.equivFin.symm
  let pts : Fin n → X := fun i => (eqv i : X)
  have hpts_inj : Function.Injective pts :=
    fun _ _ h => eqv.injective (Subtype.val_injective h)
  let mkSample : (Fin n → Bool) → (Fin n → X × Bool) := fun f i => (pts i, f i)
  have h_realizable : ∀ f : Fin n → Bool, ∃ c ∈ C, ∀ i : Fin n, c (pts i) = f i := by
    intro f
    let f' : ↥T → Bool := fun ⟨x, hx⟩ => f (T.equivFin ⟨x, hx⟩)
    obtain ⟨c, hcC, hcf'⟩ := hT_shatt f'
    exact ⟨c, hcC, fun i => by
      have := hcf' (eqv i); simp only [f', pts] at this ⊢
      rwa [T.equivFin.apply_symm_apply i] at this⟩
  have h_inj : Function.Injective (cs.compress ∘ mkSample) := by
    intro f g hfg
    exact compress_with_info_injective_on_labelings cs pts hpts_inj f g
      (h_realizable f) (h_realizable g) hfg
  -- Target: (kernel subsets of T×Bool with card ≤ K) × Info
  set A := T ×ˢ (Finset.univ : Finset Bool) with hA_def
  set target := (A.powerset.filter (fun S => S.card ≤ K)) ×ˢ
    (@Finset.univ cs.Info cs.infoFinite) with htarget_def
  have h_maps_to : ∀ f : Fin n → Bool, (cs.compress ∘ mkSample) f ∈ target := by
    intro f
    simp only [Function.comp, htarget_def, Finset.mem_product, Finset.mem_filter,
      Finset.mem_powerset, Finset.mem_univ, and_true]
    constructor
    · intro p hp
      have hsub := cs.compress_sub (mkSample f)
      have hp_range := hsub (Finset.mem_coe.mpr hp)
      obtain ⟨i, hi⟩ := hp_range
      simp only [mkSample] at hi
      rw [Finset.mem_product]
      exact ⟨by rw [show p.1 = pts i from (congr_arg Prod.fst hi).symm]; exact (eqv i).2,
             Finset.mem_univ _⟩
    · exact cs.compress_small (mkSample f)
  -- Cardinality bounds
  have hA_card : A.card = 2 * n := by simp [hA_def, Finset.card_product]; ring
  have hn_pos : 0 < n := by rw [hn_eq, hN_def]; positivity
  have h_target_card : target.card ≤ (K + 1) * (2 * n) ^ K * I := by
    simp only [htarget_def, Finset.card_product]
    apply Nat.mul_le_mul_right
    calc (A.powerset.filter (fun S => S.card ≤ K)).card
        ≤ (Finset.range (K + 1)).sum (fun j => (A.powersetCard j).card) := by
          have hsub : A.powerset.filter (fun S => S.card ≤ K) ⊆
              (Finset.range (K + 1)).biUnion (fun j => A.powersetCard j) := by
            intro S hS
            simp_all
          exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      _ = (Finset.range (K + 1)).sum (fun j => (2 * n).choose j) := by
          congr 1; ext j; simp [Finset.card_powersetCard, hA_card]
      _ ≤ (Finset.range (K + 1)).sum (fun _ => (2 * n) ^ K) := by
          apply Finset.sum_le_sum; intro j hj
          simp only [Finset.mem_range] at hj
          calc (2 * n).choose j ≤ (2 * n) ^ j := Nat.choose_le_pow _ _
            _ ≤ (2 * n) ^ K := Nat.pow_le_pow_right (by omega) (by omega)
      _ = (K + 1) * (2 * n) ^ K := by simp [Finset.sum_const, Finset.card_range]
  have h_source_card : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    simp [Fintype.card_fin, Fintype.card_bool]
  have h_target_lt : target.card < 2 ^ n := by
    have hn_val : n = 2 * (s + 1) * (s + 1) := hn_eq.trans hN_def
    have hK_le : K + 1 ≤ s + 1 := by omega
    have hI_le : I ≤ s + 1 := by omega
    have hK_le' : K ≤ s := by omega
    calc target.card
        ≤ (K + 1) * (2 * n) ^ K * I := h_target_card
      _ ≤ (s + 1) * (2 * n) ^ s * (s + 1) := by
          apply Nat.mul_le_mul (Nat.mul_le_mul hK_le
            (Nat.pow_le_pow_right (by omega) hK_le')) hI_le
      _ = (s + 1) ^ 2 * (2 * n) ^ s := by ring
      _ = (s + 1) ^ 2 * (2 * (2 * (s + 1) * (s + 1))) ^ s := by rw [hn_val]
      _ = (s + 1) ^ 2 * (4 * (s + 1) ^ 2) ^ s := by ring_nf
      _ < 2 ^ (2 * (s + 1) * (s + 1)) := exp_beats_poly_compression s
      _ = 2 ^ n := by rw [hn_val]
  have h_card_lt : target.card < (Finset.univ : Finset (Fin n → Bool)).card := by
    rw [h_source_card]; exact h_target_lt
  exact absurd h_inj (by
    intro h_inj_false
    obtain ⟨f, _, g, _, hne, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_card_lt (fun x _ => h_maps_to x)
    exact absurd heq (fun h => hne (h_inj_false h)))
