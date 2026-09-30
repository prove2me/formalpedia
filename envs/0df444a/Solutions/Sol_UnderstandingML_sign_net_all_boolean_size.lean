-- Prove2me | solution 1 for UnderstandingML.sign_net_all_boolean_size
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T13:07:15.276595+00:00
-- url     : https://prove2.me/submissions/a7c9a8cf-1480-4485-9d3e-65cecbd4ab6f

import Definitions.Def_UnderstandingML_NeuralNetworks
import Theorems.Thm_UnderstandingML_vcDim_sign_net
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

namespace UnderstandingML

open Finset

/-- `|E| ≤ |V|²`. -/
lemma numEdges_le_size_sq (G : LayeredGraph) : G.numEdges ≤ G.size ^ 2 := by
  have hw : ∀ t ≤ G.depth, G.width t ≤ G.size := by
    intro t ht
    unfold LayeredGraph.size
    exact Finset.single_le_sum (f := G.width) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))
  have hsum : ∑ t ∈ range G.depth, G.width t ≤ G.size := by
    unfold LayeredGraph.size
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ _))
  calc G.numEdges = ∑ t ∈ range G.depth, (G.edges t).card := rfl
    _ ≤ ∑ t ∈ range G.depth, G.size * G.width t := by
        refine Finset.sum_le_sum (fun t ht => ?_)
        have hsub : G.edges t ⊆ range (G.width (t + 1)) ×ˢ range (G.width t) := by
          intro e he
          have := G.edges_valid t e he
          simp [Finset.mem_product, this.1, this.2]
        calc (G.edges t).card ≤ (range (G.width (t + 1)) ×ˢ range (G.width t)).card :=
              Finset.card_le_card hsub
          _ = G.width (t + 1) * G.width t := by simp
          _ ≤ G.size * G.width t :=
              Nat.mul_le_mul_right _ (hw _ (Finset.mem_range.mp ht))
    _ = G.size * ∑ t ∈ range G.depth, G.width t := by rw [Finset.mul_sum]
    _ ≤ G.size * G.size := Nat.mul_le_mul_left _ hsum
    _ = G.size ^ 2 := by ring

/-- The `{0,1}`-cube is shattered, so the VC dimension is at least `2^n`. -/
lemma two_pow_le_vcDim (n : ℕ) (G : LayeredGraph)
    (hG : ∀ f : (Fin n → Bool) → Bool, ∃ h ∈ signNetClass n G,
      ∀ x : Fin n → Bool, h (fun i ↦ if x i then (1 : ℝ) else 0) = f x) :
    ((2 ^ n : ℕ) : ℕ∞) ≤ vcDim (signNetClass n G) := by
  classical
  set enc : (Fin n → Bool) → (Fin n → ℝ) := fun x i ↦ if x i then (1 : ℝ) else 0 with henc
  have hinj : Function.Injective enc := by
    intro x y hxy
    funext i
    have := congrFun hxy i
    simp only [henc] at this
    cases hx : x i <;> cases hy : y i <;> simp_all
  set C := (univ : Finset (Fin n → Bool)).image enc with hC
  have hcard : C.card = 2 ^ n := by
    rw [hC, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  have hsh : Shatters (signNetClass n G) C := by
    intro g
    obtain ⟨h, hh, hhf⟩ := hG (fun x ↦ g ⟨enc x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩)
    refine ⟨h, hh, fun c => ?_⟩
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp c.2
    have hc : c = ⟨enc x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩ := Subtype.ext hx.symm
    rw [hc]
    exact hhf x
  rw [← hcard]
  exact le_iSup₂ (f := fun (C : Finset (Fin n → ℝ)) (_ : Shatters (signNetClass n G) C) =>
    (C.card : ℕ∞)) C hsh

lemma logb_le_two_mul_sub (V : ℝ) (hV : 1 ≤ V) : Real.logb 2 V ≤ 2 * (V - 1) := by
  have ha : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    norm_num at this ⊢; linarith
  have hl : Real.log V ≤ V - 1 := Real.log_le_sub_one_of_pos (by linarith)
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith

theorem sign_net_all_boolean_size_aux (n : ℕ) (G : LayeredGraph) (hd : 1 ≤ G.depth)
    (hG : ∀ f : (Fin n → Bool) → Bool, ∃ h ∈ signNetClass n G,
      ∀ x : Fin n → Bool, h (fun i ↦ if x i then (1 : ℝ) else 0) = f x) :
    (2 : ℝ) ^ ((n : ℝ) / 3) ≤ 2 * G.size := by
  have hvc := vcDim_sign_net n G hd (2 ^ n) (two_pow_le_vcDim n G hG)
  push_cast at hvc
  have hEV : (G.numEdges : ℝ) ≤ (G.size : ℝ) ^ 2 := by exact_mod_cast numEdges_le_size_sq G
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hE1 : (1 : ℝ) ≤ G.numEdges := by
    by_contra h
    have hE0 : G.numEdges = 0 := by
      have : (G.numEdges : ℝ) < 1 := lt_of_not_ge h
      exact_mod_cast (show (G.numEdges : ℝ) = 0 by
        have : G.numEdges < 1 := by exact_mod_cast this
        simp [Nat.lt_one_iff.mp this])
    rw [hE0] at hvc
    simp at hvc
    linarith
  set E : ℝ := (G.numEdges : ℝ) with hEdef
  set V : ℝ := (G.size : ℝ) with hVdef
  have hV1 : 1 ≤ V := by nlinarith
  have hlogE : 0 ≤ Real.logb 2 (16 * E) := Real.logb_nonneg (by norm_num) (by linarith)
  have hlogmono : Real.logb 2 (16 * E) ≤ Real.logb 2 (16 * V ^ 2) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have hlog16 : Real.logb 2 (16 * V ^ 2) = 4 + 2 * Real.logb 2 V := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow,
      show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    push_cast; ring
  have hlV := logb_le_two_mul_sub V hV1
  have hcube : (2 : ℝ) ^ n ≤ (2 * V) ^ 3 := by
    calc (2 : ℝ) ^ n ≤ 2 * E * Real.logb 2 (16 * E) := hvc
      _ ≤ 2 * V ^ 2 * Real.logb 2 (16 * V ^ 2) := by
          have h1 : 2 * E * Real.logb 2 (16 * E) ≤ 2 * V ^ 2 * Real.logb 2 (16 * E) := by
            nlinarith
          have h2 : 2 * V ^ 2 * Real.logb 2 (16 * E) ≤ 2 * V ^ 2 * Real.logb 2 (16 * V ^ 2) := by
            have : 0 ≤ 2 * V ^ 2 := by positivity
            exact mul_le_mul_of_nonneg_left hlogmono this
          linarith
      _ ≤ 2 * V ^ 2 * (4 * V) := by
          rw [hlog16]
          have : 0 ≤ 2 * V ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_left (by linarith) this
      _ = (2 * V) ^ 3 := by ring
  have hrpow : ((2 : ℝ) ^ ((n : ℝ) / 3)) ^ (3 : ℕ) = 2 ^ n := by
    rw [← Real.rpow_mul_natCast (by norm_num), show (n : ℝ) / 3 * ((3 : ℕ) : ℝ) = n by
      push_cast; ring, Real.rpow_natCast]
  rw [← hrpow] at hcube
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hcube

end UnderstandingML

open UnderstandingML in
theorem solution (n : ℕ) (G : LayeredGraph) (hd : 1 ≤ G.depth)
    (hG : ∀ f : (Fin n → Bool) → Bool, ∃ h ∈ signNetClass n G,
      ∀ x : Fin n → Bool, h (fun i ↦ if x i then (1 : ℝ) else 0) = f x) :
    (2 : ℝ) ^ ((n : ℝ) / 3) ≤ 2 * G.size :=
  sign_net_all_boolean_size_aux n G hd hG
