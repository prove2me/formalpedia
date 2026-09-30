-- Prove2me | solution 1 for UnderstandingML.vcDim_sign_net
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T13:04:26.120589+00:00
-- url     : https://prove2.me/submissions/bcb99bfc-eaba-435b-96af-3f4e29b7b921

import Definitions.Def_UnderstandingML_NeuralNetworks
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory

namespace UnderstandingML

open Finset Classical

/-- Sum of binomials bound: `∑_{k ≤ d} C(m, k) ≤ (m + 1)^d`. -/
lemma sum_choose_le_succ_pow (m d : ℕ) : ∑ k ∈ Iic d, m.choose k ≤ (m + 1) ^ d := by
  have hI : Iic d = range (d + 1) := by ext k; simp
  rw [add_pow, hI]
  refine Finset.sum_le_sum (fun k hk => ?_)
  have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 : 1 ≤ d.choose k := Nat.choose_pos hk'
  calc m.choose k ≤ m ^ k := Nat.choose_le_pow m k
    _ = m ^ k * 1 ^ (d - k) * 1 := by simp
    _ ≤ m ^ k * 1 ^ (d - k) * d.choose k := Nat.mul_le_mul_left _ h1

/-- A linear relation among the points kills shattering. -/
lemma not_shatter_of_relation {ι : Type*} [Fintype ι] (p : ι → ℕ → ℝ)
    (J : Finset ℕ) (s : Finset ι) (a : ι → ℝ) (hrel : ∀ l ∈ J, ∑ x ∈ s, a x * p x l = 0)
    (hpos : ∃ x ∈ s, 0 < a x) :
    ¬ ∀ t ⊆ s, ∃ v : ℕ → ℝ, ∀ x ∈ s, (x ∈ t ↔ 0 < ∑ l ∈ J, v l * p x l) := by
  intro hsh
  obtain ⟨v, hv⟩ := hsh (s.filter (fun x => 0 < a x)) (Finset.filter_subset _ _)
  obtain ⟨x0, hx0s, hx0⟩ := hpos
  have hzero : ∑ x ∈ s, a x * ∑ l ∈ J, v l * p x l = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro l hl
    have := hrel l hl
    calc ∑ x ∈ s, a x * (v l * p x l) = v l * ∑ x ∈ s, a x * p x l := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by ring)
      _ = 0 := by rw [this, mul_zero]
  have hnonneg : ∀ x ∈ s, 0 ≤ a x * ∑ l ∈ J, v l * p x l := by
    intro x hx
    have := hv x hx
    simp only [Finset.mem_filter, hx, true_and] at this
    by_cases hax : 0 < a x
    · exact mul_nonneg hax.le (this.mp hax).le
    · have h1 : ¬ 0 < ∑ l ∈ J, v l * p x l := fun h => hax (this.mpr h)
      exact mul_nonneg_of_nonpos_of_nonpos (not_lt.mp hax) (not_lt.mp h1)
  have hpos' : 0 < a x0 * ∑ l ∈ J, v l * p x0 l := by
    have := hv x0 hx0s
    simp only [Finset.mem_filter, hx0s, true_and] at this
    exact mul_pos hx0 (this.mp hx0)
  have : 0 < ∑ x ∈ s, a x * ∑ l ∈ J, v l * p x l :=
    Finset.sum_pos' hnonneg ⟨x0, hx0s, hpos'⟩
  linarith

/-- Sauer's lemma for one sign neuron: at most `(m+1)^{|J|}` patterns on `m` points. -/
lemma neuron_card {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ → ℝ) (J : Finset ℕ) :
    (univ.filter (fun g : ι → Bool => ∃ v : ℕ → ℝ, ∀ x, g x = decide (0 < ∑ l ∈ J, v l * p x l))).card
      ≤ (Fintype.card ι + 1) ^ J.card := by
  set F := univ.filter (fun g : ι → Bool =>
    ∃ v : ℕ → ℝ, ∀ x, g x = decide (0 < ∑ l ∈ J, v l * p x l)) with hF
  set T : (ι → Bool) → Finset ι := fun g => univ.filter (fun x => g x = true) with hT
  have hTinj : Function.Injective T := by
    intro g g' hgg
    funext x
    have := congrArg (fun u => x ∈ u) hgg
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
    cases hg : g x <;> cases hg' : g' x <;> simp_all
  set 𝒜 := F.image T with h𝒜
  have hcard : F.card = 𝒜.card := (Finset.card_image_of_injective F hTinj).symm
  have hvc : 𝒜.vcDim ≤ J.card := by
    unfold Finset.vcDim
    apply Finset.sup_le
    intro S hS
    rw [Finset.mem_shatterer] at hS
    by_contra hlt
    push Not at hlt
    let φ : S → (J → ℝ) := fun x l => p x l
    have hnli : ¬ LinearIndependent ℝ φ := by
      intro hli
      have := hli.fintype_card_le_finrank
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
      omega
    obtain ⟨g, hg, x1, hx1⟩ := Fintype.not_linearIndependent_iff.mp hnli
    let a : ι → ℝ := fun x => if h : x ∈ S then g ⟨x, h⟩ else 0
    have hrel : ∀ l ∈ J, ∑ x ∈ S, a x * p x l = 0 := by
      intro l hl
      have := congrFun hg ⟨l, hl⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, φ] at this
      rw [← this, ← Finset.sum_coe_sort S]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp [a, x.2]
    have hsh : ∀ t ⊆ S, ∃ v : ℕ → ℝ, ∀ x ∈ S, (x ∈ t ↔ 0 < ∑ l ∈ J, v l * p x l) := by
      intro t ht
      obtain ⟨u, hu, hSu⟩ := hS ht
      rw [h𝒜, Finset.mem_image] at hu
      obtain ⟨g', hg'F, rfl⟩ := hu
      rw [hF, Finset.mem_filter] at hg'F
      obtain ⟨v, hv⟩ := hg'F.2
      refine ⟨v, fun x hx => ?_⟩
      rw [← hSu]
      simp [hT, hx, hv x]
    by_cases hp : ∃ x ∈ S, 0 < a x
    · exact not_shatter_of_relation p J S a hrel hp hsh
    · push Not at hp
      refine not_shatter_of_relation p J S (fun x => - a x) ?_ ?_ hsh
      · intro l hl
        have := hrel l hl
        simp only [neg_mul, Finset.sum_neg_distrib, this, neg_zero]
      · refine ⟨x1, x1.2, ?_⟩
        have h1 : a x1 = g x1 := by simp [a, x1.2]
        have h2 := hp x1 x1.2
        have h3 : a x1 ≠ 0 := by rw [h1]; exact hx1
        exact neg_pos.mpr (lt_of_le_of_ne h2 h3)
  calc F.card = 𝒜.card := hcard
    _ ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
    _ ≤ ∑ k ∈ Iic 𝒜.vcDim, (Fintype.card ι).choose k := Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ Iic J.card, (Fintype.card ι).choose k :=
        Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr hvc)
    _ ≤ (Fintype.card ι + 1) ^ J.card := sum_choose_le_succ_pow _ _

/-- One layer of sign neurons. -/
lemma layer_card {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ → ℝ) (W W' : ℕ)
    (E : Finset (ℕ × ℕ)) (hE : ∀ e ∈ E, e.1 < W' ∧ e.2 < W) :
    (univ.filter (fun g : ι → Fin W' → Bool => ∃ v : ℕ → ℕ → ℝ, ∀ x k,
        g x k = decide (0 < ∑ l ∈ range W, (if ((k : ℕ), l) ∈ E then v k l else 0) * p x l))).card
      ≤ (Fintype.card ι + 1) ^ E.card := by
  set J : ℕ → Finset ℕ := fun k => (range W).filter (fun l => (k, l) ∈ E) with hJ
  set N : Fin W' → Finset (ι → Bool) := fun k => univ.filter (fun h : ι → Bool =>
    ∃ v : ℕ → ℝ, ∀ x, h x = decide (0 < ∑ l ∈ J k, v l * p x l)) with hN
  set Φ : (ι → Fin W' → Bool) → (Fin W' → ι → Bool) := fun g k x => g x k with hΦ
  have hΦinj : Function.Injective Φ := by
    intro g g' h; funext x k; exact congrFun (congrFun h k) x
  have hsub : (univ.filter (fun g : ι → Fin W' → Bool => ∃ v : ℕ → ℕ → ℝ, ∀ x k,
        g x k = decide (0 < ∑ l ∈ range W, (if ((k : ℕ), l) ∈ E then v k l else 0) * p x l))).image Φ
      ⊆ Fintype.piFinset N := by
    intro f hf
    rw [Finset.mem_image] at hf
    obtain ⟨g, hg, rfl⟩ := hf
    rw [Finset.mem_filter] at hg
    obtain ⟨v, hv⟩ := hg.2
    rw [Fintype.mem_piFinset]
    intro k
    rw [hN, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, v k, fun x => ?_⟩
    show g x k = _
    rw [hv x k, hJ, Finset.sum_filter]
    congr 2
    refine Finset.sum_congr rfl (fun l _ => ?_)
    split_ifs <;> simp
  have hJcard : ∑ k : Fin W', (J k).card = E.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := range W')
      (fun e he => Finset.mem_range.mpr (hE e he).1)]
    rw [Fin.sum_univ_eq_sum_range (fun k => (J k).card) W']
    refine Finset.sum_congr rfl (fun k _ => ?_)
    symm
    refine Finset.card_bij (fun e _ => e.2) ?_ ?_ ?_
    · intro e he
      rcases e with ⟨a, b⟩
      rw [Finset.mem_filter] at he
      obtain ⟨he1, rfl⟩ := he
      rw [hJ, Finset.mem_filter, Finset.mem_range]
      exact ⟨(hE _ he1).2, he1⟩
    · intro e he e' he' h
      rw [Finset.mem_filter] at he he'
      exact Prod.ext (he.2.trans he'.2.symm) h
    · intro l hl
      rw [hJ, Finset.mem_filter] at hl
      exact ⟨(k, l), by rw [Finset.mem_filter]; exact ⟨hl.2, rfl⟩, rfl⟩
  rw [← Finset.card_image_of_injective _ hΦinj]
  calc _ ≤ (Fintype.piFinset N).card := Finset.card_le_card hsub
    _ = ∏ k, (N k).card := Fintype.card_piFinset N
    _ ≤ ∏ k : Fin W', (Fintype.card ι + 1) ^ (J k).card :=
        Finset.prod_le_prod' (fun k _ => neuron_card p (J k))
    _ = (Fintype.card ι + 1) ^ E.card := by rw [Finset.prod_pow_eq_pow_sum, hJcard]

/-- The sign patterns of layer `s + 1` on a finite set of inputs. -/
noncomputable def layerPat (n : ℕ) (G : LayeredGraph) (C : Finset (Fin n → ℝ)) (w : ℕ → ℕ → ℕ → ℝ)
    (s : ℕ) : C → Fin (G.width (s + 1)) → Bool :=
  fun x k => decide (0 < netInput signAct G w (inputLayer (x : Fin n → ℝ)) s k)

lemma layerPat_card (n : ℕ) (G : LayeredGraph) (C : Finset (Fin n → ℝ)) (s : ℕ) :
    (univ.filter (fun g => ∃ w, layerPat n G C w s = g)).card ≤
      (C.card + 1) ^ (∑ t ∈ range (s + 1), (G.edges t).card) := by
  induction s with
  | zero =>
    rw [Finset.sum_range_one, ← Fintype.card_coe C]
    refine le_trans (Finset.card_le_card ?_) (layer_card (fun (x : C) l => inputLayer (x : Fin n → ℝ) l)
      (G.width 0) (G.width (0 + 1)) (G.edges 0) (G.edges_valid 0))
    intro g hg
    rw [Finset.mem_filter] at hg ⊢
    obtain ⟨w, rfl⟩ := hg.2
    exact ⟨Finset.mem_univ _, w 0, fun x k => rfl⟩
  | succ s ih =>
    set A := univ.filter (fun g => ∃ w, layerPat n G C w s = g) with hA
    let pB : (C → Fin (G.width (s + 1)) → Bool) → C → ℕ → ℝ := fun B x l =>
      if h : l < G.width (s + 1) then (if B x ⟨l, h⟩ then 1 else -1) else 0
    have hsub : univ.filter (fun g => ∃ w, layerPat n G C w (s + 1) = g) ⊆
        A.biUnion (fun B => univ.filter (fun g : C → Fin (G.width (s + 1 + 1)) → Bool =>
          ∃ v : ℕ → ℕ → ℝ, ∀ x k, g x k = decide (0 < ∑ l ∈ range (G.width (s + 1)),
            (if ((k : ℕ), l) ∈ G.edges (s + 1) then v k l else 0) * pB B x l))) := by
      intro g hg
      rw [Finset.mem_filter] at hg
      obtain ⟨w, rfl⟩ := hg.2
      rw [Finset.mem_biUnion]
      refine ⟨layerPat n G C w s, by rw [hA, Finset.mem_filter]; exact ⟨Finset.mem_univ _, w, rfl⟩, ?_⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, w (s + 1), fun x k => ?_⟩
      show decide (0 < netInput signAct G w (inputLayer (x : Fin n → ℝ)) (s + 1) k) = _
      unfold netInput
      congr 2
      refine Finset.sum_congr rfl (fun l hl => ?_)
      congr 1
      have hl' : l < G.width (s + 1) := Finset.mem_range.mp hl
      simp only [pB, hl', dif_pos, layerPat]
      show signAct (netInput signAct G w (inputLayer (x : Fin n → ℝ)) s l) = _
      unfold signAct
      simp
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ B ∈ A, (C.card + 1) ^ (G.edges (s + 1)).card := by
          refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum (fun B _ => ?_))
          rw [← Fintype.card_coe C]
          exact layer_card (pB B) _ _ _ (G.edges_valid (s + 1))
      _ = A.card * (C.card + 1) ^ (G.edges (s + 1)).card := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (C.card + 1) ^ (∑ t ∈ range (s + 1), (G.edges t).card) *
            (C.card + 1) ^ (G.edges (s + 1)).card := Nat.mul_le_mul_right _ ih
      _ = _ := by rw [Finset.sum_range_succ _ (s + 1), pow_add]

lemma pow_le_of_shatter (n : ℕ) (G : LayeredGraph) (hd : 1 ≤ G.depth) (C : Finset (Fin n → ℝ))
    (hC : Shatters (signNetClass n G) C) : 2 ^ C.card ≤ (C.card + 1) ^ G.numEdges := by
  obtain ⟨s, hs⟩ : ∃ s, G.depth = s + 1 := ⟨G.depth - 1, by omega⟩
  have hs' : G.depth - 1 = s := by omega
  set A := univ.filter (fun g => ∃ w, layerPat n G C w s = g) with hA
  let F : (C → Fin (G.width (s + 1)) → Bool) → (C → Bool) := fun B x =>
    if h : 0 < G.width (s + 1) then B x ⟨0, h⟩ else false
  have hsub : (univ : Finset (C → Bool)) ⊆ A.image F := by
    intro g _
    obtain ⟨h, hh, hhg⟩ := hC g
    obtain ⟨w, rfl⟩ := hh
    rw [Finset.mem_image]
    refine ⟨layerPat n G C w s, by rw [hA, Finset.mem_filter]; exact ⟨Finset.mem_univ _, w, rfl⟩, ?_⟩
    funext x
    rw [← hhg x]
    simp only [F, hs']
    split_ifs with hw
    · rfl
    · have h0 : netInput signAct G w (inputLayer (x : Fin n → ℝ)) s 0 = 0 := by
        unfold netInput
        apply Finset.sum_eq_zero
        intro l _
        have : (0, l) ∉ G.edges s := fun he => hw (by simpa using (G.edges_valid s _ he).1)
        simp [this]
      simp [h0]
  have hnum : G.numEdges = ∑ t ∈ range (s + 1), (G.edges t).card := by
    rw [LayeredGraph.numEdges, hs]
  calc 2 ^ C.card = (univ : Finset (C → Bool)).card := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    _ ≤ (A.image F).card := Finset.card_le_card hsub
    _ ≤ A.card := Finset.card_image_le
    _ ≤ _ := layerPat_card n G C s
    _ = _ := by rw [hnum]

lemma arith_bound (M E : ℕ) (h : 2 ^ M ≤ (M + 1) ^ E) :
    (M : ℝ) ≤ 2 * E * Real.logb 2 (16 * E) := by
  rcases Nat.eq_zero_or_pos E with hE | hE
  · subst hE
    simp only [pow_zero] at h
    have : M = 0 := by
      by_contra hM
      have : 2 ≤ 2 ^ M := Nat.le_self_pow hM 2
      omega
    simp [this]
  have hE1 : (1 : ℝ) ≤ E := by exact_mod_cast hE
  have ha : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    norm_num at this ⊢; linarith
  have hlogM : (M : ℝ) * Real.log 2 ≤ E * Real.log (M + 1) := by
    have h' : ((2 : ℝ)) ^ M ≤ ((M : ℝ) + 1) ^ E := by exact_mod_cast h
    have := Real.log_le_log (by positivity) h'
    rwa [Real.log_pow, Real.log_pow] at this
  have h4E : (0 : ℝ) < 4 * E := by positivity
  have htan : Real.log (M + 1) ≤ Real.log (4 * E) + (M + 1) / (4 * E) - 1 := by
    have := Real.log_le_sub_one_of_pos (x := (M + 1) / (4 * E)) (by positivity)
    rw [Real.log_div (by positivity) h4E.ne'] at this
    linarith
  have hL : 0 ≤ Real.log (4 * E) := Real.log_nonneg (by linarith)
  have h16 : Real.log (16 * E) = Real.log (4 * E) + 2 * Real.log 2 := by
    rw [show (16 : ℝ) * E = 4 * E * 2 ^ 2 by ring, Real.log_mul h4E.ne' (by norm_num), Real.log_pow]
    push_cast; ring
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hmain : (M : ℝ) * Real.log 2 ≤ 2 * E * Real.log (16 * E) := by
    have h1 : (M : ℝ) * Real.log 2 ≤ E * Real.log (4 * E) + (M + 1) / 4 - E := by
      have : (E : ℝ) * ((M + 1) / (4 * E)) = (M + 1) / 4 := by field_simp
      nlinarith
    rw [h16]
    nlinarith
  rw [Real.logb, mul_div_assoc']
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem vcDim_sign_net_aux (n : ℕ) (G : LayeredGraph) (hd : 1 ≤ G.depth) (m : ℕ)
    (hm : (m : ℕ∞) ≤ vcDim (signNetClass n G)) :
    (m : ℝ) ≤ 2 * G.numEdges * Real.logb 2 (16 * G.numEdges) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    exact_mod_cast arith_bound 0 G.numEdges (by simp)
  obtain ⟨C, hC, hmC⟩ : ∃ C : Finset (Fin n → ℝ), Shatters (signNetClass n G) C ∧ m ≤ C.card := by
    by_contra hne
    push Not at hne
    have hle : vcDim (signNetClass n G) ≤ ((m - 1 : ℕ) : ℕ∞) := by
      unfold vcDim
      refine iSup₂_le (fun C hC => ?_)
      exact_mod_cast Nat.le_pred_of_lt (hne C hC)
    have := hm.trans hle
    have : m ≤ m - 1 := by exact_mod_cast this
    omega
  have hbound := arith_bound C.card G.numEdges (pow_le_of_shatter n G hd C hC)
  have : (m : ℝ) ≤ C.card := by exact_mod_cast hmC
  linarith

end UnderstandingML

open UnderstandingML in
theorem solution (n : ℕ) (G : LayeredGraph) (hd : 1 ≤ G.depth) (m : ℕ)
    (hm : (m : ℕ∞) ≤ vcDim (signNetClass n G)) :
    (m : ℝ) ≤ 2 * G.numEdges * Real.logb 2 (16 * G.numEdges) :=
  vcDim_sign_net_aux n G hd m hm
