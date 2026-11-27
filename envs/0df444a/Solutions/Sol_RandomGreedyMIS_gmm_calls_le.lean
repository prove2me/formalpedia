-- Prove2me | solution 1 for RandomGreedyMIS.gmm_calls_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:35:29.699546+00:00
-- url     : https://prove2.me/submissions/a6267410-320e-48ba-acf6-1e86cc025837

import Mathlib
import Definitions.Def_GraphMatching_basic
import Definitions.Def_RandomGreedyMIS_basic
import Definitions.Def_RandomGreedyMIS_matching
import Theorems.Thm_RandomGreedyMIS_total_calls_le
import Theorems.Thm_GraphMatching_maximal_matching_half

namespace MTSPRG
open Finset RandomGreedyMIS
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-! ### Characterisations -/

lemma inMIS_eq_true (π : Equiv.Perm (Fin n)) (v : Fin n) :
    inMIS G π v = true ↔ ∀ w, G.Adj v w → π w < π v → inMIS G π w = false := by
  rw [inMIS]
  simp only [List.all_eq_true, List.mem_finRange, true_implies]
  constructor
  · intro h w hw hlt
    have := h w
    rw [dif_pos ⟨hw, hlt⟩] at this
    simpa using this
  · intro h w
    split_ifs with hw
    · simpa using h w hw.1 hw.2
    · rfl


end MTSPRG

namespace MTSPGMM
open Finset GraphMatching RandomGreedyMIS
section Matching

variable {W : Type*}

theorem isMatching_empty (H : SimpleGraph W) : IsMatching H ∅ := by
  simp [IsMatching]

variable [Fintype W] {H : SimpleGraph W}

theorem card_le_matchingNumber {M : Finset (Sym2 W)} (hM : IsMatching H M) :
    M.card ≤ matchingNumber H := by
  classical
  unfold matchingNumber
  exact Finset.le_sup (f := Finset.card) (mem_filter.2 ⟨mem_univ _, hM⟩)

theorem exists_matching_card (H : SimpleGraph W) :
    ∃ M, IsMatching H M ∧ M.card = matchingNumber H := by
  classical
  unfold matchingNumber
  obtain ⟨M, hM, h⟩ := Finset.exists_mem_eq_sup
    ((univ : Finset (Finset (Sym2 W))).filter (IsMatching H))
    ⟨∅, mem_filter.2 ⟨mem_univ _, isMatching_empty H⟩⟩ Finset.card
  exact ⟨M, (mem_filter.1 hM).2, h.symm⟩

theorem vcNumber_le {C : Finset W} (hC : IsVC H C) : vcNumber H ≤ C.card := by
  classical
  unfold vcNumber
  exact Nat.find_min' _ ⟨C, hC, rfl⟩

theorem exists_vc_card (H : SimpleGraph W) : ∃ C, IsVC H C ∧ C.card = vcNumber H := by
  classical
  unfold vcNumber
  exact Nat.find_spec (⟨_, univ, isVC_univ H, rfl⟩ : ∃ n, ∃ C : Finset W, IsVC H C ∧ C.card = n)

/-- Weak LP duality: a matching has size at most the value of any fractional vertex cover. -/
theorem card_le_sum_of_frac {M : Finset (Sym2 W)} (hM : IsMatching H M) (Y : W → ℝ)
    (hY0 : ∀ x, 0 ≤ Y x) (hY : ∀ x z, H.Adj x z → 1 ≤ Y x + Y z) :
    (M.card : ℝ) ≤ ∑ x, Y x := by
  classical
  let F : Sym2 W → Finset W := fun e => univ.filter (· ∈ e)
  have h1 : ∀ e ∈ M, (1 : ℝ) ≤ ∑ x ∈ F e, Y x := by
    intro e he
    have hE := hM.1 e he
    induction e using Sym2.ind with
    | h a b =>
      have hab : H.Adj a b := hE
      have hne : a ≠ b := hab.ne
      have : F s(a, b) = {a, b} := by
        ext x; simp [F]
      rw [this, sum_pair hne]
      exact hY a b hab
  have hdisj : (M : Set (Sym2 W)).PairwiseDisjoint F := by
    intro e he f hf hef
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [F, mem_filter, mem_univ, true_and] at hx hx'
    exact hM.2 e he f hf hef x hx hx'
  calc (M.card : ℝ) = ∑ _e ∈ M, (1 : ℝ) := by simp
    _ ≤ ∑ e ∈ M, ∑ x ∈ F e, Y x := sum_le_sum h1
    _ = ∑ x ∈ M.biUnion F, Y x := (sum_biUnion hdisj).symm
    _ ≤ ∑ x, Y x := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ => hY0 x)

/-- Any matching is at most as large as any vertex cover. -/
theorem matching_le_vc {M : Finset (Sym2 W)} {C : Finset W} (hM : IsMatching H M)
    (hC : IsVC H C) : M.card ≤ C.card := by
  classical
  have := card_le_sum_of_frac hM (fun x => if x ∈ C then (1 : ℝ) else 0)
    (fun x => by split_ifs <;> norm_num)
    (fun x z hxz => by
      rcases hC x z hxz with h | h <;> simp only [h, if_true] <;> split_ifs <;> norm_num)
  rw [sum_boole] at this
  have hC' : (univ.filter (· ∈ C)) = C := by ext; simp
  rw [hC'] at this
  exact_mod_cast this

theorem matchingNumber_le_vcNumber (H : SimpleGraph W) : matchingNumber H ≤ vcNumber H := by
  obtain ⟨M, hM, hMc⟩ := exists_matching_card H
  obtain ⟨C, hC, hCc⟩ := exists_vc_card H
  rw [← hMc, ← hCc]
  exact matching_le_vc hM hC

/-- A maximal matching is a 2-approximation of the maximum matching. -/
theorem maximal_matching_half_local {M : Finset (Sym2 W)} (_hM : IsMatching H M)
    (hmax : ∀ e ∈ H.edgeSet, ∃ f ∈ M, ∃ x, x ∈ e ∧ x ∈ f) :
    matchingNumber H ≤ 2 * M.card := by
  classical
  let F : Sym2 W → Finset W := fun e => univ.filter (· ∈ e)
  have hC : IsVC H (M.biUnion F) := by
    intro x z hxz
    obtain ⟨f, hf, w, hw, hwf⟩ := hmax s(x, z) hxz
    rcases Sym2.mem_iff.1 hw with rfl | rfl
    · left; exact mem_biUnion.2 ⟨f, hf, by simp [F, hwf]⟩
    · right; exact mem_biUnion.2 ⟨f, hf, by simp [F, hwf]⟩
  have hF : ∀ e ∈ M, (F e).card ≤ 2 := by
    intro e _
    induction e using Sym2.ind with
    | h a b =>
      calc (F s(a, b)).card ≤ ({a, b} : Finset W).card := by
            apply card_le_card; intro x; simp [F]
        _ ≤ 2 := card_le_two
  calc matchingNumber H ≤ vcNumber H := matchingNumber_le_vcNumber H
    _ ≤ (M.biUnion F).card := vcNumber_le hC
    _ ≤ ∑ e ∈ M, (F e).card := card_biUnion_le
    _ ≤ ∑ _e ∈ M, 2 := sum_le_sum hF
    _ = 2 * M.card := by rw [sum_const, smul_eq_mul, mul_comm]


end Matching

noncomputable section LineGraph
variable {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
lemma edgeEnum_inj : Function.Injective (fun i => ((edgeEnum H i : H.edgeFinset) : Sym2 (Fin n))) :=
  Subtype.val_injective.comp (edgeEnum H).injective

theorem gm_isMatching (σ : Equiv.Perm (Fin H.edgeFinset.card)) : IsMatching H (GM H σ) := by
  constructor
  · intro f hf
    obtain ⟨i, -, rfl⟩ := mem_image.1 hf
    exact SimpleGraph.mem_edgeFinset.1 (edgeEnum H i).2
  · intro f hf g hg hfg x hxf hxg
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hf
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hg
    have hij : i ≠ j := fun h => hfg (h ▸ rfl)
    have hi' := (mem_filter.1 hi).2
    have hj' := (mem_filter.1 hj).2
    have hadj : (lineGraph H).Adj i j := ⟨hij, x, hxf, hxg⟩
    rcases lt_or_gt_of_ne (σ.injective.ne hij) with h | h
    · have := (MTSPRG.inMIS_eq_true (lineGraph H) σ j).1 hj' i hadj.symm h
      rw [hi'] at this; exact Bool.noConfusion this
    · have := (MTSPRG.inMIS_eq_true (lineGraph H) σ i).1 hi' j hadj h
      rw [hj'] at this; exact Bool.noConfusion this

theorem gm_maximal (σ : Equiv.Perm (Fin H.edgeFinset.card)) :
    ∀ f ∈ H.edgeSet, ∃ g ∈ GM H σ, ∃ x, x ∈ f ∧ x ∈ g := by
  intro f hf
  have hf' : f ∈ H.edgeFinset := SimpleGraph.mem_edgeFinset.2 hf
  set i := (edgeEnum H).symm ⟨f, hf'⟩ with hi
  have hei : ((edgeEnum H i : H.edgeFinset) : Sym2 (Fin n)) = f := by simp [hi]
  by_cases h : inMIS (lineGraph H) σ i = true
  · refine ⟨f, mem_image.2 ⟨i, mem_filter.2 ⟨mem_univ _, h⟩, hei⟩, ?_⟩
    induction f using Sym2.ind with
    | h a b => exact ⟨a, Sym2.mem_mk_left a b, Sym2.mem_mk_left a b⟩
  · rw [MTSPRG.inMIS_eq_true] at h
    push Not at h
    obtain ⟨w, hadj, -, hw⟩ := h
    simp only [Bool.not_eq_false] at hw
    obtain ⟨-, x, hx1, hx2⟩ := hadj
    exact ⟨_, mem_image.2 ⟨w, mem_filter.2 ⟨mem_univ _, hw⟩, rfl⟩, x, hei ▸ hx1, hx2⟩

theorem gm_card_bounds (σ : Equiv.Perm (Fin H.edgeFinset.card)) :
    matchingNumber H ≤ 2 * (GM H σ).card ∧ (GM H σ).card ≤ matchingNumber H :=
  ⟨GraphMatching.maximal_matching_half H _ (gm_isMatching H σ) (gm_maximal H σ),
    card_le_matchingNumber (gm_isMatching H σ)⟩

/-! ### Counting line-graph edges and the call bound -/

/-- Line-graph vertices (edges of `H`) incident to `v`. -/
def incL (v : Fin n) : Finset (Fin H.edgeFinset.card) :=
  univ.filter (fun i => v ∈ ((edgeEnum H i : H.edgeFinset) : Sym2 (Fin n)))

lemma card_incL (v : Fin n) : (incL H v).card = H.degree v := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  refine card_bij (fun i _ => ((edgeEnum H i : H.edgeFinset) : Sym2 (Fin n))) ?_ ?_ ?_
  · intro i hi
    rw [SimpleGraph.mem_incidenceFinset]
    exact ⟨SimpleGraph.mem_edgeFinset.1 (edgeEnum H i).2, (mem_filter.1 hi).2⟩
  · intro i _ j _ h; exact edgeEnum_inj H h
  · intro f hf
    rw [SimpleGraph.mem_incidenceFinset] at hf
    have hf' : f ∈ H.edgeFinset := SimpleGraph.mem_edgeFinset.2 hf.1
    refine ⟨(edgeEnum H).symm ⟨f, hf'⟩, mem_filter.2 ⟨mem_univ _, by simpa using hf.2⟩, by simp⟩

theorem line_edges_le :
    (lineGraph H).edgeFinset.card ≤ ∑ v : Fin n, (H.degree v).choose 2 := by
  have hsub : (lineGraph H).edgeFinset ⊆
      univ.biUnion (fun v => (incL H v).offDiag.image Sym2.mk.uncurry) := by
    intro s hs
    induction s using Sym2.ind with
    | h i j =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hs
      obtain ⟨hij, x, hx1, hx2⟩ := hs
      refine mem_biUnion.2 ⟨x, mem_univ _, mem_image.2 ⟨(i, j), ?_, rfl⟩⟩
      simp only [mem_offDiag, incL, mem_filter, mem_univ, true_and]
      exact ⟨hx1, hx2, hij⟩
  calc (lineGraph H).edgeFinset.card
      ≤ (univ.biUnion (fun v => (incL H v).offDiag.image Sym2.mk.uncurry)).card :=
        card_le_card hsub
    _ ≤ ∑ v, ((incL H v).offDiag.image Sym2.mk.uncurry).card := card_biUnion_le
    _ = ∑ v : Fin n, (H.degree v).choose 2 := by
        refine sum_congr rfl fun v _ => ?_
        rw [Sym2.card_image_offDiag, card_incL]

/-- Exact count: two distinct edges of a simple graph share at most one vertex. -/
theorem line_edges :
    (lineGraph H).edgeFinset.card = ∑ v : Fin n, (H.degree v).choose 2 := by
  have heq : (lineGraph H).edgeFinset =
      univ.biUnion (fun v => (incL H v).offDiag.image Sym2.mk.uncurry) := by
    ext s
    induction s using Sym2.ind with
    | h i j =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, mem_biUnion]
      constructor
      · rintro ⟨hij, x, hx1, hx2⟩
        refine ⟨x, mem_univ _, mem_image.2 ⟨(i, j), ?_, rfl⟩⟩
        simp only [mem_offDiag, incL, mem_filter, mem_univ, true_and]
        exact ⟨hx1, hx2, hij⟩
      · rintro ⟨x, -, hx⟩
        obtain ⟨⟨a, b⟩, hab, he⟩ := mem_image.1 hx
        simp only [mem_offDiag, incL, mem_filter, mem_univ, true_and] at hab
        have he' : s(a, b) = s(i, j) := he
        rcases Sym2.eq_iff.1 he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hab.2.2, x, hab.1, hab.2.1⟩
        · exact ⟨fun h => hab.2.2 h.symm, x, hab.2.1, hab.1⟩
  rw [heq, card_biUnion]
  · refine sum_congr rfl fun v _ => ?_
    rw [Sym2.card_image_offDiag, card_incL]
  · intro x _ y _ hxy
    simp only [Function.onFun]
    rw [disjoint_left]
    intro s hsx hsy
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.1 hsx
    obtain ⟨⟨c, d⟩, hcd, he⟩ := mem_image.1 hsy
    simp only [mem_offDiag, incL, mem_filter, mem_univ, true_and] at hab hcd
    have he' : s(c, d) = s(a, b) := he
    have hxa := (Sym2.mem_and_mem_iff hxy).1 ⟨hab.1, ?_⟩
    have hxb := (Sym2.mem_and_mem_iff hxy).1 ⟨hab.2.1, ?_⟩
    · exact hab.2.2 (edgeEnum_inj H (hxa.trans hxb.symm))
    · rcases Sym2.eq_iff.1 he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcd.2.1
      · exact hcd.1
    · rcases Sym2.eq_iff.1 he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcd.1
      · exact hcd.2.1

theorem gmm_calls_le :
    (∑ σ : Equiv.Perm (Fin H.edgeFinset.card), ∑ i, (calls (lineGraph H) σ i : ℝ)) ≤
      (∑ v : Fin n, ((H.degree v).choose 2 : ℝ)) * (Nat.factorial H.edgeFinset.card) := by
  refine (RandomGreedyMIS.total_calls_le _ (lineGraph H)).trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast line_edges_le H

/-! ### Unbiased estimator identity -/

theorem gm_card_eq (σ : Equiv.Perm (Fin H.edgeFinset.card)) :
    ((GM H σ).card : ℝ) = ∑ i, (if inMIS (lineGraph H) σ i = true then (1 : ℝ) else 0) := by
  rw [GM, card_image_of_injective _ (edgeEnum_inj H), sum_boole]

theorem sum_gm_card :
    ∑ σ : Equiv.Perm (Fin H.edgeFinset.card), ((GM H σ).card : ℝ) =
      ∑ σ, ∑ i, (if inMIS (lineGraph H) σ i = true then (1 : ℝ) else 0) :=
  sum_congr rfl fun σ _ => gm_card_eq H σ

end LineGraph
end MTSPGMM

open RandomGreedyMIS in
theorem solution {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    (∑ σ : Equiv.Perm (Fin H.edgeFinset.card), ∑ i, (calls (lineGraph H) σ i : ℝ)) ≤
      (∑ v : Fin n, ((H.degree v).choose 2 : ℝ)) * (Nat.factorial H.edgeFinset.card) :=
  MTSPGMM.gmm_calls_le H
