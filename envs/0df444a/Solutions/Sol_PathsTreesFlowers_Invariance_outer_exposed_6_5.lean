-- Prove2me | solution 1 for PathsTreesFlowers.Invariance.outer_exposed_6_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T10:18:34.816764+00:00
-- url     : https://prove2.me/submissions/29b918af-6a9c-4002-9133-91552a1f4102

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2
import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink
import Definitions.Def_PathsTreesFlowers_Invariance_Config
import Theorems.Thm_PathsTreesFlowers_Invariance_lemma_4_2
import Theorems.Thm_PathsTreesFlowers_Invariance_lemma_4_14_expansion

namespace SolPathsTreesFlowersOuterExposed65

set_option linter.unusedSectionVars false

open EdmondsMatching65.Polyhedron (IsMatching)
open PathsTreesFlowers.Invariance

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### Part 1: Double counting and `IsBlossomSet` properties -/

lemma sum_card_filter_ends (G : EdmondsMatching65.Polyhedron.Graph V E) (S : Finset V) (F : Finset E) :
    ∑ v ∈ S, (F.filter (fun e => v ∈ G.ends e)).card =
      ∑ e ∈ F, (S.filter (fun v => v ∈ G.ends e)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

lemma card_filter_ends_eq_two_of_mem_sym2 {G : EdmondsMatching65.Polyhedron.Graph V E}
    {S : Finset V} {e : E} (he : G.ends e ∈ S.sym2) :
    (S.filter (fun v => v ∈ G.ends e)).card = 2 := by
  rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
  have hne : a ≠ b := by
    rintro rfl
    exact G.loopless e (hab ▸ Sym2.mk_isDiag_iff.mpr rfl)
  rw [hab, Finset.mk_mem_sym2_iff] at he
  have hfilt : S.filter (fun v => v ∈ G.ends e) = {a, b} := by
    ext v
    simp only [Finset.mem_filter, hab, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨by rcases h with rfl | rfl; exacts [he.1, he.2], h⟩⟩
  rw [hfilt, Finset.card_pair hne]

lemma card_filter_matching_le_one {G : EdmondsMatching65.Polyhedron.Graph V E}
    {N : Finset E} (hN : IsMatching G N) (v : V) :
    (N.filter (fun e => v ∈ G.ends e)).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun e₁ he₁ e₂ he₂ => ?_
  simp only [Finset.mem_filter] at he₁ he₂
  by_contra hne
  exact hN e₁ he₁.1 e₂ he₂.1 hne v he₁.2 he₂.2

lemma two_mul_card_filter_sym2_le {G : EdmondsMatching65.Polyhedron.Graph V E}
    {N : Finset E} (hN : IsMatching G N) (S : Finset V) :
    2 * (N.filter (fun e => G.ends e ∈ S.sym2)).card ≤ S.card := by
  set NS := N.filter (fun e => G.ends e ∈ S.sym2)
  have hNS : IsMatching G NS := fun e he f hf =>
    hN e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1
  have hsum_e : ∑ e ∈ NS, (S.filter (fun v => v ∈ G.ends e)).card = 2 * NS.card := by
    calc ∑ e ∈ NS, (S.filter (fun v => v ∈ G.ends e)).card
        = ∑ _e ∈ NS, 2 := Finset.sum_congr rfl fun e he =>
          card_filter_ends_eq_two_of_mem_sym2 (Finset.mem_filter.mp he).2
      _ = 2 * NS.card := by simp [Nat.mul_comm]
  have hsum_v : ∑ v ∈ S, (NS.filter (fun e => v ∈ G.ends e)).card ≤ S.card := by
    calc ∑ v ∈ S, (NS.filter (fun e => v ∈ G.ends e)).card
        ≤ ∑ _v ∈ S, 1 := Finset.sum_le_sum fun v _ => card_filter_matching_le_one hNS v
      _ = S.card := by simp
  linarith [sum_card_filter_ends G S NS]

lemma blossomSet_card_le_two_mul_add_one {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} {U : Finset V} (hU : PathsTreesFlowers.Duality.IsBlossomSet G M U) :
    U.card ≤ 2 * (M.filter (fun e => G.ends e ∈ U.sym2)).card + 1 := by
  induction hU with
  | single v => simp
  | circuit k Uf ef hk _hUf hdisj hef hMf ih =>
    set W := (Finset.range (2 * k + 1)).biUnion Uf
    have hW_card : W.card ≤ ∑ i ∈ Finset.range (2 * k + 1), (Uf i).card := Finset.card_biUnion_le
    have hsum_ih : ∑ i ∈ Finset.range (2 * k + 1), (Uf i).card ≤
        ∑ i ∈ Finset.range (2 * k + 1), (2 * (M.filter (fun e => G.ends e ∈ (Uf i).sym2)).card + 1) :=
      Finset.sum_le_sum fun i hi => ih i (Finset.mem_range.mp hi)
    have hsum_rw : ∑ i ∈ Finset.range (2 * k + 1), (2 * (M.filter (fun e => G.ends e ∈ (Uf i).sym2)).card + 1) =
        (∑ i ∈ Finset.range (2 * k + 1), (M.filter (fun e => G.ends e ∈ (Uf i).sym2)).card) +
          (∑ i ∈ Finset.range (2 * k + 1), (M.filter (fun e => G.ends e ∈ (Uf i).sym2)).card) + (2 * k + 1) := by
      simp_rw [Nat.two_mul, Finset.sum_add_distrib]
      simp
    set A := (Finset.range (2 * k + 1)).biUnion (fun i => M.filter (fun e => G.ends e ∈ (Uf i).sym2))
    set B := (Finset.range k).image (fun j => ef (2 * j + 1))
    have hA_card : A.card = ∑ i ∈ Finset.range (2 * k + 1), (M.filter (fun e => G.ends e ∈ (Uf i).sym2)).card := by
      refine Finset.card_biUnion fun i hi j hj hij => ?_
      rw [Function.onFun, Finset.disjoint_left]
      intro e hei hej
      rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
      have hai : a ∈ Uf i := by
        have := (Finset.mem_filter.mp hei).2
        rw [hab, Finset.mk_mem_sym2_iff] at this
        exact this.1
      have haj : a ∈ Uf j := by
        have := (Finset.mem_filter.mp hej).2
        rw [hab, Finset.mk_mem_sym2_iff] at this
        exact this.1
      exact Finset.disjoint_left.mp (hdisj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij) hai haj
    have hB_card : B.card = k := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro j₁ hj₁ j₂ hj₂ heq
      have hj₁_lt : j₁ < k := Finset.mem_range.mp hj₁
      have hj₂_lt : j₂ < k := Finset.mem_range.mp hj₂
      by_contra hne
      obtain ⟨a₁, ha₁, b₁, hb₁, hends₁⟩ := hef (2 * j₁ + 1) (by omega)
      obtain ⟨a₂, ha₂, b₂, hb₂, hends₂⟩ := hef (2 * j₂ + 1) (by omega)
      have h_eq_ends : s(a₁, b₁) = s(a₂, b₂) := hends₁.symm.trans ((congrArg G.ends heq).trans hends₂)
      have ha₁_mem : a₁ ∈ (s(a₂, b₂) : Sym2 V) := h_eq_ends ▸ Sym2.mem_mk_left a₁ b₁
      rw [Sym2.mem_iff] at ha₁_mem
      rcases ha₁_mem with rfl | rfl
      · exact Finset.disjoint_left.mp
          (hdisj (2 * j₁ + 1) (by omega) (2 * j₂ + 1) (by omega) (by omega)) ha₁ ha₂
      · have hne_idx : 2 * j₁ + 1 ≠ (2 * j₂ + 1 + 1) % (2 * k + 1) := by
          by_cases hlt : 2 * j₂ + 2 < 2 * k + 1
          · rw [show 2 * j₂ + 1 + 1 = 2 * j₂ + 2 by omega, Nat.mod_eq_of_lt hlt]; omega
          · have heq_k : 2 * j₂ + 1 + 1 = 2 * k + 1 := by omega
            rw [heq_k, Nat.mod_self]; omega
        exact Finset.disjoint_left.mp
          (hdisj (2 * j₁ + 1) (by omega) ((2 * j₂ + 1 + 1) % (2 * k + 1)) (Nat.mod_lt _ (by omega)) hne_idx)
          ha₁ hb₂
    have hAB_disj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro e heA heB
      rcases Finset.mem_biUnion.mp heA with ⟨i, hi, hei⟩
      rcases Finset.mem_image.mp heB with ⟨j, hj, rfl⟩
      have hi_lt : i < 2 * k + 1 := Finset.mem_range.mp hi
      have hj_lt : j < k := Finset.mem_range.mp hj
      obtain ⟨a, ha, b, hb, hends⟩ := hef (2 * j + 1) (by omega)
      have he_Ui := (Finset.mem_filter.mp hei).2
      rw [hends, Finset.mk_mem_sym2_iff] at he_Ui
      have hi_eq₁ : i = 2 * j + 1 := by
        by_contra hne
        exact Finset.disjoint_left.mp (hdisj i hi_lt (2 * j + 1) (by omega) hne) he_Ui.1 ha
      have hi_eq₂ : i = (2 * j + 1 + 1) % (2 * k + 1) := by
        by_contra hne
        exact Finset.disjoint_left.mp
          (hdisj i hi_lt ((2 * j + 1 + 1) % (2 * k + 1)) (Nat.mod_lt _ (by omega)) hne) he_Ui.2 hb
      by_cases hlt : 2 * j + 2 < 2 * k + 1
      · rw [show 2 * j + 1 + 1 = 2 * j + 2 by omega, Nat.mod_eq_of_lt hlt] at hi_eq₂
        omega
      · have heq_k : 2 * j + 1 + 1 = 2 * k + 1 := by omega
        rw [heq_k, Nat.mod_self] at hi_eq₂
        omega
    have hAB_sub : A ∪ B ⊆ M.filter (fun e => G.ends e ∈ W.sym2) := by
      intro e he
      rcases Finset.mem_union.mp he with heA | heB
      · rcases Finset.mem_biUnion.mp heA with ⟨i, hi, hei⟩
        have hei' := Finset.mem_filter.mp hei
        refine Finset.mem_filter.mpr ⟨hei'.1, ?_⟩
        rw [Finset.mem_sym2_iff] at hei' ⊢
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨i, hi, hei'.2 x hx⟩
      · rcases Finset.mem_image.mp heB with ⟨j, hj, rfl⟩
        have hj_lt : j < k := Finset.mem_range.mp hj
        have heM : ef (2 * j + 1) ∈ M := (hMf (2 * j + 1) (by omega)).mpr ⟨j, rfl⟩
        obtain ⟨a, ha, b, hb, hends⟩ := hef (2 * j + 1) (by omega)
        refine Finset.mem_filter.mpr ⟨heM, ?_⟩
        rw [hends, Finset.mk_mem_sym2_iff]
        exact ⟨Finset.mem_biUnion.mpr ⟨2 * j + 1, Finset.mem_range.mpr (by omega), ha⟩,
          Finset.mem_biUnion.mpr ⟨(2 * j + 1 + 1) % (2 * k + 1),
            Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), hb⟩⟩
    have hcard_le : A.card + B.card ≤ (M.filter (fun e => G.ends e ∈ W.sym2)).card := by
      rw [← Finset.card_union_of_disjoint hAB_disj]
      exact Finset.card_le_card hAB_sub
    omega

lemma blossomSet_odd {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} {U : Finset V} (hU : PathsTreesFlowers.Duality.IsBlossomSet G M U) :
    Odd U.card := by
  induction hU with
  | single v => exact ⟨0, by simp⟩
  | circuit k Uf _ef _hk _hUf hdisj _hef _hMf ih =>
    have hcard : ((Finset.range (2 * k + 1)).biUnion Uf).card =
        ∑ i ∈ Finset.range (2 * k + 1), (Uf i).card := by
      refine Finset.card_biUnion fun i hi j hj hij => ?_
      exact hdisj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij
    have h_eq : ∀ i ∈ Finset.range (2 * k + 1), (Uf i).card = 2 * ((Uf i).card / 2) + 1 := by
      intro i hi
      rcases ih i (Finset.mem_range.mp hi) with ⟨r, hr⟩
      omega
    rw [hcard, Finset.sum_congr rfl h_eq]
    have hsum_rw : ∑ i ∈ Finset.range (2 * k + 1), (2 * ((Uf i).card / 2) + 1) =
        (∑ i ∈ Finset.range (2 * k + 1), (Uf i).card / 2) +
          (∑ i ∈ Finset.range (2 * k + 1), (Uf i).card / 2) + (2 * k + 1) := by
      simp_rw [Nat.two_mul, Finset.sum_add_distrib]
      simp
    rw [hsum_rw]
    exact ⟨(∑ i ∈ Finset.range (2 * k + 1), (Uf i).card / 2) + k, by omega⟩

lemma blossomSet_card_eq_two_mul_add_one {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) {U : Finset V}
    (hU : PathsTreesFlowers.Duality.IsBlossomSet G M U) :
    U.card = 2 * (M.filter (fun e => G.ends e ∈ U.sym2)).card + 1 := by
  have h1 := two_mul_card_filter_sym2_le hM U
  have h2 := blossomSet_card_le_two_mul_add_one hU
  rcases blossomSet_odd hU with ⟨r, hr⟩
  omega

lemma exposedIn_card_eq_one_of_blossomSet {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) {U : Finset V}
    (hU : PathsTreesFlowers.Duality.IsBlossomSet G M U) :
    (PathsTreesFlowers.Duality.exposedIn G U M).card = 1 := by
  set MS := M.filter (fun e => G.ends e ∈ U.sym2)
  have hMS : IsMatching G MS := fun e he f hf =>
    hM e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1
  have hU_card : U.card = 2 * MS.card + 1 := blossomSet_card_eq_two_mul_add_one hM hU
  have hsum_e : ∑ e ∈ MS, (U.filter (fun v => v ∈ G.ends e)).card = 2 * MS.card := by
    calc ∑ e ∈ MS, (U.filter (fun v => v ∈ G.ends e)).card
        = ∑ _e ∈ MS, 2 := Finset.sum_congr rfl fun e he =>
          card_filter_ends_eq_two_of_mem_sym2 (Finset.mem_filter.mp he).2
      _ = 2 * MS.card := by simp [Nat.mul_comm]
  have h_deg : ∀ v ∈ U, (MS.filter (fun e => v ∈ G.ends e)).card =
      if v ∉ PathsTreesFlowers.Duality.exposedIn G U M then 1 else 0 := by
    intro v hvU
    by_cases hv : v ∈ PathsTreesFlowers.Duality.exposedIn G U M
    · rw [if_neg (not_not.mpr hv), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he
      rcases Finset.mem_filter.mp he with ⟨heM, heU⟩
      exact (Finset.mem_filter.mp hv).2 e heM heU
    · rw [if_pos hv]
      have hle := card_filter_matching_le_one hMS v
      have hpos : 0 < (MS.filter (fun e => v ∈ G.ends e)).card := by
        rw [Finset.card_pos]
        simp only [PathsTreesFlowers.Duality.exposedIn, Finset.mem_filter, hvU, true_and,
          not_forall, not_not] at hv
        rcases hv with ⟨e, heM, heU, hve⟩
        exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heM, heU⟩, hve⟩⟩
      omega
  have hsum_v : ∑ v ∈ U, (MS.filter (fun e => v ∈ G.ends e)).card =
      (U.filter (fun v => v ∉ PathsTreesFlowers.Duality.exposedIn G U M)).card := by
    rw [Finset.sum_congr rfl h_deg, ← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  have hexp_filt : U.filter (fun v => v ∈ PathsTreesFlowers.Duality.exposedIn G U M) =
      PathsTreesFlowers.Duality.exposedIn G U M := by
    ext v; simp [PathsTreesFlowers.Duality.exposedIn]
  have hcard_split := Finset.card_filter_add_card_filter_not (s := U)
    (p := fun v => v ∈ PathsTreesFlowers.Duality.exposedIn G U M)
  rw [hexp_filt] at hcard_split
  have hcomm := sum_card_filter_ends G U MS
  omega

lemma card_eq_two_mul_add_one_of_unique_exposed {G : EdmondsMatching65.Polyhedron.Graph V E}
    {U : Finset V} {MP : Finset E} (hMP_sub : MP ⊆ (induced G U).edges)
    (hMP : IsMatching G MP) {u : V} (hu : u ∈ U)
    (hexp : ∀ w ∈ U, (PathsTreesFlowers.Duality.IsExposed G MP w ↔ w = u)) :
    U.card = 2 * MP.card + 1 := by
  have hsum_e : ∑ e ∈ MP, (U.filter (fun v => v ∈ G.ends e)).card = 2 * MP.card := by
    calc ∑ e ∈ MP, (U.filter (fun v => v ∈ G.ends e)).card
        = ∑ _e ∈ MP, 2 := Finset.sum_congr rfl fun e he =>
          card_filter_ends_eq_two_of_mem_sym2 (Finset.mem_filter.mp (hMP_sub he)).2
      _ = 2 * MP.card := by simp [Nat.mul_comm]
  have h_deg : ∀ w ∈ U, (MP.filter (fun e => w ∈ G.ends e)).card =
      if w ≠ u then 1 else 0 := by
    intro w hwU
    by_cases hwu : w = u
    · rw [if_neg (not_not.mpr hwu), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he
      exact (hexp w hwU).mpr hwu e he
    · rw [if_pos hwu]
      have hle := card_filter_matching_le_one hMP w
      have hnot : ¬ PathsTreesFlowers.Duality.IsExposed G MP w :=
        fun h => hwu ((hexp w hwU).mp h)
      simp only [PathsTreesFlowers.Duality.IsExposed, not_forall, not_not] at hnot
      rcases hnot with ⟨e, he, hwe⟩
      have hpos : 0 < (MP.filter (fun e => w ∈ G.ends e)).card :=
        Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hwe⟩⟩
      omega
  have hsum_v : ∑ w ∈ U, (MP.filter (fun e => w ∈ G.ends e)).card =
      (U.filter (fun w => w ≠ u)).card := by
    rw [Finset.sum_congr rfl h_deg, ← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  have hu_filt : U.filter (fun w => w = u) = {u} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hu, h⟩⟩
  have hcard_split := Finset.card_filter_add_card_filter_not (s := U) (p := fun w => w = u)
  rw [hu_filt, Finset.card_singleton] at hcard_split
  change 1 + (U.filter (fun w => w ≠ u)).card = U.card at hcard_split
  have hcomm := sum_card_filter_ends G U MP
  omega

lemma isOddCircuitSet_of_isBlossomSet {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} {U : Finset V} (hU : PathsTreesFlowers.Duality.IsBlossomSet G M U) :
    IsOddCircuitSet G U := by
  induction hU with
  | single x => exact IsOddCircuitSet.singleton x
  | circuit k Uf ef hk _hUf hdisj hef _hMf ih =>
    have hbi : (Finset.range (2 * k + 1)).biUnion Uf =
        (Finset.univ : Finset (Fin (2 * k + 1))).biUnion (fun i => Uf i.1) := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_univ, true_and]
      exact ⟨fun ⟨i, hi, hx⟩ => ⟨⟨i, hi⟩, hx⟩, fun ⟨i, hx⟩ => ⟨i.1, i.2, hx⟩⟩
    rw [hbi]
    refine IsOddCircuitSet.circuit k hk (fun i => Uf i.1) (fun i => ef i.1)
      (fun i => ih i.1 i.2)
      (fun i j hij => hdisj i.1 i.2 j.1 j.2 (Fin.val_ne_of_ne hij))
      (fun i => ?_)
    have h_add : ((i + 1 : Fin (2 * k + 1)).1) = (i.1 + 1) % (2 * k + 1) := by
      rw [Fin.val_add]
      have h1 : (1 : Fin (2 * k + 1)).1 = 1 := by
        change 1 % (2 * k + 1) = 1
        exact Nat.mod_eq_of_lt (by omega)
      rw [h1]
    rw [h_add]
    exact hef i.1 i.2

/-! ### Part 2: Splitting a single part of a `Finpartition` -/

def splitSetoid (P : Finpartition (Finset.univ : Finset V)) (U : Finset V) : Setoid V where
  r x y := x = y ∨ (P.part x = P.part y ∧ P.part x ≠ U)
  iseqv := ⟨fun _ => Or.inl rfl,
    fun h => by rcases h with rfl | ⟨h1, h2⟩; exacts [Or.inl rfl, Or.inr ⟨h1.symm, h1 ▸ h2⟩],
    fun h1 h2 => by
      rcases h1 with rfl | ⟨h1a, h1b⟩
      · exact h2
      · rcases h2 with rfl | ⟨h2a, _⟩
        · exact Or.inr ⟨h1a, h1b⟩
        · exact Or.inr ⟨h1a.trans h2a, h1b⟩⟩

instance (P : Finpartition (Finset.univ : Finset V)) (U : Finset V) :
    DecidableRel (splitSetoid P U).r := fun x y =>
  show Decidable (x = y ∨ (P.part x = P.part y ∧ P.part x ≠ U)) from inferInstance

def splitPart (P : Finpartition (Finset.univ : Finset V)) (U : Finset V) :
    Finpartition (Finset.univ : Finset V) :=
  Finpartition.ofSetoid (splitSetoid P U)

lemma splitPart_part_of_mem (P : Finpartition (Finset.univ : Finset V)) {U : Finset V}
    (hU : U ∈ P.parts) {x : V} (hx : x ∈ U) :
    (splitPart P U).part x = {x} := by
  have hx_part : P.part x = U :=
    P.eq_of_mem_parts (P.part_mem.2 (Finset.mem_univ x)) hU (P.mem_part (Finset.mem_univ x)) hx
  ext y
  rw [splitPart, Finpartition.mem_part_ofSetoid_iff_rel]
  change (x = y ∨ (P.part x = P.part y ∧ P.part x ≠ U)) ↔ y ∈ ({x} : Finset V)
  simp [hx_part, eq_comm]

lemma splitPart_part_of_not_mem (P : Finpartition (Finset.univ : Finset V)) {U : Finset V}
    {x : V} (hx : x ∉ U) :
    (splitPart P U).part x = P.part x := by
  have hx_ne : P.part x ≠ U := fun h => hx (h ▸ P.mem_part (Finset.mem_univ x))
  ext y
  rw [splitPart, Finpartition.mem_part_ofSetoid_iff_rel]
  change (x = y ∨ (P.part x = P.part y ∧ P.part x ≠ U)) ↔ y ∈ P.part x
  constructor
  · rintro (rfl | ⟨h1, _⟩)
    · exact P.mem_part (Finset.mem_univ x)
    · rw [h1]; exact P.mem_part (Finset.mem_univ y)
  · intro hy
    refine Or.inr ⟨?_, hx_ne⟩
    exact P.eq_of_mem_parts (P.part_mem.2 (Finset.mem_univ x))
      (P.part_mem.2 (Finset.mem_univ y)) hy (P.mem_part (Finset.mem_univ y))

lemma splitPart_parts (P : Finpartition (Finset.univ : Finset V)) {U : Finset V}
    (hU : U ∈ P.parts) :
    (splitPart P U).parts = P.parts.erase U ∪ U.image (fun u => ({u} : Finset V)) := by
  ext W
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_image]
  constructor
  · intro hW
    obtain ⟨x, hxW⟩ := (splitPart P U).nonempty_of_mem_parts hW
    have hpart_x : (splitPart P U).part x = W :=
      (splitPart P U).eq_of_mem_parts ((splitPart P U).part_mem.2 (Finset.mem_univ x)) hW
        ((splitPart P U).mem_part (Finset.mem_univ x)) hxW
    by_cases hxU : x ∈ U
    · refine Or.inr ⟨x, hxU, ?_⟩
      rw [← hpart_x, splitPart_part_of_mem P hU hxU]
    · refine Or.inl ⟨?_, ?_⟩
      · rw [← hpart_x, splitPart_part_of_not_mem P hxU]
        exact fun h => hxU (h ▸ P.mem_part (Finset.mem_univ x))
      · rw [← hpart_x, splitPart_part_of_not_mem P hxU]
        exact P.part_mem.2 (Finset.mem_univ x)
  · rintro (⟨hWU, hWP⟩ | ⟨u, huU, rfl⟩)
    · obtain ⟨x, hxW⟩ := P.nonempty_of_mem_parts hWP
      have hpart_x : P.part x = W :=
        P.eq_of_mem_parts (P.part_mem.2 (Finset.mem_univ x)) hWP
          (P.mem_part (Finset.mem_univ x)) hxW
      have hxU : x ∉ U := fun hxU => hWU (hpart_x.symm.trans
        (P.eq_of_mem_parts (P.part_mem.2 (Finset.mem_univ x)) hU
          (P.mem_part (Finset.mem_univ x)) hxU))
      rw [← hpart_x, ← splitPart_part_of_not_mem P hxU]
      exact (splitPart P U).part_mem.2 (Finset.mem_univ x)
    · rw [← splitPart_part_of_mem P hU huU]
      exact (splitPart P U).part_mem.2 (Finset.mem_univ u)

/-! ### Part 3: Shrunken matching and tree rerouting in `Config60 G M` -/

lemma partOf_eq_iff (P : Finpartition (Finset.univ : Finset V)) (v : V)
    (p : {U : Finset V // U ∈ P.parts}) :
    partOf P v = p ↔ v ∈ p.1 := by
  constructor
  · intro h
    rw [← congrArg Subtype.val h]
    exact P.mem_part (Finset.mem_univ v)
  · intro hv
    exact Subtype.ext (P.eq_of_mem_parts (P.part_mem.2 (Finset.mem_univ v)) p.2
      (P.mem_part (Finset.mem_univ v)) hv)

lemma not_mem_sym2_of_shrinkE {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} (e : ShrinkE G P)
    (p : {U : Finset V // U ∈ P.parts}) : G.ends e.1 ∉ p.1.sym2 := by
  intro h
  apply e.2
  rcases Sym2.exists.mp ⟨G.ends e.1, rfl⟩ with ⟨a, b, hab⟩
  rw [hab, Finset.mk_mem_sym2_iff] at h
  rw [hab, Sym2.map_mk, Sym2.mk_isDiag_iff]
  exact ((partOf_eq_iff P a p).mpr h.1).trans ((partOf_eq_iff P b p).mpr h.2).symm

lemma isDiag_map_partOf_iff {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} (e : E) :
    ((G.ends e).map (partOf P)).IsDiag ↔ ∃ U ∈ P.parts, G.ends e ∈ U.sym2 := by
  rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
  rw [hab, Sym2.map_mk, Sym2.mk_isDiag_iff]
  constructor
  · intro h
    refine ⟨P.part a, P.part_mem.2 (Finset.mem_univ a), ?_⟩
    have hba : P.part a = P.part b := congrArg Subtype.val h
    rw [Finset.mk_mem_sym2_iff, hba]
    exact ⟨ hba ▸ P.mem_part (Finset.mem_univ a), P.mem_part (Finset.mem_univ b)⟩
  · rintro ⟨U, hU, heU⟩
    rw [Finset.mk_mem_sym2_iff] at heU
    exact ((partOf_eq_iff P a ⟨U, hU⟩).mpr heU.1).trans
      ((partOf_eq_iff P b ⟨U, hU⟩).mpr heU.2).symm

lemma exists_mem_part_and_ends_of_mem_shrink_ends {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {e : ShrinkE G P}
    {p : {U : Finset V // U ∈ P.parts}} (hp : p ∈ (shrink G P).ends e) :
    ∃ v ∈ p.1, v ∈ G.ends e.1 := by
  change p ∈ (G.ends e.1).map (partOf P) at hp
  rcases Sym2.mem_map.mp hp with ⟨v, hve, hvp⟩
  exact ⟨v, (partOf_eq_iff P v p).mp hvp, hve⟩

lemma mem_exposedIn_of_mem_M_of_not_mem_sym2 {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) {U : Finset V} {e : E} (heM : e ∈ M)
    (hnot : G.ends e ∉ U.sym2) {v : V} (hvU : v ∈ U) (hve : v ∈ G.ends e) :
    v ∈ PathsTreesFlowers.Duality.exposedIn G U M := by
  refine Finset.mem_filter.mpr ⟨hvU, fun f hfM hfU hvf => ?_⟩
  have hef : e ≠ f := fun h => hnot (h ▸ hfU)
  exact hM e heM f hfM hef v hve hvf

lemma isMatching_shrinkMatching {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : Config60 G M) :
    IsMatching (shrink G C.P) (shrinkMatching G C.P M) := by
  intro e₁ he₁ e₂ he₂ hne p hp₁ hp₂
  have he₁M : e₁.1 ∈ M := Finset.mem_subtype.mp he₁
  have he₂M : e₂.1 ∈ M := Finset.mem_subtype.mp he₂
  obtain ⟨v₁, hv₁p, hv₁e⟩ := exists_mem_part_and_ends_of_mem_shrink_ends hp₁
  obtain ⟨v₂, hv₂p, hv₂e⟩ := exists_mem_part_and_ends_of_mem_shrink_ends hp₂
  have hv₁_exp := mem_exposedIn_of_mem_M_of_not_mem_sym2 C.hM.1 he₁M
    (not_mem_sym2_of_shrinkE e₁ p) hv₁p hv₁e
  have hv₂_exp := mem_exposedIn_of_mem_M_of_not_mem_sym2 C.hM.1 he₂M
    (not_mem_sym2_of_shrinkE e₂ p) hv₂p hv₂e
  have hcard1 := exposedIn_card_eq_one_of_blossomSet C.hM.1 (C.blossom p.1 p.2)
  have hv_eq : v₁ = v₂ := Finset.card_le_one.mp (by omega) v₁ hv₁_exp v₂ hv₂_exp
  subst hv_eq
  exact C.hM.1 e₁.1 he₁M e₂.1 he₂M (Subtype.coe_ne_coe.mpr hne) v₁ hv₁e hv₂e

lemma exists_rerouted_shrink_matching {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : Config60 G M) {i : Fin C.n}
    {p₀ : {U : Finset V // U ∈ C.P.parts}} (hp₀ : p₀ ∈ (C.J i).outer) :
    ∃ M₂ : Finset (ShrinkE G C.P),
      IsMatching (shrink G C.P) M₂ ∧
      M₂.card = (shrinkMatching G C.P M).card ∧
      ∀ e ∈ M₂, p₀ ∉ (shrink G C.P).ends e := by
  set G' := shrink G C.P
  set M' := shrinkMatching G C.P M
  have hM'_match : IsMatching G' M' := isMatching_shrinkMatching C
  obtain ⟨r, hpl⟩ := C.planted i
  obtain ⟨r₀, _hr₀, hiff_r⟩ := (lemma_4_2 G' (C.J i)).2.2 (M' ∩ (C.J i).edges) hpl.max_in
  have hr_eq : r = r₀ := (hiff_r r hpl.root_mem).mp hpl.root_exposed_in
  have h_no_sdiff_verts : ∀ e ∈ M' \ (C.J i).edges, ∀ w ∈ G'.ends e, w ∉ (C.J i).verts := by
    intro e he w hwe hw_verts
    rcases Finset.mem_sdiff.mp he with ⟨heM', he_not_J⟩
    by_cases hwr : w = r
    · subst hwr
      exact hpl.root_exposed e heM' hwe
    · have hnot_exp : ¬ PathsTreesFlowers.Duality.IsExposed G' (M' ∩ (C.J i).edges) w :=
        fun hexp => hwr (hr_eq.symm ▸ (hiff_r w hw_verts).mp hexp)
      simp only [PathsTreesFlowers.Duality.IsExposed, not_forall, not_not] at hnot_exp
      rcases hnot_exp with ⟨f, hf, hwf⟩
      have hef : e ≠ f := fun h => he_not_J (h ▸ (Finset.mem_inter.mp hf).2)
      exact hM'_match e heM' f (Finset.mem_inter.mp hf).1 hef w hwe hwf
  obtain ⟨NJ, ⟨hNJ_max, hNJ_exp⟩, _⟩ := (lemma_4_2 G' (C.J i)).2.1 p₀ hp₀
  have hNJ_sub : NJ ⊆ (C.J i).edges := hNJ_max.1
  have hNJ_card : NJ.card = (M' ∩ (C.J i).edges).card :=
    le_antisymm (hpl.max_in.2.2 NJ hNJ_max.1 hNJ_max.2.1)
      (hNJ_max.2.2 (M' ∩ (C.J i).edges) Finset.inter_subset_right hpl.max_in.2.1)
  set M₂ := (M' \ (C.J i).edges) ∪ NJ
  have hdisj : Disjoint (M' \ (C.J i).edges) NJ :=
    Disjoint.mono_right hNJ_sub Finset.sdiff_disjoint
  have hM₂_match : IsMatching G' M₂ := by
    intro e₁ he₁ e₂ he₂ hne w hw₁ hw₂
    rcases Finset.mem_union.mp he₁ with he₁_sdiff | he₁_NJ <;>
      rcases Finset.mem_union.mp he₂ with he₂_sdiff | he₂_NJ
    · exact hM'_match e₁ (Finset.mem_sdiff.mp he₁_sdiff).1 e₂
        (Finset.mem_sdiff.mp he₂_sdiff).1 hne w hw₁ hw₂
    · exact h_no_sdiff_verts e₁ he₁_sdiff w hw₁
        ((C.J i).toSub.ends_mem e₂ (hNJ_sub he₂_NJ) w hw₂)
    · exact h_no_sdiff_verts e₂ he₂_sdiff w hw₂
        ((C.J i).toSub.ends_mem e₁ (hNJ_sub he₁_NJ) w hw₁)
    · exact hNJ_max.2.1 e₁ he₁_NJ e₂ he₂_NJ hne w hw₁ hw₂
  have hM₂_card : M₂.card = M'.card := by
    rw [Finset.card_union_of_disjoint hdisj, hNJ_card, Finset.card_sdiff_add_card_inter]
  have hp₀_verts : p₀ ∈ (C.J i).verts := by
    rw [(C.J i).verts_eq]; exact Finset.mem_union_right _ hp₀
  have hp₀_exp : ∀ e ∈ M₂, p₀ ∉ G'.ends e := by
    intro e he hpe
    rcases Finset.mem_union.mp he with he_sdiff | he_NJ
    · exact h_no_sdiff_verts e he_sdiff p₀ hpe hp₀_verts
    · exact (hNJ_exp p₀ hp₀_verts).mpr rfl e he_NJ hpe
  exact ⟨M₂, hM₂_match, hM₂_card, hp₀_exp⟩

/-! ### Part 4: Main proof of `outer_exposed_6_5` -/

theorem outer_exposed_6_5 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (C : Config60 G M) :
    ∀ v ∈ outerSet C, ∃ M' : Finset E,
      PathsTreesFlowers.Duality.IsMaxMatching G M' ∧
      PathsTreesFlowers.Duality.IsExposed G M' v := by
  intro v hv_out
  have hex_i : ∃ i : Fin C.n, partOf C.P v ∈ (C.J i).outer := by
    rcases hv_out with ⟨_, i, hi⟩ | hcard
    · exact ⟨i, hi⟩
    · exact C.pseudo_outer (C.P.part v) (C.P.part_mem.2 (Finset.mem_univ v)) hcard
  rcases hex_i with ⟨i, hi_out⟩
  set p₀ := partOf C.P v
  set U₀ := C.P.part v
  have hU₀ : U₀ ∈ C.P.parts := C.P.part_mem.2 (Finset.mem_univ v)
  have hvU₀ : v ∈ U₀ := C.P.mem_part (Finset.mem_univ v)
  obtain ⟨M₂, hM₂_match, hM₂_card, hp₀_exp⟩ := exists_rerouted_shrink_matching C hi_out
  have hex_MP : ∀ U : Finset V, U ∈ C.P.parts →
      ∃ MP : Finset E, MP ⊆ (induced G U).edges ∧ IsMatching G MP ∧
        (∃ u ∈ U, ∀ w ∈ U, (PathsTreesFlowers.Duality.IsExposed G MP w ↔ w = u)) ∧
        (U = U₀ → PathsTreesFlowers.Duality.IsExposed G MP v) ∧
        ∃ M₁ : Finset (ShrinkE G (splitPart C.P U)),
          IsMatching (shrink G (splitPart C.P U)) M₁ ∧
          M₁.map (Function.Embedding.subtype _) =
            MP ∪ M₂.map (Function.Embedding.subtype _) := by
    intro U hU
    by_cases hUU₀ : U = U₀
    · subst hUU₀
      have h_no_edge : ∀ e ∈ M₂, (⟨U₀, hU⟩ : {W // W ∈ C.P.parts}) ∉ (shrink G C.P).ends e :=
        hp₀_exp
      obtain ⟨MP, hMP_sub, hMP_match, hMP_exp, M₁, hM₁_match, hM₁_map⟩ :=
        (lemma_4_14_expansion G (splitPart C.P U₀) C.P U₀ hU
          (isOddCircuitSet_of_isBlossomSet (C.blossom U₀ hU))
          (splitPart_parts C.P hU) M₂ hM₂_match).2 h_no_edge v hvU₀
      exact ⟨MP, hMP_sub, hMP_match, ⟨v, hvU₀, hMP_exp⟩,
        fun _ => (hMP_exp v hvU₀).mpr rfl, M₁, hM₁_match, hM₁_map⟩
    · obtain ⟨MP, hMP_sub, hMP_match, hMP_exp, M₁, hM₁_match, hM₁_map⟩ :=
        (lemma_4_14_expansion G (splitPart C.P U) C.P U hU
          (isOddCircuitSet_of_isBlossomSet (C.blossom U hU))
          (splitPart_parts C.P hU) M₂ hM₂_match).1
      exact ⟨MP, hMP_sub, hMP_match, hMP_exp, fun h => False.elim (hUU₀ h),
        M₁, hM₁_match, hM₁_map⟩
  choose MP_fn hMP_fn using hex_MP
  let MP : Finset V → Finset E := fun U =>
    if hU : U ∈ C.P.parts then MP_fn U hU else ∅
  have hMP_props : ∀ U (hU : U ∈ C.P.parts),
      MP U ⊆ (induced G U).edges ∧ IsMatching G (MP U) ∧
      (∃ u ∈ U, ∀ w ∈ U, (PathsTreesFlowers.Duality.IsExposed G (MP U) w ↔ w = u)) ∧
      (U = U₀ → PathsTreesFlowers.Duality.IsExposed G (MP U) v) ∧
      ∃ M₁ : Finset (ShrinkE G (splitPart C.P U)),
        IsMatching (shrink G (splitPart C.P U)) M₁ ∧
        M₁.map (Function.Embedding.subtype _) =
          MP U ∪ M₂.map (Function.Embedding.subtype _) := by
    intro U hU
    dsimp [MP]
    rw [dif_pos hU]
    exact hMP_fn U hU
  set M' := C.P.parts.biUnion MP ∪ M₂.map (Function.Embedding.subtype _)
  have h_mem_local : ∀ e ∈ M', ∀ x ∈ G.ends e,
      e ∈ MP (C.P.part x) ∪ M₂.map (Function.Embedding.subtype _) := by
    intro e he x hxe
    rcases Finset.mem_union.mp he with he_bi | he_M₂
    · rcases Finset.mem_biUnion.mp he_bi with ⟨W, hW, heW⟩
      have hW_sub := (hMP_props W hW).1 heW
      have hxW : x ∈ W := (induced G W).ends_mem e hW_sub x hxe
      have hWx : W = C.P.part x :=
        C.P.eq_of_mem_parts hW (C.P.part_mem.2 (Finset.mem_univ x)) hxW
          (C.P.mem_part (Finset.mem_univ x))
      exact Finset.mem_union_left _ (hWx ▸ heW)
    · exact Finset.mem_union_right _ he_M₂
  have hM'_match : IsMatching G M' := by
    intro e₁ he₁ e₂ he₂ hne x hx₁ hx₂
    have hxU : C.P.part x ∈ C.P.parts := C.P.part_mem.2 (Finset.mem_univ x)
    obtain ⟨_, _, _, _, M₁, hM₁_match, hM₁_map⟩ := hMP_props (C.P.part x) hxU
    have he₁_M₁ : e₁ ∈ M₁.map (Function.Embedding.subtype _) :=
      hM₁_map.symm ▸ h_mem_local e₁ he₁ x hx₁
    have he₂_M₁ : e₂ ∈ M₁.map (Function.Embedding.subtype _) :=
      hM₁_map.symm ▸ h_mem_local e₂ he₂ x hx₂
    rcases Finset.mem_map.mp he₁_M₁ with ⟨f₁, hf₁, rfl⟩
    rcases Finset.mem_map.mp he₂_M₁ with ⟨f₂, hf₂, rfl⟩
    have hf_ne : f₁ ≠ f₂ := fun h => hne (congrArg Subtype.val h)
    have hpx₁ : partOf (splitPart C.P (C.P.part x)) x ∈
        (shrink G (splitPart C.P (C.P.part x))).ends f₁ :=
      Sym2.mem_map.mpr ⟨x, hx₁, rfl⟩
    have hpx₂ : partOf (splitPart C.P (C.P.part x)) x ∈
        (shrink G (splitPart C.P (C.P.part x))).ends f₂ :=
      Sym2.mem_map.mpr ⟨x, hx₂, rfl⟩
    exact hM₁_match f₁ hf₁ f₂ hf₂ hf_ne (partOf (splitPart C.P (C.P.part x)) x) hpx₁ hpx₂
  have hM'_exp : PathsTreesFlowers.Duality.IsExposed G M' v := by
    intro e he hve
    rcases Finset.mem_union.mp (h_mem_local e he v hve) with he_MP | he_M₂
    · exact (hMP_props U₀ hU₀).2.2.2.1 rfl e he_MP hve
    · rcases Finset.mem_map.mp he_M₂ with ⟨f, hf, rfl⟩
      exact hp₀_exp f hf (Sym2.mem_map.mpr ⟨v, hve, rfl⟩)
  have hMP_card_eq : ∀ U ∈ C.P.parts,
      (MP U).card = (M.filter (fun e => G.ends e ∈ U.sym2)).card := by
    intro U hU
    obtain ⟨hMP_sub, hMP_m, ⟨u, huU, hMP_exp_u⟩, _, _⟩ := hMP_props U hU
    have h1 := card_eq_two_mul_add_one_of_unique_exposed hMP_sub hMP_m huU hMP_exp_u
    have h2 := blossomSet_card_eq_two_mul_add_one C.hM.1 (C.blossom U hU)
    omega
  have hbi_MP_card : (C.P.parts.biUnion MP).card = ∑ U ∈ C.P.parts, (MP U).card := by
    refine Finset.card_biUnion fun U₁ hU₁ U₂ hU₂ hne => ?_
    rw [Function.onFun, Finset.disjoint_left]
    intro e he₁ he₂
    rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
    have ha₁ : a ∈ U₁ := (induced G U₁).ends_mem e ((hMP_props U₁ hU₁).1 he₁) a
      (by rw [hab]; exact Sym2.mem_mk_left _ _)
    have ha₂ : a ∈ U₂ := (induced G U₂).ends_mem e ((hMP_props U₂ hU₂).1 he₂) a
      (by rw [hab]; exact Sym2.mem_mk_left _ _)
    exact Finset.disjoint_left.mp (C.P.disjoint hU₁ hU₂ hne) ha₁ ha₂
  have hdisj_M' : Disjoint (C.P.parts.biUnion MP) (M₂.map (Function.Embedding.subtype _)) := by
    rw [Finset.disjoint_left]
    intro e he_bi he_M₂
    rcases Finset.mem_biUnion.mp he_bi with ⟨U, hU, heU⟩
    rcases Finset.mem_map.mp he_M₂ with ⟨f, _, rfl⟩
    have heU_sym2 : G.ends f.1 ∈ U.sym2 :=
      (Finset.mem_filter.mp ((hMP_props U hU).1 heU)).2
    exact not_mem_sym2_of_shrinkE f ⟨U, hU⟩ heU_sym2
  have hM'_card : M'.card = (∑ U ∈ C.P.parts, (MP U).card) + M₂.card := by
    rw [Finset.card_union_of_disjoint hdisj_M', hbi_MP_card, Finset.card_map]
  have hM_bi_eq : M.filter (fun e => ((G.ends e).map (partOf C.P)).IsDiag) =
      C.P.parts.biUnion (fun U => M.filter (fun e => G.ends e ∈ U.sym2)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_biUnion, isDiag_map_partOf_iff]
    exact ⟨fun ⟨heM, U, hU, heU⟩ => ⟨U, hU, heM, heU⟩,
      fun ⟨U, hU, heM, heU⟩ => ⟨heM, U, hU, heU⟩⟩
  have hM_bi_card : (M.filter (fun e => ((G.ends e).map (partOf C.P)).IsDiag)).card =
      ∑ U ∈ C.P.parts, (M.filter (fun e => G.ends e ∈ U.sym2)).card := by
    rw [hM_bi_eq]
    refine Finset.card_biUnion fun U₁ hU₁ U₂ hU₂ hne => ?_
    rw [Function.onFun, Finset.disjoint_left]
    intro e he₁ he₂
    rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
    have ha₁ : a ∈ U₁ := by
      have := (Finset.mem_filter.mp he₁).2
      rw [hab, Finset.mk_mem_sym2_iff] at this; exact this.1
    have ha₂ : a ∈ U₂ := by
      have := (Finset.mem_filter.mp he₂).2
      rw [hab, Finset.mk_mem_sym2_iff] at this; exact this.1
    exact Finset.disjoint_left.mp (C.P.disjoint hU₁ hU₂ hne) ha₁ ha₂
  have hM_not_diag_card : (M.filter (fun e => ¬ ((G.ends e).map (partOf C.P)).IsDiag)).card =
      (shrinkMatching G C.P M).card := by
    rw [shrinkMatching, Finset.card_subtype]
  have hM_split := (Finset.card_filter_add_card_filter_not (s := M)
    (p := fun e => ((G.ends e).map (partOf C.P)).IsDiag)).symm
  have hM'_eq_M_card : M'.card = M.card := by
    rw [hM'_card, Finset.sum_congr rfl hMP_card_eq, hM₂_card, ← hM_bi_card,
      ← hM_not_diag_card, hM_split]
  have hM'_max : PathsTreesFlowers.Duality.IsMaxMatching G M' :=
    ⟨hM'_match, fun N hN => hM'_eq_M_card.symm ▸ C.hM.2 N hN⟩
  exact ⟨M', hM'_max, hM'_exp⟩

end SolPathsTreesFlowersOuterExposed65

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (C : PathsTreesFlowers.Invariance.Config60 G M) :
    ∀ v ∈ PathsTreesFlowers.Invariance.outerSet C, ∃ M' : Finset E,
      PathsTreesFlowers.Duality.IsMaxMatching G M' ∧
      PathsTreesFlowers.Duality.IsExposed G M' v :=
  SolPathsTreesFlowersOuterExposed65.outer_exposed_6_5 G M C
