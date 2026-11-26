-- Prove2me | solution 1 for RamseyLib.erdos_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:18:39.155732+00:00
-- url     : https://prove2.me/submissions/80f4b8e7-c19a-4530-94d1-e7843bbaa18a

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
public import Theorems.Thm_RamseyLib_card_offDiag_sym2
public import Theorems.Thm_RamseyLib_two_mul_choose_lt

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyLib
namespace RamseyLib
theorem _root_.solution (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : (n : ℝ) ≤ 2 ^ ((k : ℝ) / 2)) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  classical
  have hn2 : n ^ 2 ≤ 2 ^ k := by
    have : ((n : ℝ)) ^ 2 ≤ (2 : ℝ) ^ k := by
      calc (n : ℝ) ^ 2 ≤ ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ 2 := pow_le_pow_left₀ (by positivity) hn 2
        _ = 2 ^ k := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num)]
          norm_num
    exact_mod_cast this
  set P : Finset (Fin n) → Finset (Sym2 (Fin n)) :=
    fun S => S.sym2.filter (fun e => ¬ e.IsDiag) with hP
  set E := P Finset.univ with hE
  have hPE : ∀ S, P S ⊆ E := fun S => by
    intro e he
    simp only [hP, hE, Finset.mem_filter] at he ⊢
    exact ⟨Finset.sym2_mono (Finset.subset_univ S) he.1, he.2⟩
  set B := (Finset.univ.powersetCard k).biUnion (fun S =>
    E.powerset.filter (fun X => P S ⊆ X) ∪ E.powerset.filter (fun X => Disjoint (P S) X)) with hB
  have hcount : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      (E.powerset.filter (fun X => P S ⊆ X) ∪
        E.powerset.filter (fun X => Disjoint (P S) X)).card ≤
        2 * 2 ^ (n.choose 2 - k.choose 2) := by
    intro S hS
    have hSc : S.card = k := (Finset.mem_powersetCard.1 hS).2
    have hcd : (E \ P S).card = n.choose 2 - k.choose 2 := by
      rw [Finset.card_sdiff_of_subset (hPE S), hE, hP, card_offDiag_sym2, card_offDiag_sym2,
        Finset.card_univ, Fintype.card_fin, hSc]
    have h1 : E.powerset.filter (fun X => P S ⊆ X) ⊆
        (E \ P S).powerset.image (fun Y => Y ∪ P S) := by
      intro X hX
      rw [Finset.mem_filter, Finset.mem_powerset] at hX
      rw [Finset.mem_image]
      exact ⟨X \ P S, Finset.mem_powerset.2 (Finset.sdiff_subset_sdiff hX.1 le_rfl),
        Finset.sdiff_union_of_subset hX.2⟩
    have h2 : E.powerset.filter (fun X => Disjoint (P S) X) ⊆ (E \ P S).powerset := by
      intro X hX
      rw [Finset.mem_filter, Finset.mem_powerset] at hX
      exact Finset.mem_powerset.2 (Finset.subset_sdiff.2 ⟨hX.1, hX.2.symm⟩)
    calc _ ≤ _ := Finset.card_union_le _ _
      _ ≤ ((E \ P S).powerset.image (fun Y => Y ∪ P S)).card + (E \ P S).powerset.card :=
          add_le_add (Finset.card_le_card h1) (Finset.card_le_card h2)
      _ ≤ (E \ P S).powerset.card + (E \ P S).powerset.card :=
          Nat.add_le_add_right Finset.card_image_le _
      _ = 2 * 2 ^ (n.choose 2 - k.choose 2) := by rw [Finset.card_powerset, hcd]; ring
  have hEc : E.card = n.choose 2 := by
    rw [hE, hP, card_offDiag_sym2, Finset.card_univ, Fintype.card_fin]
  have hBlt : B.card < E.powerset.card := by
    rw [Finset.card_powerset, hEc]
    calc B.card ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          (E.powerset.filter (fun X => P S ⊆ X) ∪
            E.powerset.filter (fun X => Disjoint (P S) X)).card := Finset.card_biUnion_le
      _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          2 * 2 ^ (n.choose 2 - k.choose 2) := Finset.sum_le_sum hcount
      _ = n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
      _ < 2 ^ n.choose 2 := by
          rcases lt_or_ge n k with hnk | hnk
          · rw [Nat.choose_eq_zero_of_lt hnk, zero_mul]; positivity
          · have hK : k.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hnk
            have := two_mul_choose_lt k n hk hn2
            calc n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2))
                = (2 * n.choose k) * 2 ^ (n.choose 2 - k.choose 2) := by ring
              _ < 2 ^ k.choose 2 * 2 ^ (n.choose 2 - k.choose 2) := by gcongr
              _ = 2 ^ n.choose 2 := by rw [← pow_add]; congr 1; omega
  obtain ⟨X, hXE, hXB⟩ := Finset.exists_mem_notMem_of_card_lt_card hBlt
  rw [Finset.mem_powerset] at hXE
  refine ⟨fromEdgeSet (X : Set (Sym2 (Fin n))), ?_, ?_⟩
  · intro S hS
    apply hXB
    rw [hB, Finset.mem_biUnion]
    refine ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS.card_eq⟩,
      Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hXE, ?_⟩)⟩
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [hP, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at he
      have := hS.1 (Finset.mem_coe.2 he.1.1) (Finset.mem_coe.2 he.1.2) he.2
      rw [fromEdgeSet_adj] at this
      exact this.1
  · intro S hS
    apply hXB
    rw [hB, Finset.mem_biUnion]
    refine ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS.card_eq⟩,
      Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hXE, ?_⟩)⟩
    rw [Finset.disjoint_left]
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [hP, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at he
      have := hS.1 (Finset.mem_coe.2 he.1.1) (Finset.mem_coe.2 he.1.2) he.2
      rw [compl_adj, fromEdgeSet_adj] at this
      exact fun hX => this.2 ⟨hX, he.2⟩
end RamseyLib
