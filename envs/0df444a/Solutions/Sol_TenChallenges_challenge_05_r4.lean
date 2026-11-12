-- Prove2me | solution 1 for TenChallenges.challenge_05_r4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:59:49.689255+00:00
-- url     : https://prove2.me/submissions/db14e8fd-0de8-440e-9a38-1b4efad6ea53

import Definitions.Def_TenChallenges_Challenge_05
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option linter.all false

open SimpleGraph

namespace Aux_TC05_R4

section Cograph

variable {V : Type*} [DecidableEq V]

def NoP4On (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    G.Adj a b → G.Adj b c → G.Adj c d →
    ¬ G.Adj a c → ¬ G.Adj a d → ¬ G.Adj b d → False

lemma noP4On_mono {G : SimpleGraph V} {S T : Finset V} (hST : S ⊆ T) (h : NoP4On G T) :
    NoP4On G S :=
  fun a ha b hb c hc d hd => h a (hST ha) b (hST hb) c (hST hc) d (hST hd)

lemma noP4On_univ_of_not_induce [Fintype V] {G : SimpleGraph V}
    (hfree : ¬ pathGraph 4 ⊴ G) : NoP4On G Finset.univ := by
  intro a _ b _ c _ d _ hab hbc hcd hac had hbd
  apply hfree
  have hab_ne : a ≠ b := G.ne_of_adj hab
  have hbc_ne : b ≠ c := G.ne_of_adj hbc
  have hcd_ne : c ≠ d := G.ne_of_adj hcd
  have hac_ne : a ≠ c := fun h => had (h ▸ hcd)
  have hbd_ne : b ≠ d := fun h => had (h ▸ hab)
  have had_ne : a ≠ d := fun h => hac (h ▸ hcd.symm)
  refine ⟨{ toFun := ![a, b, c, d], inj' := ?_, map_rel_iff' := ?_ }⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [hab_ne, hab_ne.symm, hbc_ne, hbc_ne.symm, hcd_ne, hcd_ne.symm,
        hac_ne, hac_ne.symm, hbd_ne, hbd_ne.symm, had_ne, had_ne.symm]
  · intro i j
    change G.Adj (![a, b, c, d] i) (![a, b, c, d] j) ↔ (pathGraph 4).Adj i j
    fin_cases i <;> fin_cases j <;>
      simp [pathGraph, hab, hab.symm, hbc, hbc.symm, hcd, hcd.symm,
        hac, had, hbd,
        show ¬ G.Adj c a from fun h => hac h.symm,
        show ¬ G.Adj d a from fun h => had h.symm,
        show ¬ G.Adj d b from fun h => hbd h.symm]

lemma noP4On_compl {G : SimpleGraph V} {S : Finset V} (h : NoP4On G S) :
    NoP4On Gᶜ S := by
  intro a ha b hb c hc d hd hab hbc hcd hac had hbd
  have hac_ne : a ≠ c := fun e => had (e ▸ hcd)
  have hbd_ne : b ≠ d := fun e => had (e ▸ hab)
  have had_ne : a ≠ d := fun e => hac (e ▸ hcd.symm)
  have h_bd : G.Adj b d := by
    by_contra hnot; exact hbd ((G.compl_adj b d).mpr ⟨hbd_ne, hnot⟩)
  have h_da : G.Adj d a := by
    by_contra hnot; exact had ((G.compl_adj a d).mpr ⟨had_ne, fun h' => hnot h'.symm⟩)
  have h_ac : G.Adj a c := by
    by_contra hnot; exact hac ((G.compl_adj a c).mpr ⟨hac_ne, hnot⟩)
  have hn_ba : ¬ G.Adj b a := fun h' => ((G.compl_adj a b).mp hab).2 h'.symm
  have hn_bc : ¬ G.Adj b c := ((G.compl_adj b c).mp hbc).2
  have hn_dc : ¬ G.Adj d c := fun h' => ((G.compl_adj c d).mp hcd).2 h'.symm
  exact h b hb d hd a ha c hc h_bd h_da h_ac hn_ba hn_bc hn_dc

def HasCut (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ X Y : Finset V, X.Nonempty ∧ Y.Nonempty ∧ Disjoint X Y ∧ X ∪ Y = S ∧
    ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y

private lemma seinsche_half {H : SimpleGraph V} {S : Finset V}
    (hfree : NoP4On H S) {v₀ : V} (hv₀ : v₀ ∈ S)
    {X Y : Finset V} (hdisj : Disjoint X Y) (hunion : X ∪ Y = S.erase v₀)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, ¬ H.Adj x y)
    (hX_adj : ∃ x ∈ X, H.Adj v₀ x)
    (hY_adj : ∃ y ∈ Y, H.Adj v₀ y)
    (hX_nadj : ∃ z ∈ X, ¬ H.Adj v₀ z) :
    HasCut H S := by
  classical
  let X₁ := X.filter (fun x => H.Adj v₀ x)
  let X₂ := X.filter (fun x => ¬ H.Adj v₀ x)
  obtain ⟨x₁, hx₁X, hvx₁⟩ := hX_adj
  obtain ⟨x₂, hx₂X, hnvx₂⟩ := hX_nadj
  obtain ⟨c, hcY, hv₀c⟩ := hY_adj
  have hX₁_ne : X₁.Nonempty := ⟨x₁, Finset.mem_filter.mpr ⟨hx₁X, hvx₁⟩⟩
  have hX₂_ne : X₂.Nonempty := ⟨x₂, Finset.mem_filter.mpr ⟨hx₂X, hnvx₂⟩⟩
  have hv₀_not_erase : v₀ ∉ S.erase v₀ := Finset.notMem_erase v₀ S
  have hv₀_not_X : v₀ ∉ X := fun h => hv₀_not_erase (hunion ▸ Finset.mem_union_left Y h)
  by_cases hcross : ∃ a ∈ X₁, ∃ b ∈ X₂, H.Adj a b
  · obtain ⟨a, ha₁, b, hb₂, hab⟩ := hcross
    have haX : a ∈ X := (Finset.mem_filter.mp ha₁).1
    have hv₀a : H.Adj v₀ a := (Finset.mem_filter.mp ha₁).2
    have hbX : b ∈ X := (Finset.mem_filter.mp hb₂).1
    have hnv₀b : ¬ H.Adj v₀ b := (Finset.mem_filter.mp hb₂).2
    have haS : a ∈ S := Finset.mem_of_mem_erase (hunion ▸ Finset.mem_union_left Y haX)
    have hbS : b ∈ S := Finset.mem_of_mem_erase (hunion ▸ Finset.mem_union_left Y hbX)
    have hcS : c ∈ S := Finset.mem_of_mem_erase (hunion ▸ Finset.mem_union_right X hcY)
    exact False.elim (hfree b hbS a haS v₀ hv₀ c hcS
      hab.symm hv₀a.symm hv₀c
      (fun hbv => hnv₀b hbv.symm)
      (hXY b hbX c hcY)
      (hXY a haX c hcY))
  · push Not at hcross
    refine ⟨X₂, insert v₀ (X₁ ∪ Y), hX₂_ne, Finset.insert_nonempty _ _, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_insert_right]
      refine ⟨fun h => hv₀_not_X (Finset.filter_subset _ _ h), ?_⟩
      rw [Finset.disjoint_union_right]
      refine ⟨Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h1 h2), ?_⟩
      exact Disjoint.mono_left (Finset.filter_subset _ _) hdisj
    · ext w
      simp only [Finset.mem_union, Finset.mem_insert, X₁, X₂, Finset.mem_filter]
      constructor
      · rintro (⟨hwX, _⟩ | rfl | ⟨hwX, _⟩ | hwY)
        · exact Finset.mem_of_mem_erase (hunion ▸ Finset.mem_union_left Y hwX)
        · exact hv₀
        · exact Finset.mem_of_mem_erase (hunion ▸ Finset.mem_union_left Y hwX)
        · exact Finset.mem_of_mem_erase (hunion ▸ Finset.mem_union_right X hwY)
      · intro hwS
        by_cases hwv : w = v₀
        · exact Or.inr (Or.inl hwv)
        · have hwe : w ∈ X ∪ Y := hunion.symm ▸ Finset.mem_erase.mpr ⟨hwv, hwS⟩
          rcases Finset.mem_union.mp hwe with hwX | hwY
          · by_cases hadj : H.Adj v₀ w
            · exact Or.inr (Or.inr (Or.inl ⟨hwX, hadj⟩))
            · exact Or.inl ⟨hwX, hadj⟩
          · exact Or.inr (Or.inr (Or.inr hwY))
    · intro x hx y hy
      have hxX : x ∈ X := (Finset.mem_filter.mp hx).1
      have hnv₀x : ¬ H.Adj v₀ x := (Finset.mem_filter.mp hx).2
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact fun hxv => hnv₀x hxv.symm
      · rcases Finset.mem_union.mp hy' with hy₁ | hyY
        · exact fun hxy => hcross y hy₁ x hx hxy.symm
        · exact hXY x hxX y hyY

private lemma seinsche_step {H : SimpleGraph V} {S : Finset V}
    (hfree : NoP4On H S) {v₀ : V} (hv₀ : v₀ ∈ S)
    (hcut : HasCut H (S.erase v₀)) :
    HasCut H S ∨ HasCut Hᶜ S := by
  classical
  obtain ⟨X, Y, hXne, hYne, hdisj, hunion, hXY⟩ := hcut
  have hv₀_not_erase : v₀ ∉ S.erase v₀ := Finset.notMem_erase v₀ S
  have hv₀_not_X : v₀ ∉ X := fun h => hv₀_not_erase (hunion ▸ Finset.mem_union_left Y h)
  have hv₀_not_Y : v₀ ∉ Y := fun h => hv₀_not_erase (hunion ▸ Finset.mem_union_right X h)
  by_cases hX_adj : ∃ x ∈ X, H.Adj v₀ x
  · by_cases hY_adj : ∃ y ∈ Y, H.Adj v₀ y
    · by_cases hall : ∀ z ∈ S.erase v₀, H.Adj v₀ z
      · refine Or.inr ⟨{v₀}, S.erase v₀, Finset.singleton_nonempty v₀, ?_, ?_, ?_, ?_⟩
        · exact hunion ▸ hXne.mono (Finset.subset_union_left)
        · simp [hv₀_not_erase]
        · exact Finset.singleton_union _ _ |>.trans (Finset.insert_erase hv₀)
        · intro x hx y hy hcadj
          rw [Finset.mem_singleton.mp hx] at hcadj
          exact ((H.compl_adj v₀ y).mp hcadj).2 (hall y hy)
      · push Not at hall
        obtain ⟨z, hz_er, hnv₀z⟩ := hall
        rcases Finset.mem_union.mp (hunion.symm ▸ hz_er) with hzX | hzY
        · exact Or.inl (seinsche_half hfree hv₀ hdisj hunion hXY hX_adj hY_adj ⟨z, hzX, hnv₀z⟩)
        · exact Or.inl (seinsche_half hfree hv₀ hdisj.symm (Finset.union_comm X Y ▸ hunion)
            (fun y hy x hx h => hXY x hx y hy h.symm) hY_adj hX_adj ⟨z, hzY, hnv₀z⟩)
    · push Not at hY_adj
      refine Or.inl ⟨insert v₀ X, Y, Finset.insert_nonempty _ _, hYne, ?_, ?_, ?_⟩
      · exact Finset.disjoint_insert_left.mpr ⟨hv₀_not_Y, hdisj⟩
      · rw [Finset.insert_union, hunion, Finset.insert_erase hv₀]
      · intro x hx y hy
        rcases Finset.mem_insert.mp hx with rfl | hxX
        · exact hY_adj y hy
        · exact hXY x hxX y hy
  · push Not at hX_adj
    refine Or.inl ⟨X, insert v₀ Y, hXne, Finset.insert_nonempty _ _, ?_, ?_, ?_⟩
    · exact Finset.disjoint_insert_right.mpr ⟨hv₀_not_X, hdisj⟩
    · rw [Finset.union_insert, hunion, Finset.insert_erase hv₀]
    · intro x hx y hy
      rcases Finset.mem_insert.mp hy with rfl | hyY
      · exact fun h => hX_adj x hx h.symm
      · exact hXY x hx y hyY

theorem seinsche (G : SimpleGraph V) :
    ∀ n : ℕ, ∀ S : Finset V, S.card = n → 2 ≤ n → NoP4On G S →
      HasCut G S ∨ HasCut Gᶜ S := by
  classical
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro S hcard hn hfree
    by_cases hn2 : n = 2
    · subst hn2
      obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard
      by_cases hadj : G.Adj u v
      · refine Or.inr ⟨{u}, {v}, Finset.singleton_nonempty u, Finset.singleton_nonempty v,
          by simp [huv], rfl, ?_⟩
        intro x hx y hy hcadj
        rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy] at hcadj
        exact ((G.compl_adj u v).mp hcadj).2 hadj
      · refine Or.inl ⟨{u}, {v}, Finset.singleton_nonempty u, Finset.singleton_nonempty v,
          by simp [huv], rfl, ?_⟩
        intro x hx y hy
        rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy]
        exact hadj
    · have hn3 : 3 ≤ n := by omega
      have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨v₀, hv₀⟩ := hSne
      have hcard_er : (S.erase v₀).card = n - 1 := by
        rw [Finset.card_erase_of_mem hv₀, hcard]
      have hfree_er : NoP4On G (S.erase v₀) :=
        noP4On_mono (Finset.erase_subset v₀ S) hfree
      rcases ih (n - 1) (by omega) (S.erase v₀) hcard_er (by omega) hfree_er with hcut | hcut
      · exact seinsche_step hfree hv₀ hcut
      · rcases seinsche_step (H := Gᶜ) (noP4On_compl hfree) hv₀ hcut with h1 | h2
        · exact Or.inr h1
        · rw [compl_compl] at h2
          exact Or.inl h2

theorem card_le_clique_mul_indep (G : SimpleGraph V) :
    ∀ n : ℕ, ∀ S : Finset V, S.card = n → NoP4On G S →
      ∃ C I : Finset V, C ⊆ S ∧ I ⊆ S ∧ G.IsClique (C : Set V) ∧ Gᶜ.IsClique (I : Set V) ∧
        S.card ≤ C.card * I.card := by
  classical
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro S hcard hfree
    by_cases hn0 : n = 0
    · subst hn0
      have hSe : S = ∅ := Finset.card_eq_zero.mp hcard
      subst hSe
      exact ⟨∅, ∅, Finset.Subset.rfl, Finset.Subset.rfl, by simp, by simp, by simp⟩
    · by_cases hn1 : n = 1
      · subst hn1
        obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
        exact ⟨{v}, {v}, Finset.Subset.rfl, Finset.Subset.rfl, by simp, by simp, by simp⟩
      · have hn2 : 2 ≤ n := by omega
        rcases seinsche G n S hcard hn2 hfree with hcut | hcut
        · obtain ⟨X, Y, hXne, hYne, hdisj, hunion, hXY⟩ := hcut
          have hcard_sum : X.card + Y.card = n := by
            rw [← Finset.card_union_of_disjoint hdisj, hunion, hcard]
          have hXlt : X.card < n := by
            have := Finset.card_pos.mpr hYne; omega
          have hYlt : Y.card < n := by
            have := Finset.card_pos.mpr hXne; omega
          have hXS : X ⊆ S := hunion ▸ Finset.subset_union_left
          have hYS : Y ⊆ S := hunion ▸ Finset.subset_union_right
          obtain ⟨C₁, I₁, hC₁X, hI₁X, hC₁c, hI₁c, hb₁⟩ :=
            ih X.card hXlt X rfl (noP4On_mono hXS hfree)
          obtain ⟨C₂, I₂, hC₂Y, hI₂Y, hC₂c, hI₂c, hb₂⟩ :=
            ih Y.card hYlt Y rfl (noP4On_mono hYS hfree)
          have hIdisj : Disjoint I₁ I₂ := Disjoint.mono hI₁X hI₂Y hdisj
          have hIunion_clique : Gᶜ.IsClique ((I₁ ∪ I₂ : Finset V) : Set V) := by
            intro x hx y hy hxy
            rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with hx₁ | hx₂ <;>
            rcases Finset.mem_union.mp (Finset.mem_coe.mp hy) with hy₁ | hy₂
            · exact hI₁c hx₁ hy₁ hxy
            · exact (G.compl_adj x y).mpr ⟨hxy, hXY x (hI₁X hx₁) y (hI₂Y hy₂)⟩
            · exact (G.compl_adj x y).mpr ⟨hxy, fun h => hXY y (hI₁X hy₁) x (hI₂Y hx₂) h.symm⟩
            · exact hI₂c hx₂ hy₂ hxy
          rcases le_total C₁.card C₂.card with hCle | hCle
          · refine ⟨C₂, I₁ ∪ I₂, hC₂Y.trans hYS, Finset.union_subset (hI₁X.trans hXS) (hI₂Y.trans hYS),
              hC₂c, hIunion_clique, ?_⟩
            rw [Finset.card_union_of_disjoint hIdisj, mul_add, hcard, ← hcard_sum]
            exact add_le_add (hb₁.trans (Nat.mul_le_mul_right _ hCle)) hb₂
          · refine ⟨C₁, I₁ ∪ I₂, hC₁X.trans hXS, Finset.union_subset (hI₁X.trans hXS) (hI₂Y.trans hYS),
              hC₁c, hIunion_clique, ?_⟩
            rw [Finset.card_union_of_disjoint hIdisj, mul_add, hcard, ← hcard_sum]
            exact add_le_add hb₁ (hb₂.trans (Nat.mul_le_mul_right _ hCle))
        · obtain ⟨X, Y, hXne, hYne, hdisj, hunion, hXY⟩ := hcut
          have hcard_sum : X.card + Y.card = n := by
            rw [← Finset.card_union_of_disjoint hdisj, hunion, hcard]
          have hXlt : X.card < n := by
            have := Finset.card_pos.mpr hYne; omega
          have hYlt : Y.card < n := by
            have := Finset.card_pos.mpr hXne; omega
          have hXS : X ⊆ S := hunion ▸ Finset.subset_union_left
          have hYS : Y ⊆ S := hunion ▸ Finset.subset_union_right
          obtain ⟨C₁, I₁, hC₁X, hI₁X, hC₁c, hI₁c, hb₁⟩ :=
            ih X.card hXlt X rfl (noP4On_mono hXS hfree)
          obtain ⟨C₂, I₂, hC₂Y, hI₂Y, hC₂c, hI₂c, hb₂⟩ :=
            ih Y.card hYlt Y rfl (noP4On_mono hYS hfree)
          have hCdisj : Disjoint C₁ C₂ := Disjoint.mono hC₁X hC₂Y hdisj
          have hCunion_clique : G.IsClique ((C₁ ∪ C₂ : Finset V) : Set V) := by
            intro x hx y hy hxy
            rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with hx₁ | hx₂ <;>
            rcases Finset.mem_union.mp (Finset.mem_coe.mp hy) with hy₁ | hy₂
            · exact hC₁c hx₁ hy₁ hxy
            · by_contra hnot
              exact hXY x (hC₁X hx₁) y (hC₂Y hy₂) ((G.compl_adj x y).mpr ⟨hxy, hnot⟩)
            · by_contra hnot
              exact hXY y (hC₁X hy₁) x (hC₂Y hx₂) ((G.compl_adj y x).mpr ⟨hxy.symm, fun h => hnot h.symm⟩)
            · exact hC₂c hx₂ hy₂ hxy
          rcases le_total I₁.card I₂.card with hIle | hIle
          · refine ⟨C₁ ∪ C₂, I₂, Finset.union_subset (hC₁X.trans hXS) (hC₂Y.trans hYS), hI₂Y.trans hYS,
              hCunion_clique, hI₂c, ?_⟩
            rw [Finset.card_union_of_disjoint hCdisj, add_mul, hcard, ← hcard_sum]
            exact add_le_add (hb₁.trans (Nat.mul_le_mul_left _ hIle)) hb₂
          · refine ⟨C₁ ∪ C₂, I₁, Finset.union_subset (hC₁X.trans hXS) (hC₂Y.trans hYS), hI₁X.trans hXS,
              hCunion_clique, hI₁c, ?_⟩
            rw [Finset.card_union_of_disjoint hCdisj, add_mul, hcard, ← hcard_sum]
            exact add_le_add hb₁ (hb₂.trans (Nat.mul_le_mul_left _ hIle))

end Cograph

end Aux_TC05_R4

theorem solution : TenChallenges.statement_05 4 := by
  classical
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro V _ G hfree
  obtain ⟨C, I, _, _, hCc, hIc, hprod⟩ :=
    Aux_TC05_R4.card_le_clique_mul_indep G (Finset.univ : Finset V).card Finset.univ rfl
      (Aux_TC05_R4.noP4On_univ_of_not_induce hfree)
  rw [Finset.card_univ] at hprod
  let M : ℕ := max C.card I.card
  have hM_sq : (Fintype.card V : ℝ) ≤ (M : ℝ) ^ (2 : ℝ) := by
    have h1 : Fintype.card V ≤ M * M :=
      hprod.trans (Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _))
    have h2 : (Fintype.card V : ℝ) ≤ (M : ℝ) * (M : ℝ) := by exact_mod_cast h1
    simpa [Real.rpow_two, sq] using h2
  have hM_rpow : (Fintype.card V : ℝ) ^ (1 / 2 : ℝ) ≤ (M : ℝ) := by
    calc (Fintype.card V : ℝ) ^ (1 / 2 : ℝ)
        ≤ ((M : ℝ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hM_sq (by norm_num)
      _ = (M : ℝ) ^ ((2 : ℝ) * (1 / 2 : ℝ)) :=
          (Real.rpow_mul (Nat.cast_nonneg M) 2 (1 / 2)).symm
      _ = (M : ℝ) := by norm_num
  rcases le_total C.card I.card with hle | hle
  · refine ⟨I, Or.inr hIc, ?_⟩
    have hM_eq : M = I.card := max_eq_right hle
    rwa [← hM_eq]
  · refine ⟨C, Or.inl hCc, ?_⟩
    have hM_eq : M = C.card := max_eq_left hle
    rwa [← hM_eq]

#print axioms solution
