-- Prove2me | solution 1 for RainbowEFX.Sublinear.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:55:52.017349+00:00
-- url     : https://prove2.me/submissions/b854e14a-8a8f-4b4b-9d3a-82539c2eb6e0

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting
import Theorems.Thm_RainbowEFX_Sublinear_theorem_3
import Theorems.Thm_RainbowEFX_Sublinear_observation_7
import Theorems.Thm_RainbowEFX_Sublinear_observation_11
import Theorems.Thm_RainbowEFX_Sublinear_observation_13
import Theorems.Thm_RainbowEFX_Sublinear_lemma_14

open LittleCharity.EFX RainbowEFX.Sublinear

theorem solution {n m : ℕ} (hn : 0 < n) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hEFX : IsAlphaEFX (1 - ε) v X)
    (d : ℕ) (hd : 1 ≤ d) (hstar : Star ε v X) (hL : d ^ 4 + d < (LX ε v X d).card) :
    ∃ X' : Fin n → Finset (Fin m), IsPartialAllocation X' ∧ IsAlphaEFX (1 - ε) v X' ∧
      StronglyParetoDominates ε v X' X := by
  classical
  have hε1 : ε < 1 := by linarith
  have mono : ∀ i (A B : Finset (Fin m)), A ⊆ B → v i A ≤ v i B := by
    intro i A B hAB
    rw [hv.1 i A, hv.1 i B]
    exact Finset.sum_le_sum_of_subset_of_nonneg hAB (fun x _ _ => hv.2 i {x})
  -- Step 1: a source assignment exists since `E_X` is acyclic
  have hwf : WellFounded (fun s t : Fin n => Relation.TransGen (Envies v X) s t) := by
    haveI : IsTrans (Fin n) (fun s t => Relation.TransGen (Envies v X) s t) :=
      ⟨fun _ _ _ h1 h2 => h1.trans h2⟩
    haveI : IsIrrefl (Fin n) (fun s t => Relation.TransGen (Envies v X) s t) :=
      ⟨fun i => hstar.1 i⟩
    exact Finite.wellFounded_of_trans_of_irrefl _
  have hsrcex : ∀ a : Fin n, ∃ s, IsSource v X s ∧ Reach v X s a := by
    intro a
    obtain ⟨s, hs, hmin⟩ := hwf.has_min {s | Reach v X s a} ⟨a, Relation.ReflTransGen.refl⟩
    refine ⟨s, ?_, hs⟩
    intro i hi
    exact hmin i (Relation.ReflTransGen.head hi hs) (Relation.TransGen.single hi)
  choose src hsrc1 hsrc2 using hsrcex
  have hsrc : IsSourceAssignment v X src := fun a => ⟨hsrc1 a, hsrc2 a⟩
  -- Step 2: every low-demand good is valuable to some agent
  have hQ : ∀ g ∈ LX ε v X d, ∃ a, Valuable ε v X g a := by
    intro g hg
    have hgP : g ∈ pool X := (Finset.mem_filter.mp hg).1
    set s := src ⟨0, hn⟩
    have hs : IsSource v X s := hsrc1 _
    have : ∃ i, StronglyEnvies ε v X i (insert g (X s)) := by
      by_contra hcon
      push_neg at hcon
      exact hstar.2.1 ⟨s, hs, g, hgP, hcon⟩
    obtain ⟨i, T, hTS, hT⟩ := this
    refine ⟨i, observation_11 v hv ε hε0 hε1 X g hgP s hs i ?_⟩
    unfold HeavilyEnvies at *
    have := mono i T _ hTS.subset
    nlinarith
  -- Step 3: the group champion graph as a `k`-partite digraph
  let ι := ↥(LX ε v X d)
  let V := {p : Fin m × Fin n // GCVertex ε v X d src p}
  let part : V → ι := fun w => ⟨w.1.1, w.2.1⟩
  let adj : V → V → Prop := fun u w => GCAdj ε v X src u.1 w.1
  have hcard : d ^ 4 + d < Fintype.card ι := by
    simpa [ι, Fintype.card_coe] using hL
  have hparts : ∀ i : ι, 1 ≤ Nat.card {w : V // part w = i} ∧
      Nat.card {w : V // part w = i} ≤ d := by
    rintro ⟨g, hg⟩
    constructor
    · obtain ⟨a, ha⟩ := hQ g hg
      have hne : Nonempty {w : V // part w = ⟨g, hg⟩} :=
        ⟨⟨⟨(g, src a), hg, a, ha, rfl⟩, rfl⟩⟩
      have : 0 < Nat.card {w : V // part w = ⟨g, hg⟩} := Nat.card_pos
      omega
    · have hle : Nat.card {w : V // part w = ⟨g, hg⟩} ≤
          Nat.card ↥((valuableAgents ε v X g).image src) := by
        refine Nat.card_le_card_of_injective
          (fun w => ⟨w.1.1.2, ?_⟩) ?_
        · have hwg : w.1.1.1 = g := congrArg Subtype.val w.2
          obtain ⟨_, a, ha, hsa⟩ := w.1.2
          rw [hwg] at ha
          rw [Finset.mem_image]
          exact ⟨a, by simpa [valuableAgents] using ha, hsa⟩
        · rintro ⟨⟨⟨g1, y1⟩, h1⟩, e1⟩ ⟨⟨⟨g2, y2⟩, h2⟩, e2⟩ heq
          have e1' : g1 = g := congrArg Subtype.val e1
          have e2' : g2 = g := congrArg Subtype.val e2
          have hy : y1 = y2 := congrArg Subtype.val heq
          subst e1' e2' hy
          rfl
      rw [Nat.card_eq_finsetCard] at hle
      have h1 := Finset.card_image_le (s := valuableAgents ε v X g) (f := src)
      have h2 : (valuableAgents ε v X g).card ≤ d := (Finset.mem_filter.mp hg).2
      omega
  have hin : InEdgeProperty part adj := by
    rintro ⟨⟨h, x⟩, hx⟩ ⟨g, hg⟩ -
    obtain ⟨y, hy, hadj⟩ := observation_13 v hv ε hε0 hε X hX hEFX d hstar src hsrc g h hg
      hx.1 x hx
    exact ⟨⟨(g, y), hy⟩, rfl, hadj⟩
  obtain ⟨r, c, hr2, hcinj, hcadj⟩ := (theorem_3 d hd).2.2 part adj hcard hparts hin
  -- Step 4: apply Lemma 14 to the rainbow cycle
  refine lemma_14 v hv ε hε0 hε X hX hEFX d hstar src hsrc r (fun i => (c i).1)
    (fun i => (c i).2) ⟨hr2, ?_, fun i => hcadj i⟩
  intro a b hab
  apply hcinj
  simp only [Function.comp_apply, part] at hab ⊢
  exact Subtype.ext hab
