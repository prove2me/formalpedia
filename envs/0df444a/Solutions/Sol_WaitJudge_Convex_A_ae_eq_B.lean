-- Prove2me | solution 1 for WaitJudge.Convex.A_ae_eq_B
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T23:40:31.741754+00:00
-- url     : https://prove2.me/submissions/6045144e-d831-4117-a747-62a78998b9bf

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_WaitJudge_Convex_Setting

open MeasureTheory ScenarioApproach.Generalization WaitJudge.Convex

theorem solution {d p : ℕ} {Δ : Type*} [MeasurableSpace Δ] (P : Measure Δ) [IsProbabilityMeasure P]
    (c : E d) (X : Set (E d)) (Xδ : Δ → Set (E d)) (tb : Fin p → E d → ℝ)
    (hA1 : Assumption1 c X Xδ tb) (hA2 : Assumption2 c X Xδ tb P)
    (ε : ℕ → ℝ) (N k : ℕ) (hk : k ≤ N) :
    {ω : Fin N → Δ | ε k < violation P Xδ (xstar c X Xδ tb ω) ∧ sstar c X Xδ tb ω = k ∧
        ∀ i : Fin N, i.val < k → i ∈ supportSet c X Xδ tb ω}
      =ᵐ[Measure.pi fun _ : Fin N => P]
    {ω : Fin N → Δ | ε k < violation P Xδ (xstar c X Xδ tb (firstK hk ω)) ∧
        sstar c X Xδ tb (firstK hk ω) = k ∧
        ∀ j : Fin N, k ≤ j.val → xstar c X Xδ tb (firstK hk ω) ∈ Xδ (ω j)} := by
  classical
  -- generic facts about the tie-broken solution
  have solspec : ∀ F : Set (E d), (∃! x, IsTBSolution c tb F x) →
      IsTBSolution c tb F (sol c tb F) := by
    intro F h
    have : sol c tb F = h.exists.choose := by simp [sol, h]
    rw [this]; exact h.exists.choose_spec
  have soleq : ∀ (F : Set (E d)) (x : E d), (∃! x, IsTBSolution c tb F x) →
      IsTBSolution c tb F x → sol c tb F = x := by
    intro F x h hx
    exact h.unique (solspec F h) hx
  have mono : ∀ (F F' : Set (E d)) (x : E d), F' ⊆ F → x ∈ F' → IsTBSolution c tb F x →
      IsTBSolution c tb F' x := by
    intro F F' x hsub hx h
    exact ⟨hx, fun y hy => h.2 y (hsub hy)⟩
  have anti : ∀ (ω : Fin N → Δ) (J J' : Finset (Fin N)), J ⊆ J' →
      feasibleOn X Xδ ω J' ⊆ feasibleOn X Xδ ω J := by
    intro ω J J' hJ x hx
    exact ⟨hx.1, fun i hi => hx.2 i (hJ hi)⟩
  -- Assumption 1 applies to every subsample
  have U : ∀ (ω : Fin N → Δ) (J : Finset (Fin N)),
      ∃! x, IsTBSolution c tb (feasibleOn X Xδ ω J) x := by
    intro ω J
    have h := hA1 J.card (fun j => ω (J.orderEmbOfFin rfl j))
    have hF : feasibleOn X Xδ (fun j => ω (J.orderEmbOfFin rfl j)) Finset.univ =
        feasibleOn X Xδ ω J := by
      ext x
      simp only [feasibleOn, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_univ, true_implies]
      constructor
      · rintro ⟨hx, h⟩
        refine ⟨hx, fun i hi => ?_⟩
        have : i ∈ Set.range (J.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]; exact hi
        obtain ⟨j, rfl⟩ := this
        exact h j
      · rintro ⟨hx, h⟩
        exact ⟨hx, fun j => h _ (Finset.orderEmbOfFin_mem J rfl j)⟩
    rwa [hF] at h
  let e : Fin k ↪ Fin N := Fin.castLEEmb hk
  have hfirst : ∀ (ω : Fin N → Δ) (J : Finset (Fin k)),
      feasibleOn X Xδ (firstK hk ω) J = feasibleOn X Xδ ω (J.map e) := by
    intro ω J
    ext x
    simp [feasibleOn, firstK, e]
  set I₀ : Finset (Fin N) := Finset.univ.map e with hI₀
  have hI₀mem : ∀ i : Fin N, i ∈ I₀ ↔ i.val < k := by
    intro i
    simp only [hI₀, Finset.mem_map, Finset.mem_univ, true_and, e]
    constructor
    · rintro ⟨j, rfl⟩; simp
    · intro h; exact ⟨⟨i.val, h⟩, by ext; simp⟩
  have hI₀card : I₀.card = k := by simp [hI₀]
  have herase : ∀ i : Fin k, (Finset.univ.erase i).map e = I₀.erase (e i) := by
    intro i
    rw [hI₀, Finset.map_erase]
  filter_upwards [hA2 N] with ω hG
  -- notation
  set F := fun J => feasibleOn X Xδ ω J with hFdef
  set xN := xstar c X Xδ tb ω with hxN
  set xk := xstar c X Xδ tb (firstK hk ω) with hxk
  have hxk' : xk = sol c tb (F I₀) := by
    rw [hxk, xstar, hfirst]
  have hsuppN : ∀ i : Fin N, i ∈ supportSet c X Xδ tb ω ↔
      sol c tb (F (Finset.univ.erase i)) ≠ xN := by
    intro i; simp [supportSet, IsSupport, hxN, xstar, hFdef]
  have hsuppk : ∀ i : Fin k, i ∈ supportSet c X Xδ tb (firstK hk ω) ↔
      sol c tb (F (I₀.erase (e i))) ≠ xk := by
    intro i
    simp only [supportSet, IsSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hfirst, herase, ← xstar, ← hxk]
  have hxNspec : IsTBSolution c tb (F Finset.univ) xN := solspec _ (U ω _)
  have hxkspec : IsTBSolution c tb (F I₀) xk := by rw [hxk']; exact solspec _ (U ω _)
  apply propext
  constructor
  · -- A ⊆ B
    rintro ⟨hV, hcard, hsub⟩
    have hS : supportSet c X Xδ tb ω = I₀ := by
      have h1 : I₀ ⊆ supportSet c X Xδ tb ω := fun i hi => hsub i ((hI₀mem i).1 hi)
      exact (Finset.eq_of_subset_of_card_le h1 (by rw [hI₀card]; exact hcard.le)).symm
    have hG' : sol c tb (F I₀) = xN := by rw [← hS]; exact hG
    have hkN : xk = xN := by rw [hxk', hG']
    refine ⟨by change ε k < violation P Xδ xk; rw [hkN]; exact hV, ?_, ?_⟩
    · have : supportSet c X Xδ tb (firstK hk ω) = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro i
        rw [hsuppk]
        intro heq
        have hi : e i ∈ supportSet c X Xδ tb ω := by rw [hS]; simp [hI₀]
        rw [hsuppN] at hi
        apply hi
        apply soleq _ _ (U ω _)
        have hspec := solspec _ (U ω (I₀.erase (e i)))
        rw [heq, hkN] at hspec
        refine mono _ _ _ (anti ω _ _ ?_) (anti ω _ _ (Finset.subset_univ _) hxNspec.1) hspec
        intro j hj
        simp only [Finset.mem_erase] at hj ⊢
        exact ⟨hj.1, Finset.mem_univ _⟩
      simp [sstar, this]
    · intro j _
      change xk ∈ Xδ (ω j)
      rw [hkN]
      exact hxNspec.1.2 j (Finset.mem_univ _)
  · -- B ⊆ A
    rintro ⟨hV, hcard, hsat⟩
    have hSk : supportSet c X Xδ tb (firstK hk ω) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa [sstar] using hcard)
    have hxkN : xk ∈ F Finset.univ := by
      refine ⟨hxkspec.1.1, fun j _ => ?_⟩
      by_cases hj : j.val < k
      · exact hxkspec.1.2 j ((hI₀mem j).2 hj)
      · exact hsat j (by omega)
    have hkN : xN = xk := soleq _ _ (U ω _)
      (mono _ _ _ (anti ω _ _ (Finset.subset_univ _)) hxkN hxkspec)
    -- constraints outside the first k are not of support
    have hout : ∀ j : Fin N, j ∉ I₀ → j ∉ supportSet c X Xδ tb ω := by
      intro j hj
      rw [hsuppN, not_not, hkN]
      apply soleq _ _ (U ω _)
      refine mono _ _ _ (anti ω _ _ ?_) (anti ω _ _ (Finset.subset_univ _) hxkN) hxkspec
      intro i hi
      exact Finset.mem_erase.2 ⟨fun h => hj (h ▸ hi), Finset.mem_univ _⟩
    have hin : ∀ i : Fin N, i ∈ I₀ → i ∈ supportSet c X Xδ tb ω := by
      intro i hi
      by_contra hns
      obtain ⟨i', _, rfl⟩ := Finset.mem_map.1 hi
      have hsubS : supportSet c X Xδ tb ω ⊆ I₀.erase (e i') := by
        intro j hj
        refine Finset.mem_erase.2 ⟨fun h => hns (h ▸ hj), ?_⟩
        by_contra h; exact hout j h hj
      have hspecS := solspec _ (U ω (supportSet c X Xδ tb ω))
      rw [hG, hkN] at hspecS
      have hmem : xk ∈ F (I₀.erase (e i')) :=
        anti ω _ _ (Finset.erase_subset _ _) hxkspec.1
      have := soleq _ _ (U ω _) (mono _ _ _ (anti ω _ _ hsubS) hmem hspecS)
      have hsk := (hsuppk i').1 (by rw [hSk]; exact Finset.mem_univ _)
      exact hsk this
    have hS : supportSet c X Xδ tb ω = I₀ := by
      ext j
      constructor
      · intro hj; by_contra h; exact hout j h hj
      · exact hin j
    refine ⟨by change ε k < violation P Xδ xN; rw [hkN]; exact hV, by simp [sstar, hS, hI₀card], fun i hi => ?_⟩
    rw [hS]; exact (hI₀mem i).2 hi
