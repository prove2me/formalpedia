-- Prove2me | solution 1 for WaitJudge.Convex.sstar_le_dim
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T23:44:18.595736+00:00
-- url     : https://prove2.me/submissions/dc6bb370-4985-4131-8e89-432cfc9e3896

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_WaitJudge_Convex_Setting

open MeasureTheory ScenarioApproach.Generalization WaitJudge.Convex

theorem solution {d p : ℕ} {Δ : Type*} (c : E d) (X : Set (E d)) (Xδ : Δ → Set (E d))
    (tb : Fin p → E d → ℝ) (hX : Convex ℝ X) (hXδ : ∀ δ, Convex ℝ (Xδ δ))
    (htb : ∀ j, ConvexOn ℝ Set.univ (tb j)) (hA1 : Assumption1 c X Xδ tb) :
    ∀ (m : ℕ) (ω : Fin m → Δ), sstar c X Xδ tb ω ≤ d := by
  classical
  intro m ω
  by_contra hlt
  push Not at hlt
  have solspec : ∀ F : Set (E d), (∃! x, IsTBSolution c tb F x) →
      IsTBSolution c tb F (sol c tb F) := by
    intro F h
    have : sol c tb F = h.exists.choose := by simp [sol, h]
    rw [this]; exact h.exists.choose_spec
  have U : ∀ J : Finset (Fin m), ∃! x, IsTBSolution c tb (feasibleOn X Xδ ω J) x := by
    intro J
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
  set xs := xstar c X Xδ tb ω with hxsdef
  have hxs : IsTBSolution c tb (feasibleOn X Xδ ω Finset.univ) xs := solspec _ (U _)
  let xi : Fin m → E d := fun i => sol c tb (feasibleOn X Xδ ω (Finset.univ.erase i))
  have hxi : ∀ i, IsTBSolution c tb (feasibleOn X Xδ ω (Finset.univ.erase i)) (xi i) :=
    fun i => solspec _ (U _)
  -- support constraints strictly improve the lexicographic key
  have hlexlt : ∀ i ∈ supportSet c X Xδ tb ω,
      toLex (key c tb (xi i)) < toLex (key c tb xs) := by
    intro i hi
    have hne : xi i ≠ xs := by
      simpa [supportSet, IsSupport, xi, hxsdef, xstar] using hi
    have hmem : xs ∈ feasibleOn X Xδ ω (Finset.univ.erase i) :=
      ⟨hxs.1.1, fun j _ => hxs.1.2 j (Finset.mem_univ _)⟩
    refine lt_of_le_of_ne ((hxi i).2 xs hmem) (fun heq => hne ?_)
    have hsol : IsTBSolution c tb (feasibleOn X Xδ ω (Finset.univ.erase i)) xs :=
      ⟨hmem, fun y hy => heq ▸ (hxi i).2 y hy⟩
    exact (U _).unique (hxi i) hsol
  -- convexity of the strict lexicographic sublevel set
  set S : Set (E d) := {y | toLex (key c tb y) < toLex (key c tb xs)} with hSdef
  have hSconv : Convex ℝ S := by
    intro y1 hy1 y2 hy2 a b ha hb hab
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · have hb1 : b = 1 := by linarith
      rw [← ha0, hb1, zero_smul, one_smul, zero_add]; exact hy2
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · have ha1 : a = 1 := by linarith
      rw [← hb0, ha1, zero_smul, one_smul, add_zero]; exact hy1
    have hkey : ∀ j, key c tb (a • y1 + b • y2) j ≤ a * key c tb y1 j + b * key c tb y2 j := by
      intro j
      refine Fin.cases ?_ (fun j' => ?_) j
      · simp [key, inner_add_right, inner_smul_right]
      · simp only [key, Fin.cons_succ]
        have := (htb j').2 (Set.mem_univ y1) (Set.mem_univ y2) ha hb hab
        simpa [smul_eq_mul] using this
    set w : Fin (p + 1) → ℝ := fun j => a * key c tb y1 j + b * key c tb y2 j with hw
    have hle : toLex (key c tb (a • y1 + b • y2)) ≤ toLex w := Pi.toLex_monotone hkey
    refine lt_of_le_of_lt hle ?_
    obtain ⟨r1, h1, h1'⟩ := hy1
    obtain ⟨r2, h2, h2'⟩ := hy2
    set t := key c tb xs
    replace h1' : key c tb y1 r1 < t r1 := h1'
    replace h2' : key c tb y2 r2 < t r2 := h2'
    have hcomb : ∀ j, key c tb y1 j = t j → key c tb y2 j = t j → w j = t j := by
      intro j e1 e2
      show a * key c tb y1 j + b * key c tb y2 j = t j
      rw [e1, e2, ← add_mul, hab, one_mul]
    rcases le_total r1 r2 with hr | hr
    · refine ⟨r1, fun j hj => hcomb j (h1 j hj) (h2 j (lt_of_lt_of_le hj hr)), ?_⟩
      show a * key c tb y1 r1 + b * key c tb y2 r1 < t r1
      have hle2 : key c tb y2 r1 ≤ t r1 := by
        rcases eq_or_lt_of_le hr with h | h
        · rw [h]; exact h2'.le
        · exact (h2 r1 h).le
      have ht : t r1 = a * t r1 + b * t r1 := by rw [← add_mul, hab, one_mul]
      linarith [mul_lt_mul_of_pos_left h1' ha0, mul_le_mul_of_nonneg_left hle2 hb]
    · refine ⟨r2, fun j hj => hcomb j (h1 j (lt_of_lt_of_le hj hr)) (h2 j hj), ?_⟩
      show a * key c tb y1 r2 + b * key c tb y2 r2 < t r2
      have hle1 : key c tb y1 r2 ≤ t r2 := by
        rcases eq_or_lt_of_le hr with h | h
        · rw [h]; exact h1'.le
        · exact (h1 r2 h).le
      have ht : t r2 = a * t r2 + b * t r2 := by rw [← add_mul, hab, one_mul]
      linarith [mul_lt_mul_of_pos_left h2' hb0, mul_le_mul_of_nonneg_left hle1 ha]
  -- sets satisfying all constraints outside Q
  let G : Set (Fin m) → Set (E d) := fun Q => {x | x ∈ X ∧ ∀ j, j ∉ Q → x ∈ Xδ (ω j)}
  have hGconv : ∀ Q, Convex ℝ (G Q) := by
    intro Q x hx y hy a b ha hb hab
    exact ⟨hX hx.1 hy.1 ha hb hab, fun j hj => hXδ _ (hx.2 j hj) (hy.2 j hj) ha hb hab⟩
  -- d + 1 support constraints and Radon's theorem on d + 2 points
  obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq (show d + 1 ≤ (supportSet c X Xδ tb ω).card
    from hlt)
  let s := T.orderEmbOfFin hTc
  have hsS : ∀ j, s j ∈ supportSet c X Xδ tb ω := fun j => hTS (Finset.orderEmbOfFin_mem T hTc j)
  let f : Option (Fin (d + 1)) → E d := fun o => o.elim xs (fun j => xi (s j))
  have hdep : ¬ AffineIndependent ℝ f := by
    intro h
    have := h.card_le_finrank_succ
    rw [Fintype.card_option, Fintype.card_fin] at this
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range f))
    rw [finrank_euclideanSpace_fin] at h2
    omega
  obtain ⟨I, z, hz1, hz2⟩ := Convex.radon_partition hdep
  let Q : Set (Option (Fin (d + 1))) → Set (Fin m) := fun K => {i | ∃ j, some j ∈ K ∧ s j = i}
  have hfG : ∀ K, f '' K ⊆ G (Q K) := by
    rintro K _ ⟨o, ho, rfl⟩
    cases o with
    | none => exact ⟨hxs.1.1, fun j _ => hxs.1.2 j (Finset.mem_univ _)⟩
    | some j =>
      refine ⟨(hxi (s j)).1.1, fun j' hj' => (hxi (s j)).1.2 j' ?_⟩
      refine Finset.mem_erase.2 ⟨fun h => hj' ⟨j, ho, h.symm⟩, Finset.mem_univ _⟩
  have hfS : ∀ K, none ∉ K → f '' K ⊆ S := by
    rintro K hK _ ⟨o, ho, rfl⟩
    cases o with
    | none => exact absurd ho hK
    | some j => exact hlexlt _ (hsS j)
  have hzG1 : z ∈ G (Q I) := convexHull_min (hfG I) (hGconv _) hz1
  have hzG2 : z ∈ G (Q Iᶜ) := convexHull_min (hfG Iᶜ) (hGconv _) hz2
  have hzF : z ∈ feasibleOn X Xδ ω Finset.univ := by
    refine ⟨hzG1.1, fun i _ => ?_⟩
    by_cases h1 : i ∈ Q I
    · by_cases h2 : i ∈ Q Iᶜ
      · obtain ⟨j, hj, rfl⟩ := h1
        obtain ⟨j', hj', hjj⟩ := h2
        have : j' = j := s.injective hjj
        subst this
        exact absurd hj hj'
      · exact hzG2.2 i h2
    · exact hzG1.2 i h1
  have hzS : z ∈ S := by
    by_cases hn : none ∈ I
    · exact convexHull_min (hfS Iᶜ (fun h => h hn)) hSconv hz2
    · exact convexHull_min (hfS I hn) hSconv hz1
  exact absurd (hxs.2 z hzF) (not_le.2 hzS)
