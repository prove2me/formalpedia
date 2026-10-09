-- Prove2me | solution 1 for ProjSchedTW.ActiveSchedules.minimal_point_characterization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T14:06:55.556122+00:00
-- url     : https://prove2.me/submissions/3b28753d-22dd-41b8-a802-cd4ea0506251

import Mathlib
import Definitions.Def_ProjSchedTW_ActiveSchedules_Project
import Definitions.Def_ProjSchedTW_ActiveSchedules_Shifts

set_option autoImplicit false

namespace MPC8a11

open ProjSchedTW.ActiveSchedules Topology Filter

lemma mem_activeSet' {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ) (t : ℝ)
    (i : Fin (n + 2)) : i ∈ activeSet P S t ↔ S i ≤ t ∧ t < S i + (P.p i : ℝ) := by
  unfold activeSet
  simp

/-- Helly-type argument with the clean order (only pairs of positive-duration activities). -/
lemma feasible_of_clean_order {n : ℕ} {K : Type} (P : Project n K)
    (S x : Fin (n + 2) → ℝ) (hS : S ∈ feasibleSet P) (hx : x ∈ timeFeasibleSet P)
    (hO : ∀ e ∈ scheduleOrder P S, 0 < P.p e.1 → 0 < P.p e.2 →
      x e.1 + (P.p e.1 : ℝ) ≤ x e.2) : x ∈ feasibleSet P := by
  classical
  refine ⟨hx, hx.1, hx.2.1, ?_⟩
  intro k t _ht
  by_cases hA : (activeSet P x t).Nonempty
  · obtain ⟨m, hmA, hmax⟩ := (activeSet P x t).exists_max_image S hA
    have hsub : activeSet P x t ⊆ activeSet P S (S m) := by
      intro i hi
      rw [mem_activeSet'] at hi ⊢
      refine ⟨hmax i ((mem_activeSet' P x t i).2 hi), ?_⟩
      by_cases him : i = m
      · subst him
        have : (0 : ℝ) < (P.p i : ℝ) := by linarith [hi.1, hi.2]
        linarith
      · by_contra hcon
        replace hcon := not_lt.mp hcon
        have hmem : (i, m) ∈ scheduleOrder P S := ⟨him, hcon⟩
        rw [mem_activeSet'] at hmA
        have hpi : 0 < P.p i := by
          have : (0 : ℝ) < (P.p i : ℝ) := by linarith [hi.1, hi.2]
          exact_mod_cast this
        have hpm : 0 < P.p m := by
          have : (0 : ℝ) < (P.p m : ℝ) := by linarith [hmA.1, hmA.2]
          exact_mod_cast this
        have hx2 := hO (i, m) hmem hpi hpm
        simp only at hx2
        linarith [hmA.1, hi.2]
    calc usage P x k t = ∑ i ∈ activeSet P x t, P.r i k := rfl
      _ ≤ ∑ i ∈ activeSet P S (S m), P.r i k := Finset.sum_le_sum_of_subset hsub
      _ ≤ P.R k := hS.2.2.2 k (S m) (hS.2.2.1 m)
  · rw [Finset.not_nonempty_iff_eq_empty] at hA
    have : usage P x k t = 0 := by
      unfold usage; rw [hA]; simp
    rw [this]; exact Nat.zero_le _

lemma feasible_of_order_sub {n : ℕ} {K : Type} (P : Project n K)
    (S x : Fin (n + 2) → ℝ) (hS : S ∈ feasibleSet P) (hx : x ∈ timeFeasibleSet P)
    (hO : scheduleOrder P S ⊆ scheduleOrder P x) : x ∈ feasibleSet P :=
  feasible_of_clean_order P S x hS hx (fun _ he _ _ => (hO he).2)

lemma seg_time {n : ℕ} {K : Type} (P : Project n K) (S S' : Fin (n + 2) → ℝ)
    (hS : S ∈ timeFeasibleSet P) (hS' : S' ∈ timeFeasibleSet P) (τ : ℝ) (h0 : 0 ≤ τ)
    (h1 : τ ≤ 1) : (fun i => (1 - τ) * S i + τ * S' i) ∈ timeFeasibleSet P := by
  refine ⟨?_, ?_, ?_⟩
  · simp [hS.1, hS'.1]
  · intro i
    have := hS.2.1 i; have := hS'.2.1 i
    have : 0 ≤ 1 - τ := by linarith
    positivity
  · intro e he
    have a := hS.2.2 e he
    have b := hS'.2.2 e he
    have c : 0 ≤ 1 - τ := by linarith
    have := mul_le_mul_of_nonneg_left a c
    have := mul_le_mul_of_nonneg_left b h0
    simp only
    nlinarith

lemma seg_poly {n : ℕ} {K : Type} (P : Project n K) (O : Set (Fin (n + 2) × Fin (n + 2)))
    (S S' : Fin (n + 2) → ℝ) (hS : S ∈ orderPolyhedron P O) (hS' : S' ∈ orderPolyhedron P O)
    (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    (fun i => (1 - τ) * S i + τ * S' i) ∈ orderPolyhedron P O := by
  refine ⟨seg_time P S S' hS.1 hS'.1 τ h0 h1, fun e he => ?_⟩
  have a := hS.2 e he
  have b := hS'.2 e he
  have c : 0 ≤ 1 - τ := by linarith
  have := mul_le_mul_of_nonneg_left a c
  have := mul_le_mul_of_nonneg_left b h0
  simp only
  nlinarith

lemma seg_order {n : ℕ} {K : Type} (P : Project n K) (S S' T : Fin (n + 2) → ℝ)
    (hT : scheduleOrder P T ⊆ scheduleOrder P S ∧ scheduleOrder P T ⊆ scheduleOrder P S')
    (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    scheduleOrder P T ⊆ scheduleOrder P (fun i => (1 - τ) * S i + τ * S' i) := by
  intro e he
  have a := (hT.1 he).2
  have b := (hT.2 he).2
  refine ⟨he.1, ?_⟩
  have c : 0 ≤ 1 - τ := by linarith
  have := mul_le_mul_of_nonneg_left a c
  have := mul_le_mul_of_nonneg_left b h0
  simp only
  nlinarith

/-- The clean order `{(i,j) ∈ O(S) | p_i > 0, p_j > 0}`. -/
def cleanOrder {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ) :
    Set (Fin (n + 2) × Fin (n + 2)) :=
  {e | e ∈ scheduleOrder P S ∧ 0 < P.p e.1 ∧ 0 < P.p e.2}

lemma clean_feasible {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ)
    (hS : S ∈ feasibleSet P) : IsFeasibleOrder P (cleanOrder P S) := by
  refine ⟨⟨?_, ?_⟩, ⟨S, hS.1, fun e he => he.1.2⟩, ?_⟩
  · intro i j h1 h2
    have a : S i + (P.p i : ℝ) ≤ S j := h1.1.2
    have b : S j + (P.p j : ℝ) ≤ S i := h2.1.2
    have : (0 : ℝ) < (P.p i : ℝ) := by exact_mod_cast h1.2.1
    have : (0 : ℝ) ≤ (P.p j : ℝ) := by positivity
    linarith
  · intro i j l h1 h2
    have a : S i + (P.p i : ℝ) ≤ S j := h1.1.2
    have b : S j + (P.p j : ℝ) ≤ S l := h2.1.2
    have hpi : (0 : ℝ) < (P.p i : ℝ) := by exact_mod_cast h1.2.1
    have hpj : (0 : ℝ) < (P.p j : ℝ) := by exact_mod_cast h1.2.2
    refine ⟨⟨?_, ?_⟩, h1.2.1, h2.2.2⟩
    · intro hil
      simp only at hil
      subst hil
      linarith
    · show S i + (P.p i : ℝ) ≤ S l
      linarith
  · rintro x ⟨hx, hxO⟩
    exact feasible_of_clean_order P S x hS hx (fun e he h1 h2 => hxO e ⟨he, h1, h2⟩)

lemma eventually_order_sub {n : ℕ} {K : Type} (P : Project n K) {X : Type} [TopologicalSpace X]
    (f : X → (Fin (n + 2) → ℝ)) (hf : Continuous f) (a : X) :
    ∀ᶠ x in 𝓝 a, scheduleOrder P (f x) ⊆ scheduleOrder P (f a) := by
  have key : ∀ e : Fin (n + 2) × Fin (n + 2),
      ∀ᶠ x in 𝓝 a, e ∈ scheduleOrder P (f x) → e ∈ scheduleOrder P (f a) := by
    intro e
    by_cases he : e ∈ scheduleOrder P (f a)
    · exact Filter.Eventually.of_forall (fun _ _ => he)
    · by_cases hne : e.1 = e.2
      · exact Filter.Eventually.of_forall (fun x hx => absurd hne hx.1)
      · have hlt : (0 : ℝ) < f a e.1 + (P.p e.1 : ℝ) - f a e.2 := by
          by_contra h
          exact he ⟨hne, by linarith⟩
        have hc : Continuous (fun x => f x e.1 + (P.p e.1 : ℝ) - f x e.2) := by fun_prop
        have hev := (hc.tendsto a).eventually (lt_mem_nhds hlt)
        filter_upwards [hev] with x hx hxe
        have := hxe.2
        exact absurd this (by linarith)
  filter_upwards [Filter.eventually_all.2 key] with x hx e he using hx e he

lemma joined_local {n : ℕ} {K : Type} (P : Project n K) (y : feasibleSet P) :
    ∀ᶠ z in 𝓝 y, Joined y z := by
  have h := eventually_order_sub P (fun T => T) continuous_id (y : Fin (n + 2) → ℝ)
  have h2 := (continuous_subtype_val.tendsto y).eventually h
  filter_upwards [h2] with z hz
  have hmem : ∀ τ : unitInterval,
      (fun i => (1 - (τ : ℝ)) * (y : Fin (n + 2) → ℝ) i + (τ : ℝ) * (z : Fin (n + 2) → ℝ) i)
        ∈ feasibleSet P := fun τ =>
    feasible_of_order_sub P z.1 _ z.2 (seg_time P y z y.2.1 z.2.1 τ τ.2.1 τ.2.2)
      (seg_order P y z z ⟨hz, subset_rfl⟩ τ τ.2.1 τ.2.2)
  exact ⟨{ toFun := fun τ => ⟨_, hmem τ⟩
           continuous_toFun := Continuous.subtype_mk (by fun_prop) _
           source' := by apply Subtype.ext; funext i; simp
           target' := by apply Subtype.ext; funext i; simp }⟩

lemma path_of_mem_component {n : ℕ} {K : Type} (P : Project n K) (S T : Fin (n + 2) → ℝ)
    (hS : S ∈ feasibleSet P) (hT : T ∈ connectedComponentIn (feasibleSet P) S) :
    ∃ x : unitInterval → (Fin (n + 2) → ℝ), Continuous x ∧ x 0 = S ∧ x 1 = T ∧
      ∀ τ, x τ ∈ feasibleSet P := by
  rw [connectedComponentIn_eq_image hS] at hT
  obtain ⟨t, ht, rfl⟩ := hT
  have hclopen : IsClopen (pathComponent (⟨S, hS⟩ : feasibleSet P)) := by
    constructor
    · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro y hy
      filter_upwards [joined_local P y] with z hz hzc
      exact hy (hzc.trans hz.symm)
    · rw [isOpen_iff_mem_nhds]
      intro y hy
      filter_upwards [joined_local P y] with z hz
      exact hy.trans hz
  have hpc := hclopen.connectedComponent_subset (mem_pathComponent_self _) ht
  obtain ⟨γ⟩ := hpc
  exact ⟨fun τ => (γ τ : Fin (n + 2) → ℝ), continuous_subtype_val.comp γ.continuous,
    by simp, by simp, fun τ => (γ τ).2⟩

lemma part_a {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ)
    (hS : S ∈ feasibleSet P) : IsActive P S ↔ Minimal (· ∈ feasibleSet P) S := by
  constructor
  · rintro ⟨-, h⟩
    refine ⟨hS, fun y hy hyS => ?_⟩
    by_contra hne
    have hne' : y ≠ S := fun h => hne (h ▸ le_refl _)
    exact h ⟨y, ⟨hS, hy, hne'⟩, hyS, hne'⟩
  · intro hm
    refine ⟨hS, ?_⟩
    rintro ⟨y, ⟨-, hy, hne⟩, hyS, -⟩
    exact hne (le_antisymm hyS (hm.2 hy hyS))

lemma part_d {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ)
    (hS : S ∈ feasibleSet P) :
    IsQuasiactive P S ↔ Minimal (· ∈ orderPolyhedron P (scheduleOrder P S)) S := by
  have hSmem : S ∈ orderPolyhedron P (scheduleOrder P S) := ⟨hS.1, fun e he => he.2⟩
  constructor
  · rintro ⟨-, h⟩
    refine ⟨hSmem, fun y hy hyS => ?_⟩
    by_contra hne
    have hne' : y ≠ S := fun h => hne (h ▸ le_refl _)
    have hy' : y ∈ orderPolyhedron P (scheduleOrder P S) := hy
    have hsub : scheduleOrder P S ⊆ scheduleOrder P y := fun e he => ⟨he.1, hy'.2 e he⟩
    have hyF := feasible_of_order_sub P S y hS hy'.1 hsub
    exact h ⟨y, ⟨⟨hS, hyF, hne'⟩, hsub⟩, hyS, hne'⟩
  · intro hm
    refine ⟨hS, ?_⟩
    rintro ⟨y, ⟨⟨-, hy, hne⟩, hsub⟩, hyS, -⟩
    have hyP : y ∈ orderPolyhedron P (scheduleOrder P S) := ⟨hy.1, fun e he => (hsub he).2⟩
    exact hne (le_antisymm hyS (hm.2 hyP hyS))

lemma part_c {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ)
    (hS : S ∈ feasibleSet P) :
    IsPseudoactive P S ↔ ∀ O : Set (Fin (n + 2) × Fin (n + 2)), IsFeasibleOrder P O →
      O ⊆ scheduleOrder P S → Minimal (· ∈ orderPolyhedron P O) S := by
  constructor
  · rintro ⟨-, h⟩ O hO hOS
    have hSO : S ∈ orderPolyhedron P O := ⟨hS.1, fun e he => (hOS he).2⟩
    refine ⟨hSO, fun y hy hyS => ?_⟩
    by_contra hne
    have hne' : y ≠ S := fun h => hne (h ▸ le_refl _)
    have hy' : y ∈ orderPolyhedron P O := hy
    let f : ℝ → (Fin (n + 2) → ℝ) := fun t i => (1 - t) * S i + t * y i
    have hf : Continuous f := by fun_prop
    have hf0 : f 0 = S := by funext i; simp [f]
    have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), scheduleOrder P (f t) ⊆ scheduleOrder P (f 0) :=
      nhdsWithin_le_nhds (eventually_order_sub P f hf 0)
    have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
    obtain ⟨t, ht, ht0, ht1⟩ := (h1.and h2).exists
    rw [hf0] at ht
    have hft : f t ∈ orderPolyhedron P O := seg_poly P O S y hSO hy' t ht0.le ht1.le
    have hftF := hO.2.2 hft
    have hle : f t ≤ S := fun i => by
      have := hyS i
      simp only [f]
      nlinarith
    have hneq : f t ≠ S := by
      intro heq
      apply hne'
      funext i
      have := congrFun heq i
      simp only [f] at this
      have h3 : t * (y i - S i) = 0 := by linarith
      rcases mul_eq_zero.1 h3 with h4 | h4
      · linarith
      · linarith
    exact h ⟨f t, ⟨⟨hS, hftF, hneq⟩, Or.inr ht⟩, hle, hneq⟩
  · intro hm
    refine ⟨hS, ?_⟩
    rintro ⟨y, ⟨⟨-, hy, hne⟩, hmono⟩, hyS, -⟩
    rcases hmono with hsub | hsub
    · have hO := clean_feasible P S hS
      have hyP : y ∈ orderPolyhedron P (cleanOrder P S) := ⟨hy.1, fun e he => (hsub he.1).2⟩
      exact hne (le_antisymm hyS ((hm _ hO (fun e he => he.1)).2 hyP hyS))
    · have hO := clean_feasible P y hy
      have hyP : y ∈ orderPolyhedron P (cleanOrder P y) := ⟨hy.1, fun e he => he.1.2⟩
      exact hne (le_antisymm hyS ((hm _ hO (fun e he => hsub he.1)).2 hyP hyS))

lemma part_b {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ)
    (hS : S ∈ feasibleSet P) :
    IsSemiactive P S ↔
      ∃ x ∈ feasibleSet P, Minimal (· ∈ connectedComponentIn (feasibleSet P) x) S := by
  constructor
  · rintro ⟨-, h⟩
    refine ⟨S, hS, mem_connectedComponentIn hS, fun y hy hyS => ?_⟩
    by_contra hne
    have hne' : y ≠ S := fun h => hne (h ▸ le_refl _)
    have hy' : y ∈ connectedComponentIn (feasibleSet P) S := hy
    obtain ⟨x, hx, hx0, hx1, hxF⟩ := path_of_mem_component P S y hS hy'
    have hyF : y ∈ feasibleSet P := connectedComponentIn_subset _ _ hy'
    exact h ⟨y, ⟨⟨hS, hyF, hne'⟩, x, hx, hx0, hx1, hxF⟩, hyS, hne'⟩
  · rintro ⟨x, -, hm⟩
    refine ⟨hS, ?_⟩
    rintro ⟨y, ⟨⟨-, -, hne⟩, γ, hγ, hγ0, hγ1, hγF⟩, hyS, -⟩
    have hconn : IsPreconnected (Set.range γ) := isPreconnected_range hγ
    have hsub : Set.range γ ⊆ connectedComponentIn (feasibleSet P) S :=
      hconn.subset_connectedComponentIn ⟨0, hγ0⟩ (by rintro _ ⟨τ, rfl⟩; exact hγF τ)
    have hyc : y ∈ connectedComponentIn (feasibleSet P) S := hsub ⟨1, hγ1⟩
    have hSx : connectedComponentIn (feasibleSet P) x = connectedComponentIn (feasibleSet P) S :=
      connectedComponentIn_eq hm.1
    rw [← hSx] at hyc
    exact hne (le_antisymm hyS (hm.2 hyc hyS))

end MPC8a11

open MPC8a11 in
open ProjSchedTW.ActiveSchedules in
theorem solution {n : ℕ} {K : Type} (P : Project n K)
    (S : Fin (n + 2) → ℝ) (hS : S ∈ feasibleSet P) :
    (IsActive P S ↔ Minimal (· ∈ feasibleSet P) S) ∧
      (IsSemiactive P S ↔
        ∃ x ∈ feasibleSet P, Minimal (· ∈ connectedComponentIn (feasibleSet P) x) S) ∧
      (IsPseudoactive P S ↔
        ∀ O : Set (Fin (n + 2) × Fin (n + 2)), IsFeasibleOrder P O → O ⊆ scheduleOrder P S →
          Minimal (· ∈ orderPolyhedron P O) S) ∧
      (IsQuasiactive P S ↔ Minimal (· ∈ orderPolyhedron P (scheduleOrder P S)) S) := by
  exact ⟨part_a P S hS, part_b P S hS, part_c P S hS, part_d P S hS⟩
