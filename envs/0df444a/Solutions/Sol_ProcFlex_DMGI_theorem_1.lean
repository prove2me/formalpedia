-- Prove2me | solution 1 for ProcFlex.DMGI.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T21:10:23.137409+00:00
-- url     : https://prove2.me/submissions/1422872d-8800-481d-b917-e5616821f0eb

import Mathlib
import Definitions.Def_ProcFlex_DMGI_Model
import Theorems.Thm_ProcFlex_DMGI_proposition_3

open ProcFlex.DMGI Finset

theorem solution {m n T : ℕ} (S : System m n T) (hS : S.IsValid)
    (A : Design m n) (h : ℝ → (Fin T → ℝ) → ℝ)
    (hh : ∀ y, StrictMono (fun x => h x y))
    (hcont : ContinuousOn (f S h A) {d | ∀ i, 0 ≤ d i})
    (U : Set (Fin n → ℝ)) (μ : Fin n → ℝ)
    (hU : IsSymmetricAround S U μ)
    (hUpos : ∀ d ∈ U, ∀ i, 0 ≤ d i)
    (hUne : U.Nonempty) (hUc : IsCompact U) :
    IsLeast {v : ℝ | ∃ (K : Fin T → Fin (T + 1) → ℕ), InQ S K ∧
      ∃ ε ∈ ((fun d => d - μ) '' U),
        v = h (dmgi S μ K A + blockSum S K ε)
          (catSum S (μ + ε))}
      (Rf S h A U) := by
  have hcontU : ContinuousOn (f S h A) U := hcont.mono (fun d hd => hUpos d hd)
  set Us : (Fin T → ℝ) → Set (Fin n → ℝ) := fun s => {d | d ∈ U ∧ catSum S d = s} with hUs
  have hcs : Continuous (fun d : Fin n → ℝ => catSum S d) := by
    unfold catSum
    exact continuous_pi (fun t => continuous_finset_sum _ (fun i _ => continuous_apply i))
  have hUsc : ∀ s, IsCompact (Us s) := fun s =>
    hUc.inter_right (isClosed_eq hcs continuous_const)
  have hsum_perm : ∀ (e : Fin n → ℝ) (σ : Equiv.Perm (Fin n)),
      (∀ i, S.cat (σ i) = S.cat i) → ∀ t, ∑ i ∈ S.s t, e (σ i) = ∑ i ∈ S.s t, e i := by
    intro e σ hσ t
    unfold System.s
    rw [sum_filter, sum_filter]
    rw [← Equiv.sum_comp σ (fun j => if S.cat j = t then e j else 0)]
    apply sum_congr rfl; intro i _; rw [hσ i]
  have hUsym : ∀ s, IsSymmetricAround S (Us s) μ := by
    intro s
    obtain ⟨h1, h2⟩ := hU
    constructor
    · intro x hx
      have hxE : x ∈ (fun d => d - μ) '' U := h1 x (fun t => by
        obtain ⟨e, he, hei⟩ := hx t
        obtain ⟨d, hd, rfl⟩ := he
        exact ⟨d - μ, ⟨d, hd.1, rfl⟩, hei⟩)
      obtain ⟨d, hdU, hdx⟩ := hxE
      refine ⟨d, ⟨hdU, ?_⟩, hdx⟩
      funext t
      obtain ⟨e, he, hei⟩ := hx t
      obtain ⟨d', hd', rfl⟩ := he
      rw [← hd'.2]
      unfold catSum
      apply sum_congr rfl
      intro i hi
      have hci : S.cat i = t := by simpa [System.s] using hi
      have h3 := hei i hci
      have h4 := congrFun hdx i
      simp at h3 h4
      linarith
    · intro e he σ hσ
      obtain ⟨d, hd, rfl⟩ := he
      obtain ⟨d', hd', hd'e⟩ := h2 (d - μ) ⟨d, hd.1, rfl⟩ σ hσ
      refine ⟨d', ⟨hd', ?_⟩, hd'e⟩
      funext t
      rw [← hd.2]
      unfold catSum
      have hd'eq : ∀ i, d' i = μ i + (d (σ i) - μ (σ i)) := by
        intro i; have := congrFun hd'e i; simp at this; linarith
      simp only [hd'eq, sum_add_distrib]
      rw [hsum_perm (fun i => d i - μ i) σ hσ t]
      simp [sum_sub_distrib]
  have hslice : ∀ s, (Us s).Nonempty → ∃ d' ∈ Us s,
      Rf S (fun x _ => x) A (Us s) = g S A d' ∧ ∀ d ∈ Us s, g S A d' ≤ g S A d := by
    intro s hne
    obtain ⟨d', hd', hmin⟩ := (hUsc s).exists_isMinOn hne (hcontU.mono (fun d hd => hd.1))
    have hg : ∀ d ∈ Us s, g S A d' ≤ g S A d := by
      intro d hd
      by_contra hlt
      push Not at hlt
      have h1 : f S h A d < f S h A d' := by
        simp only [f, hd.2, hd'.2]; exact hh s hlt
      have h2 : f S h A d' ≤ f S h A d := hmin hd
      linarith
    refine ⟨d', hd', ?_, hg⟩
    unfold Rf
    exact IsLeast.csInf_eq ⟨⟨d', hd', rfl⟩, by rintro _ ⟨d, hd, rfl⟩; exact hg d hd⟩
  have hbdd : BddBelow (f S h A '' U) := hUc.bddBelow_image hcontU
  have hlow : ∀ v ∈ {v : ℝ | ∃ (K : Fin T → Fin (T + 1) → ℕ), InQ S K ∧
      ∃ ε ∈ ((fun d => d - μ) '' U),
        v = h (dmgi S μ K A + blockSum S K ε) (catSum S (μ + ε))}, Rf S h A U ≤ v := by
    rintro v ⟨K, hK, ε, ⟨d0, hd0, rfl⟩, rfl⟩
    have he0 : μ + (d0 - μ) = d0 := by abel
    rw [he0]
    have hd0s : d0 ∈ Us (catSum S d0) := ⟨hd0, rfl⟩
    obtain ⟨d', hd', hRg, _⟩ := hslice (catSum S d0) ⟨d0, hd0s⟩
    have hP3 := proposition_3 S hS A (Us (catSum S d0)) μ (hUsym _)
      (fun d hd => hUpos d hd.1) ⟨d0, hd0s⟩ (hUsc _)
    have hle : g S A d' ≤ dmgi S μ K A + blockSum S K (d0 - μ) := by
      rw [← hRg]; exact hP3.2 ⟨K, hK, d0 - μ, ⟨d0, hd0s, rfl⟩, rfl⟩
    calc Rf S h A U ≤ f S h A d' := csInf_le hbdd ⟨d', hd'.1, rfl⟩
      _ = h (g S A d') (catSum S d0) := by simp only [f, hd'.2]
      _ ≤ _ := (hh _).monotone hle
  refine ⟨?_, hlow⟩
  obtain ⟨dstar, hdstar, hdmin⟩ := hUc.exists_isMinOn hUne hcontU
  have hRf : Rf S h A U = f S h A dstar :=
    IsLeast.csInf_eq ⟨⟨dstar, hdstar, rfl⟩, by rintro _ ⟨d, hd, rfl⟩; exact hdmin hd⟩
  have hds : dstar ∈ Us (catSum S dstar) := ⟨hdstar, rfl⟩
  obtain ⟨d', hd', hRg, hg'⟩ := hslice (catSum S dstar) ⟨dstar, hds⟩
  have hP3 := proposition_3 S hS A (Us (catSum S dstar)) μ (hUsym _)
    (fun d hd => hUpos d hd.1) ⟨dstar, hds⟩ (hUsc _)
  obtain ⟨K, hK, ε, ⟨d0, hd0, rfl⟩, hval⟩ := hP3.1
  have he0 : μ + (d0 - μ) = d0 := by abel
  have hv1 : h (dmgi S μ K A + blockSum S K (d0 - μ)) (catSum S (μ + (d0 - μ))) ∈
      {v : ℝ | ∃ (K : Fin T → Fin (T + 1) → ℕ), InQ S K ∧
        ∃ ε ∈ ((fun d => d - μ) '' U),
          v = h (dmgi S μ K A + blockSum S K ε) (catSum S (μ + ε))} :=
    ⟨K, hK, d0 - μ, ⟨d0, hd0.1, rfl⟩, rfl⟩
  have hup : h (dmgi S μ K A + blockSum S K (d0 - μ)) (catSum S (μ + (d0 - μ))) ≤
      Rf S h A U := by
    rw [he0, hd0.2, ← hval, hRg, hRf]
    exact (hh _).monotone (hg' dstar hds)
  have heq := le_antisymm (hlow _ hv1) hup
  rw [heq]; exact hv1
