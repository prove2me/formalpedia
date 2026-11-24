-- Prove2me | solution 1 for SunMinCut.Cactus.partition_strength_bounds
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T16:50:45.646462+00:00
-- url     : https://prove2.me/submissions/421f3679-ad37-497a-a26e-79d24f3414a1

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Graph

open CombOpt.MinCut

namespace SunMinCut.Cactus.PSB

open SunMinCut.Cactus

variable {n m : ℕ}

lemma lam_spec (hn : 2 ≤ n) (G : SunMinCut.Cactus.Graph n m) :
    ∃ S0, Nontriv S0 ∧ lam G = cutw G S0 ∧ ∀ S, Nontriv S → lam G ≤ cutw G S := by
  obtain ⟨F, hF, hgF⟩ : ∃ F : Finset (Finset (Fin n)), (∀ S, S ∈ F ↔ Nontriv S) ∧
      G.globalMinCut = F.inf (fun S => ((cutw G S : ℝ) : WithTop ℝ)) :=
    ⟨_, fun S => by simp [Nontriv], rfl⟩
  have hne : F.Nonempty := by
    refine ⟨{⟨0, by omega⟩}, (hF _).mpr ⟨by simp, ?_⟩⟩
    intro h
    have : (⟨1, by omega⟩ : Fin n) ∈ ({⟨0, by omega⟩} : Finset (Fin n)) := h ▸ Finset.mem_univ _
    simp at this
  obtain ⟨S0, hS0, heq⟩ := Finset.exists_mem_eq_inf _ hne
    (fun S => ((cutw G S : ℝ) : WithTop ℝ))
  have hg : G.globalMinCut = ((cutw G S0 : ℝ) : WithTop ℝ) := hgF.trans heq
  have hlam : lam G = cutw G S0 := by
    unfold lam; rw [hg]; rfl
  refine ⟨S0, (hF _).mp hS0, hlam, ?_⟩
  intro S hS
  have hle : G.globalMinCut ≤ ((cutw G S : ℝ) : WithTop ℝ) := by
    rw [hgF]
    exact Finset.inf_le (f := fun S => ((cutw G S : ℝ) : WithTop ℝ)) ((hF S).mpr hS)
  rw [hg] at hle
  rw [hlam]
  exact WithTop.coe_le_coe.mp hle

lemma ends_rep (G : SunMinCut.Cactus.Graph n m) (e : Fin m) : ∃ a b, G.ends e = s(a, b) := by
  induction G.ends e using Sym2.ind with
  | h a b => exact ⟨a, b, rfl⟩

lemma crosses_iff (G : SunMinCut.Cactus.Graph n m) (P : Partition n) (e : Fin m) (a b : Fin n)
    (hab : G.ends e = s(a, b)) : CrossesPart G P e ↔ P.part a ≠ P.part b := by
  unfold CrossesPart
  rw [hab]
  simp only [Sym2.mem_iff]
  constructor
  · rintro ⟨x, hx, y, hy, hne⟩
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hne
    · exact hne
    · exact fun h => hne h.symm
    · exact absurd rfl hne
  · intro h
    exact ⟨a, Or.inl rfl, b, Or.inr rfl, h⟩

lemma delta_iff (G : SunMinCut.Cactus.Graph n m) (B : Finset (Fin n)) (e : Fin m) (a b : Fin n)
    (hab : G.ends e = s(a, b)) :
    e ∈ G.delta B ↔ (a ∈ B ∨ b ∈ B) ∧ (a ∉ B ∨ b ∉ B) := by
  simp only [CapGraph.delta, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hab]
  simp only [Sym2.mem_iff]
  constructor
  · rintro ⟨⟨x, hx, hxB⟩, ⟨y, hy, hyB⟩⟩
    constructor
    · rcases hx with rfl | rfl
      · exact Or.inl hxB
      · exact Or.inr hxB
    · rcases hy with rfl | rfl
      · exact Or.inl hyB
      · exact Or.inr hyB
  · rintro ⟨h1, h2⟩
    constructor
    · rcases h1 with h | h
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨b, Or.inr rfl, h⟩
    · rcases h2 with h | h
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨b, Or.inr rfl, h⟩

lemma sum_cut_eq (G : SunMinCut.Cactus.Graph n m) (P : Partition n) :
    ∑ B ∈ P.parts, cutw G B = 2 * partCut G P := by
  classical
  unfold cutw CapGraph.uSum partCut
  have h1 : ∀ B ∈ P.parts, ∑ e ∈ G.delta B, G.u e =
      ∑ e, if e ∈ G.delta B then G.u e else 0 := by
    intro B _
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext e; simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  obtain ⟨a, b, hab⟩ := ends_rep G e
  have hpa : P.part a ∈ P.parts := P.part_mem.mpr (Finset.mem_univ a)
  have hpb : P.part b ∈ P.parts := P.part_mem.mpr (Finset.mem_univ b)
  have key : ∀ B ∈ P.parts, (if e ∈ G.delta B then G.u e else 0) =
      if P.part a = P.part b then 0 else
        ((if P.part a = B then G.u e else 0) + (if P.part b = B then G.u e else 0)) := by
    intro B hB
    have ha : a ∈ B ↔ P.part a = B := (P.part_eq_iff_mem hB).symm
    have hb : b ∈ B ↔ P.part b = B := (P.part_eq_iff_mem hB).symm
    simp only [delta_iff G B e a b hab, ha, hb]
    by_cases h : P.part a = P.part b
    · rw [if_pos h, h]; simp
    · rw [if_neg h]
      by_cases h1 : P.part a = B <;> by_cases h2 : P.part b = B
      · exact absurd (h1.trans h2.symm) h
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl key, crosses_iff G P e a b hab]
  by_cases h : P.part a = P.part b
  · simp [h]
  · simp only [if_neg h, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hpa, if_pos hpb,
      not_false_eq_true, if_true]
    rw [if_pos (show P.part a ≠ P.part b from h)]
    ring

lemma lower (hn : 2 ≤ n) (G : SunMinCut.Cactus.Graph n m) (hpos : Positive G) (P : Partition n)
    (hP : 2 ≤ P.parts.card) : lam G / 2 ≤ partCut G P / ((P.parts.card : ℝ) - 1) := by
  obtain ⟨S0, -, hlam, hmin⟩ := lam_spec hn G
  have hlam0 : 0 ≤ lam G := by
    rw [hlam]; unfold cutw CapGraph.uSum
    exact Finset.sum_nonneg (fun e _ => (hpos e).le)
  have hB : ∀ B ∈ P.parts, lam G ≤ cutw G B := by
    intro B hBm
    apply hmin
    refine ⟨P.nonempty_of_mem_parts hBm, ?_⟩
    intro hu
    obtain ⟨C, hC, hCB⟩ := Finset.exists_mem_ne (by omega : 1 < P.parts.card) B
    obtain ⟨c, hc⟩ := P.nonempty_of_mem_parts hC
    exact hCB (P.eq_of_mem_parts hC hBm hc (hu ▸ Finset.mem_univ c))
  have hsum := Finset.sum_le_sum hB
  rw [sum_cut_eq, Finset.sum_const, nsmul_eq_mul] at hsum
  have hk : (2 : ℝ) ≤ P.parts.card := by exact_mod_cast hP
  rw [div_le_div_iff₀ (by norm_num) (by linarith)]
  nlinarith

def twoPart (S : Finset (Fin n)) (h : Nontriv S) : Partition n where
  parts := {S, Finset.univ \ S}
  supIndep := by
    obtain ⟨x, hx⟩ := h.1
    have hne : S ≠ Finset.univ \ S := by
      intro e; have := e ▸ hx; simp [hx] at this
    exact (Finset.supIndep_pair hne).mpr disjoint_sdiff_self_right
  sup_parts := by
    simp [Finset.union_sdiff_of_subset (Finset.subset_univ S)]
  bot_notMem := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun e => ?_, fun e => ?_⟩
    · obtain ⟨x, hx⟩ := h.1; rw [← e] at hx; simp at hx
    · apply h.2
      have : Finset.univ \ S = ∅ := e.symm
      rw [Finset.sdiff_eq_empty_iff_subset] at this
      exact Finset.eq_univ_of_forall (fun x => this (Finset.mem_univ x))

lemma twoPart_card (S : Finset (Fin n)) (h : Nontriv S) : (twoPart S h).parts.card = 2 := by
  obtain ⟨x, hx⟩ := h.1
  have hne : S ≠ Finset.univ \ S := by
    intro e; have := e ▸ hx; simp [hx] at this
  exact Finset.card_pair hne

lemma twoPart_cut (G : SunMinCut.Cactus.Graph n m) (S : Finset (Fin n)) (h : Nontriv S) :
    partCut G (twoPart S h) = cutw G S := by
  classical
  unfold partCut cutw CapGraph.uSum
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext e
  obtain ⟨a, b, hab⟩ := ends_rep G e
  have hS : S ∈ (twoPart S h).parts := by simp [twoPart]
  have hp : ∀ x, (twoPart S h).part x = S ↔ x ∈ S := fun x => (twoPart S h).part_eq_iff_mem hS
  have hp' : ∀ x, x ∉ S → (twoPart S h).part x = Finset.univ \ S := fun x hx =>
    (twoPart S h).part_eq_of_mem (by simp [twoPart]) (by simp [hx])
  rw [Finset.mem_filter, crosses_iff G _ e a b hab, delta_iff G S e a b hab]
  simp only [Finset.mem_univ, true_and]
  have hSne : S ≠ Finset.univ \ S := by
    obtain ⟨x, hx⟩ := h.1
    intro e; have := e ▸ hx; simp [hx] at this
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · rw [(hp a).mpr ha, (hp b).mpr hb]; simp [ha, hb]
  · rw [(hp a).mpr ha, hp' b hb]; simp [ha, hb, hSne]
  · rw [hp' a ha, (hp b).mpr hb]; simp [ha, hb, hSne.symm]
  · rw [hp' a ha, hp' b hb]; simp [ha, hb]

end SunMinCut.Cactus.PSB

open SunMinCut.Cactus SunMinCut.Cactus.PSB

theorem solution (n m : ℕ) (hn : 2 ≤ n) (G : SunMinCut.Cactus.Graph n m) (hpos : Positive G)
    (hconn : Connected G) :
    lam G / 2 ≤ sigma G ∧ sigma G ≤ lam G := by
  obtain ⟨S0, hS0, hlam, -⟩ := lam_spec hn G
  have hmem : lam G ∈ {x | ∃ P : Partition n, 2 ≤ P.parts.card ∧
      x = partCut G P / ((P.parts.card : ℝ) - 1)} := by
    refine ⟨twoPart S0 hS0, by rw [twoPart_card], ?_⟩
    rw [twoPart_card, twoPart_cut, hlam]; norm_num
  have hlow : ∀ x ∈ {x | ∃ P : Partition n, 2 ≤ P.parts.card ∧
      x = partCut G P / ((P.parts.card : ℝ) - 1)}, lam G / 2 ≤ x := by
    rintro x ⟨P, hP, rfl⟩
    exact lower hn G hpos P hP
  exact ⟨le_csInf ⟨_, hmem⟩ hlow, csInf_le ⟨_, hlow⟩ hmem⟩
