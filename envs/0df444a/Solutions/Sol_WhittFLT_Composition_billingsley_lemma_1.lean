-- Prove2me | solution 1 for WhittFLT.Composition.billingsley_lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T13:20:49.58364+00:00
-- url     : https://prove2.me/submissions/8113db0e-78ec-43fc-9ef5-c35f7f5c1d4a

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD

open WhittFLT.Composition
open Set Filter Topology
open scoped ENNReal

namespace WhittBill1

variable {S : Type*} [MetricSpace S]

noncomputable def osc (x : ℝ → S) (p q : ℝ) : ℝ≥0∞ :=
  ⨆ s₁ ∈ Ico p q, ⨆ s₂ ∈ Ico p q, edist (x s₁) (x s₂)

lemma osc_lt (x : ℝ → S) (p q : ℝ) (z : S) (ε : ℝ) (hε : 0 < ε)
    (h : ∀ s ∈ Ico p q, dist (x s) z < ε / 3) : osc x p q < ENNReal.ofReal ε := by
  have hle : osc x p q ≤ ENNReal.ofReal (2 * (ε / 3)) := by
    unfold osc
    refine iSup₂_le fun s₁ h₁ => iSup₂_le fun s₂ h₂ => ?_
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have := dist_triangle_right (x s₁) (x s₂) z
    linarith [h s₁ h₁, h s₂ h₂]
  refine lt_of_le_of_lt hle ?_
  rw [ENNReal.ofReal_lt_ofReal_iff hε]
  linarith

def Good (x : ℝ → S) (c : ℝ) (ε : ℝ) (t : ℝ) : Prop :=
  ∃ F : Finset ℝ, (↑F : Set ℝ) ⊆ Icc c t ∧ c ∈ F ∧ t ∈ F ∧
    ∀ p ∈ F, ∀ q ∈ F, p < q → (∀ r ∈ F, ¬ (p < r ∧ r < q)) → osc x p q < ENNReal.ofReal ε

lemma good_c (x : ℝ → S) (c ε : ℝ) : Good x c ε c := by
  refine ⟨{c}, by simp, by simp, by simp, ?_⟩
  intro p hp q hq hpq
  simp at hp hq; subst hp; subst hq; exact absurd hpq (lt_irrefl _)

lemma good_ext (x : ℝ → S) (c ε t u : ℝ) (ht : Good x c ε t) (htu : t < u)
    (hosc : osc x t u < ENNReal.ofReal ε) : Good x c ε u := by
  obtain ⟨F, hF, hc, htF, hgood⟩ := ht
  have hct : c ≤ t := (hF htF).1
  refine ⟨insert u F, ?_, Finset.mem_insert_of_mem hc, Finset.mem_insert_self _ _, ?_⟩
  · intro z hz
    simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe] at hz
    rcases hz with rfl | hz
    · exact ⟨by linarith, le_rfl⟩
    · exact ⟨(hF hz).1, (hF hz).2.trans htu.le⟩
  · intro p hp q hq hpq hcons
    have hle : ∀ z ∈ F, z ≤ t := fun z hz => (hF hz).2
    rw [Finset.mem_insert] at hp hq
    rcases hp with rfl | hp
    · rcases hq with rfl | hq
      · exact absurd hpq (lt_irrefl _)
      · exact absurd (lt_of_lt_of_le hpq (hle q hq)) (by linarith)
    · rcases hq with rfl | hq
      · -- p ∈ F, q = u
        have hpt : p = t := by
          rcases (hle p hp).lt_or_eq with h | h
          · exact absurd ⟨h, htu⟩ (hcons t (Finset.mem_insert_of_mem htF))
          · exact h
        subst hpt; exact hosc
      · exact hgood p hp q hq hpq (fun r hr => hcons r (Finset.mem_insert_of_mem hr))

lemma good_d (c d : ℝ) (hcd : c < d) (x : ℝ → S) (hx : IsCadlagOn (Icc c d) x) (ε : ℝ)
    (hε : 0 < ε) : Good x c ε d := by
  set A := {t | t ∈ Icc c d ∧ Good x c ε t} with hA
  have hAne : A.Nonempty := ⟨c, ⟨le_rfl, hcd.le⟩, good_c x c ε⟩
  have hAbdd : BddAbove A := ⟨d, fun t ht => ht.1.2⟩
  set τ := sSup A with hτ
  have hcτ : c ≤ τ := le_csSup hAbdd ⟨⟨le_rfl, hcd.le⟩, good_c x c ε⟩
  have hτd : τ ≤ d := csSup_le hAne fun t ht => ht.1.2
  have hτmem : τ ∈ Icc c d := ⟨hcτ, hτd⟩
  have hε3 : 0 < ε / 3 := by linarith
  -- τ is good
  have hτgood : Good x c ε τ := by
    rcases hcτ.lt_or_eq with hlt | heq
    · obtain ⟨l, hl⟩ := (hx τ hτmem).2
      have hev := (Metric.tendsto_nhds.1 hl) (ε / 3) hε3
      rcases Metric.mem_nhdsWithin_iff.1 hev with ⟨δ, hδ, hsub⟩
      obtain ⟨t, ⟨htmem, htgood⟩, ht⟩ :=
        exists_lt_of_lt_csSup hAne (show max c (τ - δ) < τ from max_lt hlt (by linarith))
      have htτ : t ≤ τ := le_csSup hAbdd ⟨htmem, htgood⟩
      rcases htτ.lt_or_eq with htτ | htτ
      · refine good_ext x c ε t τ htgood htτ ?_
        apply osc_lt x t τ l ε hε
        intro s hs
        have hmem : s ∈ Metric.ball τ δ ∩ (Icc c d ∩ Iio τ) := by
          refine ⟨?_, ⟨?_, ?_⟩, hs.2⟩
          · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
            constructor <;> linarith [hs.1, hs.2, le_max_right c (τ - δ)]
          · linarith [hs.1, le_max_left c (τ - δ)]
          · linarith [hs.2]
        exact hsub hmem
      · rw [← htτ]; exact htgood
    · rw [← heq]; exact good_c x c ε
  -- τ = d
  by_contra hne
  have hτlt : τ < d := lt_of_le_of_ne hτd (fun h => hne (h ▸ hτgood))
  have hev := (Metric.tendsto_nhds.1 (hx τ hτmem).1) (ε / 3) hε3
  rcases Metric.mem_nhdsWithin_iff.1 hev with ⟨δ, hδ, hsub⟩
  set u := min (τ + δ / 2) d with hu
  have hτu : τ < u := lt_min (by linarith) hτlt
  have hud : u ≤ d := min_le_right _ _
  have hugood : Good x c ε u := by
    refine good_ext x c ε τ u hτgood hτu ?_
    apply osc_lt x τ u (x τ) ε hε
    intro s hs
    have hmem : s ∈ Metric.ball τ δ ∩ (Icc c d ∩ Ici τ) := by
      refine ⟨?_, ⟨?_, ?_⟩, hs.1⟩
      · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hs.1, hs.2, min_le_left (τ + δ / 2) d]
      · linarith [hs.1]
      · linarith [hs.2]
    exact hsub hmem
  have : u ≤ τ := le_csSup hAbdd ⟨⟨by linarith, hud⟩, hugood⟩
  linarith

end WhittBill1

open WhittBill1 in
theorem solution {S : Type*} [MetricSpace S] (c d : ℝ) (hcd : c < d)
    (x : ℝ → S) (hx : IsCadlagOn (Icc c d) x) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (t : Fin (n + 1) → ℝ), t 0 = c ∧ t (Fin.last n) = d ∧ StrictMono t ∧
      ∀ j : Fin n, (⨆ s₁ ∈ Ico (t j.castSucc) (t j.succ), ⨆ s₂ ∈ Ico (t j.castSucc) (t j.succ),
        edist (x s₁) (x s₂)) < ENNReal.ofReal ε := by
  obtain ⟨F, hF, hc, hd, hgood⟩ := good_d c d hcd x hx ε hε
  have hcard : 0 < F.card := Finset.card_pos.2 ⟨c, hc⟩
  obtain ⟨n, hn⟩ : ∃ n, F.card = n + 1 := ⟨F.card - 1, by omega⟩
  set e := F.orderEmbOfFin hn with he
  have hmem : ∀ k, e k ∈ F := fun k => Finset.orderEmbOfFin_mem F hn k
  have hsurj : ∀ z ∈ F, ∃ k, e k = z := by
    intro z hz
    have : z ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact hz
    exact this
  refine ⟨n, e, ?_, ?_, e.strictMono, ?_⟩
  · apply le_antisymm
    · obtain ⟨k, hk⟩ := hsurj c hc
      rw [← hk]; exact e.monotone (Fin.zero_le k)
    · exact (hF (hmem 0)).1
  · apply le_antisymm
    · exact (hF (hmem _)).2
    · obtain ⟨k, hk⟩ := hsurj d hd
      rw [← hk]; exact e.monotone (Fin.le_last k)
  · intro j
    have hlt : e j.castSucc < e j.succ := e.strictMono (Fin.castSucc_lt_succ (i := j))
    refine hgood _ (hmem _) _ (hmem _) hlt ?_
    intro r hr ⟨h1, h2⟩
    obtain ⟨k, rfl⟩ := hsurj r hr
    have a1 : j.castSucc < k := e.strictMono.lt_iff_lt.1 h1
    have a2 : k < j.succ := e.strictMono.lt_iff_lt.1 h2
    rw [Fin.lt_def] at a1 a2
    simp at a1 a2
    omega
