-- Prove2me | solution 1 for TemporalAgg.gta_loop_terminates
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-26T12:25:04.972021+00:00
-- url     : https://prove2.me/submissions/b6219ab1-321e-4c21-a402-d860b8e41baa

import Mathlib
import Definitions.Def_TemporalAgg_IsGTARun

open TemporalAgg

namespace P2MHole01_c2cc3af3
/-- For `s` distinct from `t`, `t₁` and `t₂`, `s` is in the image of
`mergeInto t t₁ t₂ last` iff it is in the image of `last`: the merge only
replaces values `t₁, t₂` by `t`, and `t` is excluded. -/
theorem solution_img {n : ℕ} (t t₁ t₂ s : ℕ) (last : Fin n → ℕ)
    (hst : s ≠ t) (hs1 : s ≠ t₁) (hs2 : s ≠ t₂) :
    (∃ u : Fin n, (mergeInto t t₁ t₂ last) u = s) ↔ ∃ u : Fin n, last u = s := by
  constructor
  · rintro ⟨u, hu⟩
    by_cases hm : last u = t₁ ∨ last u = t₂
    · exfalso
      have : (mergeInto t t₁ t₂ last) u = t := by
        rw [mergeInto]
        simp [hm]
      exact hst (by simpa [this] using hu.symm)
    · refine ⟨u, ?_⟩
      have : (mergeInto t t₁ t₂ last) u = last u := by
        rw [mergeInto]
        simp [hm]
      simpa [this] using hu
  · rintro ⟨u, hu⟩
    have hm : ¬ (last u = t₁ ∨ last u = t₂) := by
      intro h
      cases h with
      | inl h => exact hs1 (by simpa [hu] using h)
      | inr h => exact hs2 (by simpa [hu] using h)
    refine ⟨u, ?_⟩
    have : (mergeInto t t₁ t₂ last) u = last u := by
      rw [mergeInto]
      simp [hm]
    simp [this, hu]

theorem solution {n : ℕ} (t t₁ t₂ : ℕ) (last : Fin n → ℕ) :
  ((Finset.image (mergeInto t t₁ t₂ last) Finset.univ).erase t₁).erase t₂ ∪ {t} =
    ((Finset.image last Finset.univ).erase t₁).erase t₂ ∪ {t} := by
  ext s
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase,
    Finset.mem_image, Finset.mem_univ]
  by_cases ht : s = t
  · simp [ht]
  · by_cases h1 : s = t₁
    · simp [h1]
    · by_cases h2 : s = t₂
      · simp [h2]
      · simp [ht, h1, h2]
        exact solution_img t t₁ t₂ s last ht h1 h2
end P2MHole01_c2cc3af3

/-- Step 1 (image computation): the set of distinct times after a merge is the image of the old
state minus `t₁` and `t₂`, plus `t` (objects of `t₁, t₂` move to `t`; everything else keeps
its value; `t` always gains the two groups). -/
lemma image_after_merge {n : ℕ} (t t₁ t₂ : ℕ) (last : Fin n → ℕ) :
    (((Finset.univ.image (mergeInto t t₁ t₂ last)).erase t₁).erase t₂) ∪ {t} =
        ((Finset.univ.image last).erase t₁).erase t₂ ∪ {t} := by
  (first | exact P2MHole01_c2cc3af3.solution t t₁ t₂ last | (apply P2MHole01_c2cc3af3.solution <;> assumption))
namespace P2MHole02_8db64da6
theorem solution {n : ℕ} (t t₁ t₂ : ℕ) (last : Fin n → ℕ) (hcand : MergeCandidate last t₁ t₂) :
  (Finset.image (mergeInto t t₁ t₂ last) Finset.univ).card < (Finset.image last Finset.univ).card := by
  set f : Fin n → ℕ := mergeInto t t₁ t₂ last with hf
  set imlast : Finset ℕ := Finset.image last Finset.univ with himlast
  set Y : Finset ℕ := (imlast.erase t₁).erase t₂ with hY
  have hne : t₁ ≠ t₂ := hcand.1
  have hT1 : 0 < groupSize last t₁ := hcand.2.1
  have hT2 : 0 < groupSize last t₂ := hcand.2.2.1
  have him1 : t₁ ∈ imlast := by
    rw [Finset.mem_image]
    obtain ⟨u, hu, hval⟩ := Finset.filter_nonempty_iff.mp (by
      rw [groupSize, Finset.card_pos] at hT1
      exact hT1)
    exact ⟨u, hu, hval⟩
  have him2 : t₂ ∈ imlast := by
    rw [Finset.mem_image]
    obtain ⟨u, hu, hval⟩ := Finset.filter_nonempty_iff.mp (by
      rw [groupSize, Finset.card_pos] at hT2
      exact hT2)
    exact ⟨u, hu, hval⟩
  have hE : t₂ ∈ imlast.erase t₁ := Finset.mem_erase.mpr ⟨hne.symm, him2⟩
  have him2card : 2 ≤ imlast.card := by
    have hge : 0 < (imlast.erase t₁).card :=
      Finset.card_pos.mpr (Finset.nonempty_def.mpr ⟨t₂, hE⟩)
    have her : (imlast.erase t₁).card = imlast.card - 1 := Finset.card_erase_of_mem him1
    rw [her] at hge
    omega
  have hsub : Finset.image f Finset.univ ⊆ {t} ∪ Y := by
    intro v hv
    obtain ⟨u, _, hvu⟩ := Finset.mem_image.mp hv
    by_cases h : last u = t₁ ∨ last u = t₂
    · dsimp only [f, mergeInto] at hvu
      rw [if_pos h] at hvu
      rw [Finset.mem_union, Finset.mem_singleton]
      left
      exact hvu.symm
    · have hn1 : last u ≠ t₁ := by intro h'; apply h; exact Or.inl h'
      have hn2 : last u ≠ t₂ := by intro h'; apply h; exact Or.inr h'
      dsimp only [f, mergeInto] at hvu
      rw [if_neg h] at hvu
      rw [hvu] at hn1 hn2
      rw [Finset.mem_union, Finset.mem_singleton]
      right
      rw [hY, Finset.mem_erase, Finset.mem_erase]
      exact ⟨hn2, hn1, by rw [Finset.mem_image]; exact ⟨u, Finset.mem_univ u, hvu⟩⟩
  have hcard : (Finset.image f Finset.univ).card ≤ 1 + Y.card := by
    calc
      (Finset.image f Finset.univ).card ≤ ({t} ∪ Y).card := Finset.card_mono hsub
      _ = (insert t Y).card := by rw [Finset.singleton_union t Y]
      _ ≤ Y.card + 1 := Finset.card_insert_le t Y
      _ = 1 + Y.card := by omega
  have hYcard : Y.card = imlast.card - 2 := by
    calc
      Y.card = ((imlast.erase t₁).erase t₂).card := by rw [hY]
      _ = (imlast.erase t₁).card - 1 := by rw [Finset.card_erase_of_mem hE]
      _ = imlast.card - 2 := by
        rw [Finset.card_erase_of_mem him1]
        omega
  calc
    (Finset.image f Finset.univ).card ≤ 1 + Y.card := hcard
    _ = 1 + (imlast.card - 2) := by rw [hYcard]
    _ = imlast.card - 1 := by omega
    _ < imlast.card := Nat.sub_lt (by omega) (by decide)
end P2MHole02_8db64da6

-- riskiest
/-- Step 2 (the decrease): if both groups are nonempty and `t₁ ≠ t₂`, the merge strictly
decreases the number of distinct times. -/
lemma image_card_decreases {n : ℕ} (t t₁ t₂ : ℕ) (last : Fin n → ℕ)
    (hcand : MergeCandidate last t₁ t₂) :
    (Finset.univ.image (mergeInto t t₁ t₂ last)).card < (Finset.univ.image last).card := by
  (first | exact P2MHole02_8db64da6.solution t t₁ t₂ last hcand | (apply P2MHole02_8db64da6.solution <;> assumption))

/-- Step 3 (monotonicity of one step, glue): one `MergeStep t` strictly decreases the number
of distinct times. -/
lemma mergeStep_decreases {n : ℕ} (t : ℕ) {a b : (Fin n → ℕ) × ℕ}
    (h : MergeStep t a b) :
    (Finset.univ.image b.1).card < (Finset.univ.image a.1).card := by
  obtain ⟨t₁, t₂, hcand, hmerge, hcount⟩ := h
  rw [hmerge]
  exact image_card_decreases t t₁ t₂ a.1 hcand

namespace P2MHole03_41f820e2
universe u_1
/-- If `r x y` implies `k y < k x` for a rank function `k : α → ℕ`, then every
`r`-chain starting at `x` is finite: prove `Acc` by induction on a bound `c`
with `k x ≤ c` (and an arbitrary starting point `x`). -/
lemma acc_of_nat_decr {α : Type u_1} (r : α → α → Prop) (k : α → ℕ)
    (hdec : ∀ (a b : α), r a b → k b < k a) (x : α) : Acc (fun (b a : α) => r a b) x := by
  have hacc : ∀ (c : ℕ) (z : α), k z ≤ c → Acc (fun (b a : α) => r a b) z := by
    intro c
    induction' c with n ihn
    case zero =>
      intro z hzc
      refine Acc.intro z fun y hy => by
        have hky : k y < k z := hdec z y hy
        omega
    case succ =>
      intro z hzc
      refine Acc.intro z fun y hy => by
        have hky : k y < k z := hdec z y hy
        exact ihn y (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hky hzc))
  exact hacc (k x) x (Nat.le_refl (k x))

theorem solution {α : Type u_1} (r : α → α → Prop) (k : α → ℕ)
  (hdec : ∀ (a b : α), r a b → k b < k a) : WellFounded fun (b a : α) => r a b := by
  exact WellFounded.intro (acc_of_nat_decr r k hdec)
end P2MHole03_41f820e2

/-- Step 4 (well-foundedness from a decreasing ℕ-rank, general order fact): if `r a b → k b < k a`
for a rank `k : α → ℕ`, then the converse of `r` is well-founded (no infinite ℕ-descending chain). -/
lemma wellFounded_of_Nat_rank {α : Type*} (r : α → α → Prop) (k : α → ℕ)
    (hdec : ∀ a b, r a b → k b < k a) : WellFounded (fun b a => r a b) := by
  (first | exact P2MHole03_41f820e2.solution r k hdec | (apply P2MHole03_41f820e2.solution <;> assumption))

/-- Step 5 (clause 1, glue): `MergeStep t` is well-founded, read backwards. -/
theorem mergeStep_wellFounded {n : ℕ} (t : ℕ) :
    WellFounded (fun b a : (Fin n → ℕ) × ℕ => MergeStep t a b) := by
  exact wellFounded_of_Nat_rank (MergeStep t) (fun a => (Finset.univ.image a.1).card) fun a b =>
    by
      intro h
      exact mergeStep_decreases t h

namespace P2MHole04_5bced20e
universe u_1
theorem solution {α : Type u_1} (r : α → α → Prop) (hwf : WellFounded fun (b a : α) => r a b) (a : α) :
  ∃ (b : α), Relation.ReflTransGen r a b ∧ ∀ (c : α), ¬r b c := by
  obtain ⟨hacc⟩ := hwf
  exact (hacc a).rec (fun x h ih => by
    by_cases hrc : ∃ c, r x c
    · obtain ⟨c, hc⟩ := hrc
      obtain ⟨b, hb, hterm⟩ := ih c hc
      exact ⟨b, Relation.ReflTransGen.trans (Relation.ReflTransGen.tail Relation.ReflTransGen.refl hc) hb, hterm⟩
    · exact ⟨x, Relation.ReflTransGen.refl, fun c hc' => hrc ⟨c, hc'⟩⟩)
end P2MHole04_5bced20e

/-- Step 6 (terminal point, general order fact): if the converse of `r` is well-founded, from
every `a` some `b` is reachable by `Relation.ReflTransGen r` with no `r`-successor. -/
lemma terminal_exists {α : Type*} (r : α → α → Prop)
    (hwf : WellFounded (fun b a => r a b)) (a : α) :
    ∃ b, Relation.ReflTransGen r a b ∧ ∀ c, ¬ r b c := by
  (first | exact P2MHole04_5bced20e.solution r hwf a | (apply P2MHole04_5bced20e.solution <;> assumption))

/-- Step 7 (clause 2, glue): from every state some finite sequence of iterations reaches a
`Stable` state. -/
theorem mergeStep_reachesStable {n : ℕ} (t : ℕ) (a : (Fin n → ℕ) × ℕ) :
    ∃ b, Relation.ReflTransGen (MergeStep t) a b ∧ Stable b.1 := by
  obtain ⟨b, hrtg, hterm⟩ := terminal_exists (MergeStep t) (mergeStep_wellFounded t) a
  refine ⟨b, hrtg, ?_⟩
  intro t₁ t₂ hcand
  have : MergeStep t b (mergeInto t t₁ t₂ b.1, b.2 + groupSize b.1 t₁ + groupSize b.1 t₂) :=
    ⟨t₁, t₂, hcand, rfl, rfl⟩
  exact hterm (mergeInto t t₁ t₂ b.1, b.2 + groupSize b.1 t₁ + groupSize b.1 t₂) this

theorem solution {n : ℕ} (t : ℕ) :
    WellFounded (fun b a : (Fin n → ℕ) × ℕ => MergeStep t a b) ∧
      ∀ a : (Fin n → ℕ) × ℕ, ∃ b, Relation.ReflTransGen (MergeStep t) a b ∧ Stable b.1 := by
  exact ⟨mergeStep_wellFounded t, fun a => mergeStep_reachesStable t a⟩
