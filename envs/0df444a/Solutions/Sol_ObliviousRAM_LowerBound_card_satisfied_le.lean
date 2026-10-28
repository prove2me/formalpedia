-- Prove2me | solution 1 for ObliviousRAM.LowerBound.card_satisfied_le
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T16:49:10.911388+00:00
-- url     : https://prove2.me/submissions/db339ad3-685b-4e16-8a58-f6f08f42acb6

import Mathlib
import Definitions.Def_ObliviousRAM_LowerBound_Game

open ObliviousRAM.LowerBound
open Classical

noncomputable def oram_run {m : ℕ} (b : ℕ) (s : Option (State m)) (l : List (Action m)) :
    Option (State m) :=
  l.foldl (fun os act => os.bind (fun s => step b s act)) s

theorem oram_run_none {m : ℕ} (b : ℕ) (l : List (Action m)) : oram_run b none l = none := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa [oram_run, List.foldl_cons] using ih

theorem oram_run_cons {m : ℕ} (b : ℕ) (s : State m) (a : Action m) (l : List (Action m)) :
    oram_run b (some s) (a :: l) = oram_run b (step b s a) l := by
  simp [oram_run, List.foldl_cons]

theorem oram_step_hand {m : ℕ} (b : ℕ) (s s' : State m) (a : Action m)
    (h : step b s a = some s') (hs : s.hand.card ≤ b) : s'.hand.card ≤ b := by
  obtain ⟨v, h0⟩ := a
  cases h0 with
  | take =>
    simp only [step] at h
    split at h
    · simp at h
    · split_ifs at h with hc
      simp only [Option.some.injEq] at h
      subst h
      exact (Finset.card_insert_le _ _).trans (by omega)
  | place β =>
    simp only [step] at h
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    exact (Finset.card_erase_le).trans hs
  | nothing =>
    simp only [step, Option.some.injEq] at h
    subst h; exact hs


theorem oram_run_hand {m : ℕ} (b : ℕ) (l : List (Action m)) :
    ∀ s s' : State m, s.hand.card ≤ b → oram_run b (some s) l = some s' → s'.hand.card ≤ b := by
  induction l with
  | nil =>
    intro s s' hs h
    simp only [oram_run, List.foldl_nil, Option.some.injEq] at h
    subst h; exact hs
  | cons a l ih =>
    intro s s' hs h
    rw [oram_run_cons] at h
    rcases hst : step b s a with _ | s1
    · rw [hst, oram_run_none] at h; simp at h
    · rw [hst] at h
      exact ih s1 s' (oram_step_hand b s s1 a hst hs) h

theorem oram_handAfter_card {m : ℕ} (b : ℕ) (a : List (Action m)) (k : ℕ) :
    (handAfter b a k).card ≤ b := by
  unfold handAfter
  rcases h : stateAfter b a k with _ | s
  · simp
  · simp only [Option.map_some, Option.getD_some]
    have : oram_run b (some (initState m)) (a.take k) = some s := h
    exact oram_run_hand b _ _ _ (by simp [initState]) this

theorem oram_mono_inj {t L : ℕ} (g1 g2 : Fin t → Fin L) (h1 : Monotone g1) (h2 : Monotone g2)
    (h : Finset.univ.val.map g1 = Finset.univ.val.map g2) : g1 = g2 := by
  rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at h
  exact List.ofFn_injective (List.Perm.eq_of_sortedLE h1.sortedLE_ofFn h2.sortedLE_ofFn h)

theorem oram_card_mono (t L : ℕ) :
    (Finset.univ.filter fun g : Fin t → Fin L => Monotone g).card ≤ Nat.multichoose L t := by
  let f : (Fin t → Fin L) → Sym (Fin L) t := fun g => ⟨Finset.univ.val.map g, by simp⟩
  have hinj : Set.InjOn f ↑(Finset.univ.filter fun g : Fin t → Fin L => Monotone g) := by
    intro g1 hg1 g2 hg2 heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg1 hg2
    apply oram_mono_inj g1 g2 hg1 hg2
    exact congrArg Subtype.val heq
  rw [← Finset.card_image_of_injOn hinj, ← Sym.card_sym_fin_eq_multichoose L t]
  exact Finset.card_le_univ _

theorem solution {b m t : ℕ} (a : List (Action m)) :
    (Finset.univ.filter fun r : Fin t → Fin m => Satisfies b a r).card ≤
      Nat.multichoose a.length t * b ^ t := by
  set L := a.length with hL
  let J : Finset (Fin t → Fin L) := Finset.univ.filter fun g => Monotone g
  have hsub : (Finset.univ.filter fun r : Fin t → Fin m => Satisfies b a r) ⊆
      J.biUnion (fun g => Fintype.piFinset (fun i => handAfter b a (g i + 1))) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    obtain ⟨-, j, hjm, hj1, hjL, -, hjr⟩ := hr
    rw [Finset.mem_biUnion]
    refine ⟨fun i => ⟨j i - 1, by have := hj1 i; have := hjL i; omega⟩, ?_, ?_⟩
    · simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
      intro x y hxy
      have := hjm hxy
      simp only [Fin.mk_le_mk]
      omega
    · rw [Fintype.mem_piFinset]
      intro i
      have : j i - 1 + 1 = j i := by have := hj1 i; omega
      simp only
      rw [this]; exact hjr i
  calc _ ≤ (J.biUnion (fun g => Fintype.piFinset (fun i => handAfter b a (g i + 1)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ g ∈ J, (Fintype.piFinset (fun i => handAfter b a (g i + 1))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ J, b ^ t := by
        apply Finset.sum_le_sum
        intro g _
        rw [Fintype.card_piFinset]
        calc ∏ i, (handAfter b a (g i + 1)).card ≤ ∏ _i : Fin t, b :=
              Finset.prod_le_prod' (fun i _ => oram_handAfter_card b a _)
          _ = b ^ t := by simp
    _ = J.card * b ^ t := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ Nat.multichoose L t * b ^ t := Nat.mul_le_mul_right _ (oram_card_mono t L)
