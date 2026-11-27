-- Prove2me | solution 1 for StableDispatch.Markov.Supplement.prop_B_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:24:18.908736+00:00
-- url     : https://prove2.me/submissions/487af0f5-e06c-42d0-83f4-23b25dc964ae

import Mathlib
import Definitions.Def_StableDispatch_Markov_Supplement_Policy

open StableDispatch
open StableDispatch.Markov
open StableDispatch.Markov.Supplement

open MeasureTheory ProbabilityTheory Asymptotics Filter

theorem solution (c : ℕ → ℝ) (hc : c =o[atTop] (fun n : ℕ => Real.log n))
    (P : ∀ n : ℕ, 1 ≤ n → Policy n) (hsym : ∀ n (hn : 1 ≤ n), WeaklySymmetric (P n hn))
    (hmem : ∀ n (hn : 1 ≤ n), ((P n hn).memSize : ℝ) ≤ (2 : ℝ) ^ c n)
    (s : ℕ → ℝ) (hs : s =o[atTop] (fun n : ℕ => (n : ℝ))) :
    ∃ N : ℕ, ∀ n (hn : 1 ≤ n), N ≤ n →
      ∀ (m : Fin (P n hn).memSize) (w : ℝ), 0 ≤ w →
      ∀ S : Finset (Fin n), (S.card : ℝ) ≤ s n →
        0 < unif {u | ∃ i ∉ S, (P n hn).f1 m w u = insert i S} →
        ∀ j ∉ S, ∀ j' ∉ S,
          unif[|{u | ∃ i ∉ S, (P n hn).f1 m w u = insert i S}] {u | j ∈ (P n hn).f1 m w u} =
            unif[|{u | ∃ i ∉ S, (P n hn).f1 m w u = insert i S}]
              {u | j' ∈ (P n hn).f1 m w u} := by
                have h1 := hc.bound (show (0:ℝ) < 1/2 by norm_num)
                have h2 := hs.bound (show (0:ℝ) < 1/4 by norm_num)
                obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h1.and (h2.and (Filter.eventually_ge_atTop 16)))
                refine ⟨N, ?_⟩
                intro n hn hNn m w hw S hS _hpos j hj j' hj'
                obtain ⟨hcn, hsn, h16⟩ := hN n hNn
                have hmemn := hmem n hn
                have hsymn := hsym n hn
                generalize P n hn = Q at hmemn hsymn m ⊢
                -- cardinality bound
                have hcard : Q.memSize + S.card + 1 < n := by
                  have hn16 : (16:ℝ) ≤ n := by exact_mod_cast h16
                  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
                  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogn] at hcn
                  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ n)] at hsn
                  have hcn' : c n ≤ 1/2 * Real.log n := (le_abs_self (c n)).trans hcn
                  have hsn' : s n ≤ 1/4 * n := (le_abs_self (s n)).trans hsn
                  have hl2 := Real.log_two_lt_d9
                  have hl2' : 0 < Real.log 2 := Real.log_pos one_lt_two
                  have hprod : Real.log 2 * c n ≤ Real.log n / 2 := by
                    by_cases h : 0 ≤ c n
                    · nlinarith
                    · nlinarith
                  have hx : Real.exp (Real.log n / 2) * Real.exp (Real.log n / 2) = n := by
                    rw [← Real.exp_add, show Real.log n / 2 + Real.log n / 2 = Real.log n by ring,
                      Real.exp_log (by linarith)]
                  have hxpos := Real.exp_pos (Real.log n / 2)
                  have hxle : Real.exp (Real.log n / 2) ≤ n / 4 := by nlinarith
                  have h2le : (2:ℝ) ^ c n ≤ n / 4 := by
                    rw [Real.rpow_def_of_pos two_pos]
                    exact (Real.exp_le_exp.mpr hprod).trans hxle
                  have : ((Q.memSize + S.card + 1 : ℕ) : ℝ) < n := by
                    push_cast
                    linarith
                  exact_mod_cast this
                -- measurability
                have hmeasT : ∀ T : Finset (Fin n), MeasurableSet {u | Q.f1 m w u = T} := by
                  intro T
                  have := Q.measurable_f1 m T
                  exact this.preimage measurable_prodMk_left
                have hA : MeasurableSet {u | ∃ i ∉ S, Q.f1 m w u = insert i S} := by
                  have : {u | ∃ i ∉ S, Q.f1 m w u = insert i S} =
                      ⋃ i ∈ (Sᶜ : Finset (Fin n)), {u | Q.f1 m w u = insert i S} := by
                    ext u; simp
                  rw [this]
                  exact Finset.measurableSet_biUnion _ (fun i _ => hmeasT _)
                have hinter : ∀ x ∉ S, {u | ∃ i ∉ S, Q.f1 m w u = insert i S} ∩ {u | x ∈ Q.f1 m w u} =
                    {u | Q.f1 m w u = insert x S} := by
                  intro x hx
                  ext u
                  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
                  constructor
                  · rintro ⟨⟨i, hi, he⟩, hxu⟩
                    rw [he, Finset.mem_insert] at hxu
                    rcases hxu with h | h
                    · rw [he, h]
                    · exact absurd h hx
                  · intro he
                    exact ⟨⟨x, hx, he⟩, by rw [he]; exact Finset.mem_insert_self _ _⟩
                rw [cond_apply hA, cond_apply hA, hinter j hj, hinter j' hj']
                congr 1
                -- main combinatorial claim
                set p : Fin Q.memSize → Fin n → ENNReal := fun m0 x => unif {u | Q.f1 m0 w u = insert x S}
                  with hp
                show p m j = p m j'
                have key : ∀ (a b : Fin n) (m0 : Fin Q.memSize), ∃ m' : Fin Q.memSize,
                    a ∉ S → b ∉ S → ∀ x, p m' x = p m0 (Equiv.swap a b x) := by
                  intro a b m0
                  obtain ⟨σM, hσ1, -⟩ := hsymn (Equiv.swap a b)
                  refine ⟨σM m0, fun ha hb x => ?_⟩
                  have hSfix : S.map (Equiv.swap a b).toEmbedding = S := by
                    ext y
                    simp only [Finset.mem_map, Equiv.toEmbedding_apply]
                    constructor
                    · rintro ⟨z, hz, rfl⟩
                      rwa [Equiv.swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem hz ha)
                        (ne_of_mem_of_not_mem hz hb)]
                    · intro hy
                      exact ⟨y, hy, Equiv.swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem hy ha)
                        (ne_of_mem_of_not_mem hy hb)⟩
                  simp only [hp]
                  rw [← hσ1 m0 w hw (insert x S)]
                  congr 1
                  ext u
                  simp only [Set.mem_setOf_eq]
                  have : insert x S = (insert (Equiv.swap a b x) S).map (Equiv.swap a b).toEmbedding := by
                    rw [Finset.map_insert, hSfix]
                    simp
                  rw [this]
                  exact Finset.map_inj
                by_contra hne
                choose g hg using key
                let C := (Sᶜ : Finset (Fin n)).erase j'
                let f : Fin n → Fin Q.memSize := fun l => if p m l = p m j then g j' l m else g j l m
                have hCcard : (Finset.univ : Finset (Fin Q.memSize)).card < C.card := by
                  rw [Finset.card_univ, Fintype.card_fin, Finset.card_erase_of_mem (by simpa using hj'),
                    Finset.card_compl, Fintype.card_fin]
                  omega
                obtain ⟨l, hl, l', hl', hll', hfe⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hCcard
                  (f := f) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
                have hl2 := Finset.mem_erase.mp hl
                have hl2' := Finset.mem_erase.mp hl'
                have hlS : l ∉ S := by simpa using hl2.2
                have hl'S : l' ∉ S := by simpa using hl2'.2
                have hlj' : l ≠ j' := hl2.1
                have hl'j' : l' ≠ j' := hl2'.1
                have hjj' : j ≠ j' := fun h => hne (h ▸ rfl)
                by_cases hE : p m l = p m j <;> by_cases hE' : p m l' = p m j <;>
                  simp only [f, hE, hE', if_true, if_false] at hfe
                · -- both E
                  have e1 := hg j' l m hj' hlS l
                  have e2 := hg j' l' m hj' hl'S l
                  rw [hfe, Equiv.swap_apply_right] at e1
                  rw [e1, Equiv.swap_apply_of_ne_of_ne hlj' hll'] at e2
                  exact hne (hE.symm.trans e2.symm)
                · -- l E, l' F
                  have e1 := hg j' l m hj' hlS j'
                  have e2 := hg j l' m hj hl'S j'
                  rw [hfe, Equiv.swap_apply_left] at e1
                  rw [e1, Equiv.swap_apply_of_ne_of_ne hjj'.symm hl'j'.symm] at e2
                  exact hne (hE.symm.trans e2)
                · -- l F, l' E
                  have e1 := hg j l m hj hlS j'
                  have e2 := hg j' l' m hj' hl'S j'
                  rw [hfe, Equiv.swap_apply_of_ne_of_ne hjj'.symm hlj'.symm] at e1
                  rw [e1, Equiv.swap_apply_left] at e2
                  exact hne (hE'.symm.trans e2.symm)
                · -- both F
                  have e1 := hg j l m hj hlS l
                  have e2 := hg j l' m hj hl'S l
                  rw [hfe, Equiv.swap_apply_right] at e1
                  rw [e1, Equiv.swap_apply_of_ne_of_ne (fun h => hE (by rw [h])) hll'] at e2
                  exact hE e2.symm
