-- Prove2me | solution 1 for VRPTWColGen92.Bound.fig1_solution_spaces
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:53:20.082395+00:00
-- url     : https://prove2.me/submissions/a2078452-42f9-483c-9fee-3a9827416449

import Mathlib
import Definitions.Def_VRPTWColGen92_Bound_Network
import Definitions.Def_VRPTWColGen92_Bound_Fig1

open VRPTWColGen92.Bound
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private lemma fin_zero (h : 0 < 4) : (⟨0,h⟩ : Fin 4) = 0 := rfl
private lemma fin_one (h : 1 < 4) : (⟨1,h⟩ : Fin 4) = 1 := rfl
private lemma fin_two (h : 2 < 4) : (⟨2,h⟩ : Fin 4) = 2 := rfl
private lemma fin_three (h : 3 < 4) : (⟨3,h⟩ : Fin 4) = 3 := rfl

private def candidates : List (List (Fin 4)) := [[1], [2], [3], [1, 2], [1, 3], [2, 1], [2, 3], [3, 1], [1, 2, 3], [2, 1, 3], [2, 3, 1], [1, 2, 1], [1, 3, 1], [2, 1, 2], [3, 1, 3], [1, 2, 1, 2], [1, 2, 1, 3], [1, 2, 3, 1], [1, 3, 1, 3], [2, 1, 2, 1], [2, 1, 3, 1], [3, 1, 3, 1]]

private lemma path_forward (c : Fin 4 → Fin 4 → ℝ) (p : List (Fin 4))
    (h : IsPath (fig1 c) p) : p ∈ candidates := by
  rcases h with ⟨hne, hz, hA, ⟨T, h0, hT, hW⟩, hL⟩
  cases p with
  | nil =>
    have hw0 := hW 0 (by norm_num [nodes])
    have ht0 := hT 0 (by norm_num [nodes])
    have hw1 := hW 1 (by norm_num [nodes])
    norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons] at *
    <;> linarith
  | cons a p =>
    fin_cases a

    all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
    · simp at hz
    · 
      cases p with
      | nil =>
        norm_num [candidates, Fin.ext_iff]
      | cons a p =>
        fin_cases a

        all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
        · simp at hz
        · have he := hA 1 (by simp [nodes])
          norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
        · 
          cases p with
          | nil =>
            norm_num [candidates, Fin.ext_iff]
          | cons a p =>
            fin_cases a

            all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
            · simp at hz
            · 
              cases p with
              | nil =>
                norm_num [candidates, Fin.ext_iff]
              | cons a p =>
                fin_cases a

                all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
                · simp at hz
                · have he := hA 3 (by simp [nodes])
                  norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
                · 
                  cases p with
                  | nil =>
                    norm_num [candidates, Fin.ext_iff]
                  | cons a p =>
                    fin_cases a

                    all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
                    · simp at hz
                    · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                        intro v hv
                        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                        fin_cases i <;> norm_num [fig1Dem])
                      norm_num [load, fig1, fig1Dem] at hL
                      linarith
                    · have he := hA 4 (by simp [nodes])
                      norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
                    · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                        intro v hv
                        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                        fin_cases i <;> norm_num [fig1Dem])
                      norm_num [load, fig1, fig1Dem] at hL
                      linarith
                · 
                  cases p with
                  | nil =>
                    norm_num [candidates, Fin.ext_iff]
                  | cons a p =>
                    fin_cases a

                    all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
                    · simp at hz
                    · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                        intro v hv
                        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                        fin_cases i <;> norm_num [fig1Dem])
                      norm_num [load, fig1, fig1Dem] at hL
                      linarith
                    · have he := hA 4 (by simp [nodes])
                      norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
                    · have he := hA 4 (by simp [nodes])
                      norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
            · have he := hA 2 (by simp [nodes])
              norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
            · 
              cases p with
              | nil =>
                norm_num [candidates, Fin.ext_iff]
              | cons a p =>
                fin_cases a

                all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
                · simp at hz
                · 
                  cases p with
                  | nil =>
                    norm_num [candidates, Fin.ext_iff]
                  | cons a p =>
                    fin_cases a

                    all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
                    · simp at hz
                    · have he := hA 4 (by simp [nodes])
                      norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
                    · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                        intro v hv
                        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                        fin_cases i <;> norm_num [fig1Dem])
                      norm_num [load, fig1, fig1Dem] at hL
                      linarith
                    · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                        intro v hv
                        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                        fin_cases i <;> norm_num [fig1Dem])
                      norm_num [load, fig1, fig1Dem] at hL
                      linarith
                · have he := hA 3 (by simp [nodes])
                  norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
                · have he := hA 3 (by simp [nodes])
                  norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
        · 
          cases p with
          | nil =>
            norm_num [candidates, Fin.ext_iff]
          | cons a p =>
            fin_cases a

            all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
            · simp at hz
            · 
              cases p with
              | nil =>
                norm_num [candidates, Fin.ext_iff]
              | cons a p =>
                fin_cases a

                all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
                · simp at hz
                · have he := hA 3 (by simp [nodes])
                  norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
                · 
                  cases p with
                  | nil =>
                    have hw0 := hW 0 (by norm_num [nodes])
                    have ht0 := hT 0 (by norm_num [nodes])
                    have hw1 := hW 1 (by norm_num [nodes])
                    have ht1 := hT 1 (by norm_num [nodes])
                    have hw2 := hW 2 (by norm_num [nodes])
                    have ht2 := hT 2 (by norm_num [nodes])
                    have hw3 := hW 3 (by norm_num [nodes])
                    have ht3 := hT 3 (by norm_num [nodes])
                    have hw4 := hW 4 (by norm_num [nodes])
                    have ht4 := hT 4 (by norm_num [nodes])
                    have hw5 := hW 5 (by norm_num [nodes])
                    norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons] at *
                    linarith
                  | cons a p =>
                    fin_cases a

                    all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
                    · simp at hz
                    · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                        intro v hv
                        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                        fin_cases i <;> norm_num [fig1Dem])
                      norm_num [load, fig1, fig1Dem] at hL
                      linarith
                    · have he := hA 4 (by simp [nodes])
                      norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
                    · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                        intro v hv
                        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                        fin_cases i <;> norm_num [fig1Dem])
                      norm_num [load, fig1, fig1Dem] at hL
                      linarith
                · 
                  cases p with
                  | nil =>
                    norm_num [candidates, Fin.ext_iff]
                  | cons a p =>
                    fin_cases a

                    all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
                    · simp at hz
                    · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                        intro v hv
                        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                        fin_cases i <;> norm_num [fig1Dem])
                      norm_num [load, fig1, fig1Dem] at hL
                      linarith
                    · have he := hA 4 (by simp [nodes])
                      norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
                    · have he := hA 4 (by simp [nodes])
                      norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
            · have he := hA 2 (by simp [nodes])
              norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
            · have he := hA 2 (by simp [nodes])
              norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
    · 
      cases p with
      | nil =>
        norm_num [candidates, Fin.ext_iff]
      | cons a p =>
        fin_cases a

        all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
        · simp at hz
        · 
          cases p with
          | nil =>
            norm_num [candidates, Fin.ext_iff]
          | cons a p =>
            fin_cases a

            all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
            · simp at hz
            · have he := hA 2 (by simp [nodes])
              norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
            · 
              cases p with
              | nil =>
                norm_num [candidates, Fin.ext_iff]
              | cons a p =>
                fin_cases a

                all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
                · simp at hz
                · 
                  cases p with
                  | nil =>
                    norm_num [candidates, Fin.ext_iff]
                  | cons a p =>
                    fin_cases a

                    all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
                    · simp at hz
                    · have he := hA 4 (by simp [nodes])
                      norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
                    · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                        intro v hv
                        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                        fin_cases i <;> norm_num [fig1Dem])
                      norm_num [load, fig1, fig1Dem] at hL
                      linarith
                    · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                        intro v hv
                        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                        fin_cases i <;> norm_num [fig1Dem])
                      norm_num [load, fig1, fig1Dem] at hL
                      linarith
                · have he := hA 3 (by simp [nodes])
                  norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
                · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                    intro v hv
                    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                    fin_cases i <;> norm_num [fig1Dem])
                  norm_num [load, fig1, fig1Dem] at hL
                  linarith
            · 
              cases p with
              | nil =>
                norm_num [candidates, Fin.ext_iff]
              | cons a p =>
                fin_cases a

                all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
                · simp at hz
                · 
                  cases p with
                  | nil =>
                    norm_num [candidates, Fin.ext_iff]
                  | cons a p =>
                    fin_cases a

                    all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
                    · simp at hz
                    · have he := hA 4 (by simp [nodes])
                      norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
                    · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                        intro v hv
                        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                        fin_cases i <;> norm_num [fig1Dem])
                      norm_num [load, fig1, fig1Dem] at hL
                      linarith
                    · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                        intro v hv
                        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                        fin_cases i <;> norm_num [fig1Dem])
                      norm_num [load, fig1, fig1Dem] at hL
                      linarith
                · have he := hA 3 (by simp [nodes])
                  norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
                · have he := hA 3 (by simp [nodes])
                  norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
        · have he := hA 1 (by simp [nodes])
          norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
        · 
          cases p with
          | nil =>
            norm_num [candidates, Fin.ext_iff]
          | cons a p =>
            fin_cases a

            all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
            · simp at hz
            · 
              cases p with
              | nil =>
                norm_num [candidates, Fin.ext_iff]
              | cons a p =>
                fin_cases a

                all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
                · simp at hz
                · have he := hA 3 (by simp [nodes])
                  norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
                · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                    intro v hv
                    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                    fin_cases i <;> norm_num [fig1Dem])
                  norm_num [load, fig1, fig1Dem] at hL
                  linarith
                · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                    intro v hv
                    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                    fin_cases i <;> norm_num [fig1Dem])
                  norm_num [load, fig1, fig1Dem] at hL
                  linarith
            · have he := hA 2 (by simp [nodes])
              norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
            · have he := hA 2 (by simp [nodes])
              norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
    · 
      cases p with
      | nil =>
        norm_num [candidates, Fin.ext_iff]
      | cons a p =>
        fin_cases a

        all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
        · simp at hz
        · 
          cases p with
          | nil =>
            norm_num [candidates, Fin.ext_iff]
          | cons a p =>
            fin_cases a

            all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
            · simp at hz
            · have he := hA 2 (by simp [nodes])
              norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
            · 
              cases p with
              | nil =>
                have hw0 := hW 0 (by norm_num [nodes])
                have ht0 := hT 0 (by norm_num [nodes])
                have hw1 := hW 1 (by norm_num [nodes])
                have ht1 := hT 1 (by norm_num [nodes])
                have hw2 := hW 2 (by norm_num [nodes])
                have ht2 := hT 2 (by norm_num [nodes])
                have hw3 := hW 3 (by norm_num [nodes])
                have ht3 := hT 3 (by norm_num [nodes])
                have hw4 := hW 4 (by norm_num [nodes])
                norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons] at *
                linarith
              | cons a p =>
                fin_cases a

                all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
                · simp at hz
                · 
                  cases p with
                  | nil =>
                    have hw0 := hW 0 (by norm_num [nodes])
                    have ht0 := hT 0 (by norm_num [nodes])
                    have hw1 := hW 1 (by norm_num [nodes])
                    have ht1 := hT 1 (by norm_num [nodes])
                    have hw2 := hW 2 (by norm_num [nodes])
                    have ht2 := hT 2 (by norm_num [nodes])
                    have hw3 := hW 3 (by norm_num [nodes])
                    have ht3 := hT 3 (by norm_num [nodes])
                    have hw4 := hW 4 (by norm_num [nodes])
                    have ht4 := hT 4 (by norm_num [nodes])
                    have hw5 := hW 5 (by norm_num [nodes])
                    norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons] at *
                    linarith
                  | cons a p =>
                    fin_cases a

                    all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
                    · simp at hz
                    · have he := hA 4 (by simp [nodes])
                      norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
                    · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                        intro v hv
                        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                        fin_cases i <;> norm_num [fig1Dem])
                      norm_num [load, fig1, fig1Dem] at hL
                      linarith
                    · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                        intro v hv
                        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                        fin_cases i <;> norm_num [fig1Dem])
                      norm_num [load, fig1, fig1Dem] at hL
                      linarith
                · have he := hA 3 (by simp [nodes])
                  norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
                · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                    intro v hv
                    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                    fin_cases i <;> norm_num [fig1Dem])
                  norm_num [load, fig1, fig1Dem] at hL
                  linarith
            · 
              cases p with
              | nil =>
                norm_num [candidates, Fin.ext_iff]
              | cons a p =>
                fin_cases a

                all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
                · simp at hz
                · 
                  cases p with
                  | nil =>
                    norm_num [candidates, Fin.ext_iff]
                  | cons a p =>
                    fin_cases a

                    all_goals simp only [id_eq, fin_zero, fin_one, fin_two, fin_three] at hA hT hW hL ⊢
                    · simp at hz
                    · have he := hA 4 (by simp [nodes])
                      norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
                    · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                        intro v hv
                        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                        fin_cases i <;> norm_num [fig1Dem])
                      norm_num [load, fig1, fig1Dem] at hL
                      linarith
                    · have hn : 0 ≤ (p.map fig1Dem).sum := List.sum_nonneg (by
                        intro v hv
                        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
                        fin_cases i <;> norm_num [fig1Dem])
                      norm_num [load, fig1, fig1Dem] at hL
                      linarith
                · have he := hA 3 (by simp [nodes])
                  norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
                · have he := hA 3 (by simp [nodes])
                  norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
        · have he := hA 1 (by simp [nodes])
          norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he
        · have he := hA 1 (by simp [nodes])
          norm_num [nodes, fig1, fig1Arc, Fin.ext_iff] at he

private lemma path_reverse (c : Fin 4 → Fin 4 → ℝ) (p : List (Fin 4))
    (h : p ∈ candidates) : IsPath (fig1 c) p := by
  simp only [candidates, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 1 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 1, 2] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 1 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 2 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 1 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 2, 4] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 1 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 2 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 1 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 4, 6] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 1 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 2 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 2 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 1, 2, 4] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 2 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 3 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 2 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 1, 4, 6] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 2 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 3 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 2 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 2, 3, 4] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 2 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 3 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 2 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 2, 4, 6] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 2 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 3 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 2 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 4, 5, 6] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 2 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 3 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 3 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 1, 2, 4, 6] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 3 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 4 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 3 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 2, 3, 4, 6] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 3 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 4 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 3 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 2, 4, 5, 6] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 3 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 4 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 3 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 1, 2, 3, 4] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 3 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 4 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 3 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 1, 4, 5, 6] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 3 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 4 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 3 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 2, 3, 4, 6] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 3 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 4 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 3 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 4, 5, 6, 8] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 3 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 4 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 4 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 1, 2, 3, 4, 6] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 4 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 5 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 4 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 1, 2, 3, 4, 6] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 4 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 5 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 4 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 1, 2, 4, 5, 6] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 4 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 5 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 4 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 1, 4, 5, 6, 8] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 4 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 5 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 4 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 2, 3, 4, 5, 6] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 4 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 5 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 4 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 2, 3, 4, 5, 6] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 4 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 5 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]
  · refine ⟨by decide, by decide, ?_, ?_, ?_⟩
    · intro k hk
      norm_num [nodes] at hk
      have hk' : k ≤ 4 := by omega
      interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · refine ⟨fun k => ([0, 4, 5, 6, 7, 8] : List ℝ)[k]?.getD 0, by norm_num, ?_, ?_⟩
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 4 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
      · intro k hk
        norm_num [nodes] at hk
        have hk' : k ≤ 5 := by omega
        interval_cases k <;> norm_num [nodes, fig1, fig1Arc, fig1Dur, fig1A, fig1B, List.getElem_cons]
    · norm_num [load, fig1, fig1Dem]

theorem solution (c : Fin 4 → Fin 4 → ℝ) :
    {p | IsRoute (fig1 c) p} =
      ({[1], [2], [3], [1, 2], [1, 3], [2, 1], [2, 3], [3, 1], [1, 2, 3], [2, 1, 3], [2, 3, 1]} :
        Set (List (Fin 4))) ∧
    {p | IsPath (fig1 c) p} =
      ({[1], [2], [3], [1, 2], [1, 3], [2, 1], [2, 3], [3, 1], [1, 2, 3], [2, 1, 3], [2, 3, 1],
        [1, 2, 1], [1, 3, 1], [2, 1, 2], [3, 1, 3], [1, 2, 1, 2], [1, 2, 1, 3], [1, 2, 3, 1],
        [1, 3, 1, 3], [2, 1, 2, 1], [2, 1, 3, 1], [3, 1, 3, 1]} : Set (List (Fin 4))) ∧
    {p | IsPath3 (fig1 c) p} =
      ({[1], [2], [3], [1, 2], [1, 3], [2, 1], [2, 3], [3, 1], [1, 2, 3], [2, 1, 3], [2, 3, 1],
        [1, 2, 3, 1]} : Set (List (Fin 4))) := by
  have hp (p : List (Fin 4)) : IsPath (fig1 c) p ↔ p ∈ candidates :=
    ⟨path_forward c p, path_reverse c p⟩
  refine ⟨?_, ?_, ?_⟩
  · ext p
    simp only [Set.mem_setOf_eq, IsRoute, hp]
    simp [candidates, List.nodup_cons]
    aesop
  · ext p
    simp [hp, candidates]
  · ext p
    simp only [Set.mem_setOf_eq, IsPath3, hp]
    simp [candidates]
    constructor
    · rintro ⟨h, hc⟩
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · have hh := hc 0 (by norm_num)
        simp at hh
      · have hh := hc 0 (by norm_num)
        simp at hh
      · have hh := hc 0 (by norm_num)
        simp at hh
      · have hh := hc 0 (by norm_num)
        simp at hh
      · have hh := hc 0 (by norm_num)
        simp at hh
      · have hh := hc 0 (by norm_num)
        simp at hh
      · simp
      · have hh := hc 0 (by norm_num)
        simp at hh
      · have hh := hc 0 (by norm_num)
        simp at hh
      · have hh := hc 1 (by norm_num)
        simp at hh
      · have hh := hc 0 (by norm_num)
        simp at hh
    · intro h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · constructor
        · simp
        · intro k hk
          simp only [List.length_cons, List.length_nil] at hk
          omega
      · constructor
        · simp
        · intro k hk
          simp only [List.length_cons, List.length_nil] at hk
          omega
      · constructor
        · simp
        · intro k hk
          simp only [List.length_cons, List.length_nil] at hk
          omega
      · constructor
        · simp
        · intro k hk
          simp only [List.length_cons, List.length_nil] at hk
          omega
      · constructor
        · simp
        · intro k hk
          simp only [List.length_cons, List.length_nil] at hk
          omega
      · constructor
        · simp
        · intro k hk
          simp only [List.length_cons, List.length_nil] at hk
          omega
      · constructor
        · simp
        · intro k hk
          simp only [List.length_cons, List.length_nil] at hk
          omega
      · constructor
        · simp
        · intro k hk
          simp only [List.length_cons, List.length_nil] at hk
          omega
      · constructor
        · simp
        · intro k hk
          have hk' : k ≤ 0 := by simp only [List.length_cons, List.length_nil] at hk; omega
          interval_cases k <;> norm_num [Fin.ext_iff]
      · constructor
        · simp
        · intro k hk
          have hk' : k ≤ 0 := by simp only [List.length_cons, List.length_nil] at hk; omega
          interval_cases k <;> norm_num [Fin.ext_iff]
      · constructor
        · simp
        · intro k hk
          have hk' : k ≤ 0 := by simp only [List.length_cons, List.length_nil] at hk; omega
          interval_cases k <;> norm_num [Fin.ext_iff]
      · constructor
        · simp
        · intro k hk
          have hk' : k ≤ 1 := by simp only [List.length_cons, List.length_nil] at hk; omega
          interval_cases k <;> norm_num [Fin.ext_iff]
#print axioms solution
