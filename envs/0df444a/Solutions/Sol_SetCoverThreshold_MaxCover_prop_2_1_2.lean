-- Prove2me | solution 1 for SetCoverThreshold.MaxCover.prop_2_1_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T18:38:27.082501+00:00
-- url     : https://prove2.me/submissions/59d4edbd-064a-4b54-b970-c87a43a8a4b8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Theorems.Thm_SetCoverThreshold_SetCover_prop_2_1_2

set_option autoImplicit false

open CookPvsNP SetCoverThreshold.MaxCover

private lemma to_setCover_thm211 (h211 : SetCoverThreshold.MaxCover.Thm211) :
    SetCoverThreshold.SetCover.Thm211 := by
  rcases h211 with ⟨B, ε, hε, hGap⟩
  refine ⟨B, ε, hε, ?_⟩
  intro Sym' _ _ L' hL'
  rcases hGap Sym' L' hL' with ⟨f, hf_poly, hf_spec⟩
  refine ⟨f, hf_poly, fun x => ⟨(hf_spec x).1, fun hx => ?_⟩⟩
  rcases (hf_spec x).2 hx with ⟨hB, hne, hsat⟩
  exact ⟨hB, List.length_pos_of_ne_nil hne, hsat⟩

private lemma filter_ofFn_length {n : ℕ} {α : Type*} (f : Fin n → α) (p : α → Bool) :
    ((List.ofFn f).filter p).length = (Finset.univ.filter (fun i : Fin n => p (f i) = true)).card := by
  have h1 : List.ofFn f = (List.finRange n).map f :=
    List.ext_get (by simp) (fun i h1 h2 => by simp)
  rw [h1, List.filter_map]
  have h2 : Finset.univ.filter (fun i : Fin n => p (f i) = true) =
      ((List.finRange n).filter (p ∘ f)).toFinset := by
    ext i
    simp [Function.comp]
  rw [h2, List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _), List.length_map]

private lemma formula5_toCNF_is3CNF5 (φ : SetCoverThreshold.SetCover.Formula5) :
    SetCoverThreshold.MaxCover.Is3CNF5 φ.toCNF := by
  constructor
  · intro C hC
    rw [SetCoverThreshold.SetCover.Formula5.toCNF, List.mem_ofFn] at hC
    rcases hC with ⟨c, rfl⟩
    refine ⟨List.length_ofFn, ?_⟩
    have h01 : ((φ.clause c 0).2 : ℕ) ≠ ((φ.clause c 1).2 : ℕ) :=
      fun h => (by decide : (0 : Fin 3) ≠ 1) (φ.distinct c (Fin.ext h))
    have h02 : ((φ.clause c 0).2 : ℕ) ≠ ((φ.clause c 2).2 : ℕ) :=
      fun h => (by decide : (0 : Fin 3) ≠ 2) (φ.distinct c (Fin.ext h))
    have h12 : ((φ.clause c 1).2 : ℕ) ≠ ((φ.clause c 2).2 : ℕ) :=
      fun h => (by decide : (1 : Fin 3) ≠ 2) (φ.distinct c (Fin.ext h))
    simp [List.ofFn_succ, h01, h02, h12]
  · intro v hv
    rcases hv with ⟨C, hC, l, hl, rfl⟩
    rw [SetCoverThreshold.SetCover.Formula5.toCNF, List.mem_ofFn] at hC
    rcases hC with ⟨c₀, rfl⟩
    rw [List.mem_ofFn] at hl
    rcases hl with ⟨p₀, rfl⟩
    let v' : Fin φ.n := (φ.clause c₀ p₀).2
    rw [SetCoverThreshold.SetCover.Formula5.toCNF, filter_ofFn_length]
    have hcard_eq :
        (Finset.univ.filter (fun c : Fin φ.M =>
          decide (∃ l ∈ List.ofFn (fun p : Fin 3 => ((φ.clause c p).1, ((φ.clause c p).2 : ℕ))),
            l.2 = (v' : ℕ)) = true)).card =
        (Finset.univ.filter (fun cp : Fin φ.M × Fin 3 => (φ.clause cp.1 cp.2).2 = v')).card := by
      have hiff : ∀ c : Fin φ.M,
          (decide (∃ l ∈ List.ofFn (fun p : Fin 3 => ((φ.clause c p).1, ((φ.clause c p).2 : ℕ))),
            l.2 = (v' : ℕ)) = true) ↔
          ∃ p : Fin 3, (φ.clause c p).2 = v' := by
        intro c
        simp only [decide_eq_true_eq, List.mem_ofFn, exists_exists_eq_and, Fin.ext_iff]
      simp_rw [hiff]
      refine Finset.card_bij
        (fun (c : Fin φ.M) (hc : c ∈ Finset.univ.filter (fun c : Fin φ.M => ∃ p : Fin 3, (φ.clause c p).2 = v')) =>
          (c, Classical.choose ((Finset.mem_filter.mp hc).2)))
        (fun c hc => by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, Classical.choose_spec ((Finset.mem_filter.mp hc).2)⟩)
        (fun c₁ hc₁ c₂ hc₂ h => Prod.ext_iff.mp h |>.1)
        (fun cp hcp => by
          rcases cp with ⟨c, p⟩
          rw [Finset.mem_filter] at hcp
          have hc : c ∈ Finset.univ.filter (fun c : Fin φ.M => ∃ p : Fin 3, (φ.clause c p).2 = v') := by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ _, p, hcp.2⟩
          refine ⟨c, hc, Prod.ext rfl ?_⟩
          exact φ.distinct c ((Classical.choose_spec ((Finset.mem_filter.mp hc).2)).trans hcp.2.symm))
    rw [hcard_eq]
    exact φ.five v'

theorem solution (h211 : Thm211) :
    ∃ ε : ℝ, 0 < ε ∧
      GapNPHard encodeCNF (fun F => Is3CNF5 F ∧ F.Satisfiable)
        (fun F => Is3CNF5 F ∧ F ≠ [] ∧ AtMostFracSat (1 - ε) F) := by
  obtain ⟨ε, hε, hGap⟩ := SetCoverThreshold.SetCover.prop_2_1_2 (to_setCover_thm211 h211)
  refine ⟨ε, hε, ?_⟩
  intro Sym' _ _ L' hL'
  obtain ⟨f, hf_poly, hf_spec⟩ := hGap Sym' L' hL'
  refine ⟨fun x => (f x).toCNF, hf_poly, fun x => ?_⟩
  have h5 : Is3CNF5 (f x).toCNF := formula5_toCNF_is3CNF5 (f x)
  have hne : (f x).toCNF ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    rw [SetCoverThreshold.SetCover.Formula5.toCNF, List.length_ofFn] at hlen
    exact Nat.ne_of_gt (f x).M_pos hlen
  refine ⟨fun hx => ⟨h5, (hf_spec x).1 hx⟩, fun hx => ⟨h5, hne, ((hf_spec x).2 hx).2⟩⟩
