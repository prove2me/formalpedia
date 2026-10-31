-- Prove2me | solution 1 for SetCoverThreshold.MaxCover.max_k_cover_threshold
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T19:44:35.951995+00:00
-- url     : https://prove2.me/submissions/613261cd-c50a-4be5-9ef0-690a47391c5a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem
import Definitions.Def_SetCoverThreshold_MaxCover_Instance
import Definitions.Def_SetCoverThreshold_MaxCover_Reduction
import Definitions.Def_SetCoverThreshold_MaxCover_Theorem53
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Theorems.Thm_SetCoverThreshold_SetCover_prop_2_1_2
import Theorems.Thm_SetCoverThreshold_MaxCover_exists_isCode
import Theorems.Thm_SetCoverThreshold_MaxCover_maxCoverInst_opt_gap
import Theorems.Thm_SetCoverThreshold_MaxCover_maxCoverInst_gap_decide_in_P
import Theorems.Thm_CookPvsNP_P_subset_NP

set_option autoImplicit false

open CookPvsNP SetCoverThreshold.MaxCover Classical

private lemma to_setCover_thm211 (h211 : SetCoverThreshold.MaxCover.Thm211) :
    SetCoverThreshold.SetCover.Thm211 := by
  rcases h211 with ⟨B, ε, hε, hGap⟩
  refine ⟨B, ε, hε, ?_⟩
  intro Sym' _ _ L' hL'
  rcases hGap Sym' L' hL' with ⟨f, hf_poly, hf_spec⟩
  refine ⟨f, hf_poly, fun x => ⟨(hf_spec x).1, fun hx => ?_⟩⟩
  rcases (hf_spec x).2 hx with ⟨hB, hne, hsat⟩
  exact ⟨hB, List.length_pos_of_ne_nil hne, hsat⟩

private def ofSetCoverFormula5 (φ : SetCoverThreshold.SetCover.Formula5) : Formula5 where
  M := φ.M
  clause c p := ((φ.clause c p).1, ((φ.clause c p).2 : ℕ))
  distinct_vars c p₁ p₂ h := φ.distinct c (Fin.ext h)
  five := by
    intro v hv
    rcases hv with ⟨c₀, p₀, rfl⟩
    let v' : Fin φ.n := (φ.clause c₀ p₀).2
    have hfilter :
        Finset.univ.filter (fun c : Fin φ.M =>
          ∃ p : Fin 3, ((φ.clause c p).1, ((φ.clause c p).2 : ℕ)).2 =
            ((φ.clause c₀ p₀).1, ((φ.clause c₀ p₀).2 : ℕ)).2) =
        Finset.univ.filter (fun c : Fin φ.M => ∃ p : Fin 3, (φ.clause c p).2 = v') := by
      ext c
      simp [v', Fin.ext_iff]
    rw [hfilter]
    refine (Finset.card_bij
      (fun (c : Fin φ.M) (hc : c ∈ Finset.univ.filter (fun c : Fin φ.M => ∃ p : Fin 3, (φ.clause c p).2 = v')) =>
        (c, Classical.choose ((Finset.mem_filter.mp hc).2)))
      (fun c hc => by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, Classical.choose_spec ((Finset.mem_filter.mp hc).2)⟩)
      (fun c₁ _ c₂ _ h => Prod.ext_iff.mp h |>.1)
      (fun cp hcp => by
        rcases cp with ⟨c, p⟩
        rw [Finset.mem_filter] at hcp
        have hc : c ∈ Finset.univ.filter (fun c : Fin φ.M => ∃ p : Fin 3, (φ.clause c p).2 = v') := by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, p, hcp.2⟩
        refine ⟨c, hc, Prod.ext rfl ?_⟩
        exact φ.distinct c ((Classical.choose_spec ((Finset.mem_filter.mp hc).2)).trans hcp.2.symm))).trans
      (φ.five v')

private lemma ofSetCoverFormula5_toCNF (φ : SetCoverThreshold.SetCover.Formula5) :
    (ofSetCoverFormula5 φ).toCNF = φ.toCNF := rfl

theorem solution (h211 : Thm211) (hRaz : RazRepetition) (ε : ℝ) (hε : 0 < ε)
    (hA : MaxCoverApproximable (1 - Real.exp (-1) + ε)) :
    P Bool = NP Bool := by
  apply Set.Subset.antisymm (P_subset_NP Bool)
  intro L hL
  obtain ⟨A, hA_poly, hA_spec⟩ := hA
  obtain ⟨ε', hε', hGap212⟩ := SetCoverThreshold.SetCover.prop_2_1_2 (to_setCover_thm211 h211)
  obtain ⟨f₀, hf₀_poly, hf₀_spec⟩ := hGap212 Bool L hL
  obtain ⟨hOptYes, hOptNo⟩ := maxCoverInst_opt_gap hRaz
  obtain ⟨k₀, hk₀⟩ := hOptNo (ε / 2) (by linarith)
  let k : ℕ := max k₀ 1
  have hk_ge : k₀ ≤ k := le_max_left k₀ 1
  have hk1 : 1 ≤ k := le_max_right k₀ 1
  obtain ⟨ℓ₀, hℓ₀⟩ := hk₀ k hk_ge ε' hε'
  obtain ⟨ℓ, code, hℓ_ge, hℓ1, hcode⟩ := exists_isCode k ℓ₀ hk1
  let f : List Bool → Formula5 := fun x => ofSetCoverFormula5 (f₀ x)
  refine maxCoverInst_gap_decide_in_P k ℓ hk1 hℓ1 code hcode ε hε A hA_poly L f hf₀_poly
    (fun x => (f₀ x).M_pos) (fun x => ⟨?_, ?_⟩)
  · intro hx
    have hsat : (f x).toCNF.Satisfiable := (hf₀_spec x).1 hx
    have hopt : opt (maxCoverInst (f x) code) = (maxCoverInst (f x) code).n :=
      hOptYes k ℓ code (f x) hsat
    have hA_low := (hA_spec (maxCoverInst (f x) code)).1
    rw [hopt] at hA_low
    exact hA_low
  · intro hx
    have hfrac : AtMostFracSat (1 - ε') (f x).toCNF := ((hf₀_spec x).2 hx).2
    have hopt : (opt (maxCoverInst (f x) code) : ℝ) ≤
        (1 - Real.exp (-1) + ε / 2) * ((maxCoverInst (f x) code).n : ℝ) :=
      hOptNo (ε / 2) (by linarith) |> fun _ => hℓ₀ ℓ hℓ_ge code hcode (f x) hfrac
    have hA_high : ((A (encode (maxCoverInst (f x) code))).length : ℝ) ≤
        (opt (maxCoverInst (f x) code) : ℝ) := by
      exact_mod_cast (hA_spec (maxCoverInst (f x) code)).2
    exact hA_high.trans hopt
