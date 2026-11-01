-- Prove2me | solution 2 for SetCoverThreshold.SetCover.set_cover_threshold
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T12:02:11.039722+00:00
-- url     : https://prove2.me/submissions/3e2cddff-c6db-41d9-8308-b5dc18709c88
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem
import Definitions.Def_SetCoverThreshold_SetCover_PartitionSystem
import Definitions.Def_SetCoverThreshold_SetCover_Instance
import Definitions.Def_SetCoverThreshold_SetCover_Reduction
import Definitions.Def_SetCoverThreshold_SetCover_Theorem44
import Theorems.Thm_SetCoverThreshold_SetCover_prop_2_1_2
import Theorems.Thm_SetCoverThreshold_SetCover_scInst_cover_gap
import Theorems.Thm_SetCoverThreshold_SetCover_scInst_gap_decide_in_LogLogTime

open SetCoverThreshold.SetCover CookPvsNP

theorem solution (h211 : Thm211) (hRaz : RazRepetition)
    (hNaor : NaorPartitionSystems) (ε : ℝ) (hε : 0 < ε)
    (hA : ApproximableWithin (fun n => (1 - ε) * Real.log n)) :
    ∀ (Sym : Type) [Fintype Sym] [Nonempty Sym], CookPvsNP.NP Sym ⊆ LogLogTime Sym := by
  intro Sym _ _ L hL
  rcases prop_2_1_2 h211 with ⟨ε', hε', hHard⟩
  rcases scInst_cover_gap hRaz ε' hε' with ⟨c, hc, hsc⟩
  have hη : 0 < min (ε / 4) (1 / 4) := by positivity
  rcases hNaor (min (ε / 4) (1 / 4)) hη with ⟨k₀, hk₀⟩
  set k := max k₀ 2
  have hk_ge_k₀ : k₀ ≤ k := le_max_left k₀ 2
  have hk : 2 ≤ k := le_max_right k₀ 2
  rcases hk₀ k hk_ge_k₀ 1 with ⟨m₀, F, hF, hNaor1⟩
  have hNaorSpec : ∀ m L_part : ℕ, m₀ ≤ m → L_part ≤ Nat.log 2 m →
      ∃ (m' d : ℕ) (P₀ : PartitionSystem m' L_part k d),
        m ≤ m' ∧ F (unaryPair m L_part) = encodeTable P₀.table ∧
          (1 - min (ε / 4) (1 / 4)) * k * Real.log m' ≤ d := by
    intro m L_part hm hL_part
    apply hNaor1 m L_part hm
    simpa using hL_part
  rcases hA with ⟨A, hA_poly, n₀, hA_spec⟩
  rcases hHard Sym L hL with ⟨f, hf_poly, hf_gap⟩
  refine scInst_gap_decide_in_LogLogTime Sym L ε ε' c hε hε' hc k m₀ n₀ hk F hF hNaorSpec A hA_poly f hf_poly ?_
  intro x ℓ m' d code hcode P₀ _ hn₀
  have hsc_inst := hsc (f x) ℓ k m' d code hcode (fun _ => P₀)
  have hcov : (scInst (f x) code (fun _ => P₀)).Coverable := hsc_inst.1
  have hA_inst := hA_spec (scInst (f x) code (fun _ => P₀)) hn₀ hcov
  constructor
  · intro hxL
    have hsat : (f x).toCNF.Satisfiable := (hf_gap x).1 hxL
    rcases hsc_inst.2.1 hsat with ⟨C, hC_cov, hC_card⟩
    exact ⟨C, hC_cov, hC_card, hA_inst.2 C hC_cov⟩
  · intro hd h2ℓ hxnotL
    have hnosat : AtMostFracSat (1 - ε') (f x).toCNF := (hf_gap x).2 hxnotL
    rcases hA_inst.1 with ⟨C, hC_cov, hC_le_A⟩
    have hlow := hsc_inst.2.2 (min (ε / 4) (1 / 4)) hη hd h2ℓ hnosat C hC_cov
    have hC_le_A' : (C.card : ℝ) ≤ ((A (scInst (f x) code (fun _ => P₀)).encode).length : ℝ) := by
      exact_mod_cast hC_le_A
    linarith
