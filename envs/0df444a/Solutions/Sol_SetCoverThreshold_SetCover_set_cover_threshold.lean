-- Prove2me | solution 1 for SetCoverThreshold.SetCover.set_cover_threshold
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T19:54:11.855113+00:00
-- url     : https://prove2.me/submissions/10a3c083-277f-4993-9417-e13117a4bbec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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

set_option autoImplicit false
set_option linter.unusedVariables false

open CookPvsNP SetCoverThreshold.SetCover Classical

theorem solution (h211 : Thm211) (hRaz : RazRepetition)
    (hNaor : NaorPartitionSystems) (ε : ℝ) (hε : 0 < ε)
    (hA : ApproximableWithin (fun n => (1 - ε) * Real.log n)) :
    ∀ (Sym : Type) [Fintype Sym] [Nonempty Sym], CookPvsNP.NP Sym ⊆ LogLogTime Sym := by
  intro Sym _ _ L hL
  obtain ⟨ε', hε', hGap212⟩ := prop_2_1_2 h211
  obtain ⟨f, hf_poly, hf_spec⟩ := hGap212 Sym L hL
  obtain ⟨c, hc, hCovGap⟩ := scInst_cover_gap hRaz ε' hε'
  let η : ℝ := min (ε / 4) (1 / 4)
  have hη_pos : 0 < η := lt_min (by linarith) (by norm_num)
  obtain ⟨k₀, hk₀⟩ := hNaor η hη_pos
  let k : ℕ := max k₀ 2
  have hk_ge : k₀ ≤ k := le_max_left k₀ 2
  have hk2 : 2 ≤ k := le_max_right k₀ 2
  obtain ⟨m₀, F, hF_poly, hF_spec⟩ := hk₀ k hk_ge 1
  have hF_spec1 : ∀ m L_part : ℕ, m₀ ≤ m → L_part ≤ Nat.log 2 m →
      ∃ (m' d : ℕ) (P₀ : PartitionSystem m' L_part k d),
        m ≤ m' ∧ F (unaryPair m L_part) = encodeTable P₀.table ∧
          (1 - η) * k * Real.log m' ≤ d := by
    intro m L_part hm hL_part
    exact hF_spec m L_part hm (by simpa using hL_part)
  obtain ⟨A, hA_poly, n₀, hA_spec⟩ := hA
  refine scInst_gap_decide_in_LogLogTime Sym L ε ε' c hε hε' hc k m₀ n₀ hk2 F hF_poly hF_spec1
    A hA_poly f hf_poly ?_
  intro x ℓ m' d code hcode P₀ I hn₀
  obtain ⟨hCov, hYes, hNo⟩ := hCovGap (f x) ℓ k m' d code hcode (fun _ => P₀)
  obtain ⟨⟨C_low, hC_low_cov, hC_low_card⟩, hA_upper⟩ := hA_spec I hn₀ hCov
  constructor
  · intro hx
    obtain ⟨C_yes, hC_yes_cov, hC_yes_card⟩ := hYes ((hf_spec x).1 hx)
    exact ⟨C_yes, hC_yes_cov, hC_yes_card, hA_upper C_yes hC_yes_cov⟩
  · intro hd hprob hx
    have hlow := hNo η hη_pos hd hprob ((hf_spec x).2 hx) C_low hC_low_cov
    exact hlow.trans (by exact_mod_cast hC_low_card)
