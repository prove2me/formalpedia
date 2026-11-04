-- Prove2me | solution 1 for ThreeSum.LightBandPrimeSetup.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:03:33.79405+00:00
-- url     : https://prove2.me/submissions/082a6370-5b82-453d-a88e-89a23592f1d2

import Definitions.Def_Submission_ThreeSum_LightBandPrimeDepth
import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_4c7c7c4548f5a674
import Theorems.Thm_ThreeSum_LightBandPrimeConstruction_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_984b86210e82afdf
import Theorems.Thm_ThreeSum_LightBandPrimeDepth_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_7e2b05f783284e0e
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_9ba359ecf22e73cc
import Definitions.Def_WeightedCache3SUM_Alias_0f0d845b38fcc358
import Theorems.Thm_ThreeSum_LightBandWeightedScoreSlice_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_2ea73ff18fd48136
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Theorems.Thm_ThreeSum_LightPrimality_program_meets
import Theorems.Thm_ThreeSum_LightPrimeChain_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeChain_program_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_a00dee90c4e0ea45
import Theorems.Thm_ThreeSum_LightPrimePool_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_280261ae8ac7fab5
import Theorems.Thm_ThreeSum_LightWeightedScore_program_meets
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeSetup
open Light BandCandidateRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ} {a b c nA nB nC g recs M y free maxMod U : ℕ}
namespace ThreeSum.LightBandPrimeSetup
theorem _root_.solution (rs : List Record) (hw : (lim.space : ℤ) ≤ lim.word) (hy : 0 < y) (hg : 0 < g)
    (ha : a + nA ≤ free) (hb : b + nB ≤ free) (hc : c + nC ≤ free) (hrecs : recs + 4 * rs.length ≤ free)
    (hspace : space free maxMod g M y U ≤ lim.space) (hword : (word maxMod nA nB nC g rs.length M y U : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 maxMod + 10 ≤ lim.depth) (hrecords : Seg μ recs (cells rs))
    (hflag : ∀ r ∈ rs, r.flag = 0 ∨ r.flag = 1)
    (hvalid : ∀ r ∈ rs, r.flag = 1 → r.a * g ≤ nA ∧ r.b * g ≤ nB ∧ r.c * g ≤ nC) (hA : ∀ i < nA, |μ (a + i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b + i)| ≤ (U : ℤ)) (hC : ∀ i < nC, |μ (c + i)| ≤ (U : ℤ))
    (hmax : (4 * y) ^ (LightBandPrimeDepth.depth M y + 1) ≤ maxMod) :
    Meets lim program 24 d [a, b, c, nA, nB, nC, g, recs, rs.length, M, y, free] μ (time maxMod g rs.length M y U)
      (fun result ν =>
        result =
            (LightBandPrimeConstruction.modulus y nA nB nC g (fun j => μ (a + j)) (fun j => μ (b + j))
                (fun j => μ (c + j)) rs (LightBandPrimeDepth.depth M y) :
              ℤ) ∧
          SegN ν free (LightPrimePool.values y) ∧
            (∀ i ≤ LightBandPrimeDepth.depth M y,
                ν (free + 3 * y + i) =
                  (LightBandPrimeConstruction.modulus y nA nB nC g (fun j => μ (a + j)) (fun j => μ (b + j))
                      (fun j => μ (c + j)) rs i :
                    ℤ)) ∧
              Kept μ ν free) :=
  by
  have hdWord : (LightBandPrimeDepth.word M y : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hcWord : (LightBandPrimeConstruction.word maxMod nA nB nC g rs.length y U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  apply Meets.of_body (p := 24) (by rfl : program[24]? = some (body 0 23))
  unfold body time
  have hD :=
    ((LightBandPrimeDepth.program_meets (d := d + 1) (μ := μ) hy hdWord).append
          (LightBandPrimeConstruction.program.map (ReportingHostRelocation.relocate 1))).append
      [body 0 23]
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    | refine _root_.Light.Ends.callToThen (hD _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hD ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro levels μ₁ ⟨hlevels, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₁
  have hC :=
    (ReportingHostRelocation.meets
          (LightBandPrimeConstruction.program_meets (d := d + 1) (μ := μ) (a := a) (b := b) (c := c) (y := y) (levels :=
            LightBandPrimeDepth.depth M y) rs hw hy hg ha hb hc hrecs hspace hcWord (by omega) hrecords hflag hvalid hA
            hB hC hmax)
          LightBandPrimeDepth.program).append
      [body 0 23]
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    | refine _root_.Light.Ends.callToThen (hC _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hC ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlevels]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hlevels] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlevels] <;> omega)
    on_goal -1 => (rintro result ν hresult; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  exact hresult
end ThreeSum.LightBandPrimeSetup
