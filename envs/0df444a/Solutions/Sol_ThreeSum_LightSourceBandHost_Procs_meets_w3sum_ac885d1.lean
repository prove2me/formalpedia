-- Prove2me | solution 1 for ThreeSum.LightSourceBandHost.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:12:23.126296+00:00
-- url     : https://prove2.me/submissions/32752c26-8c6f-4123-9e8d-f3ef480e480a

import Definitions.Def_Submission_ThreeSum_LightSourceBandPair
import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_LightSourceBandHost
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_00da40658bb1c003
import Theorems.Thm_ThreeSum_BlockSourceEncoding_modulus_pos
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_fecb00c51dea7534
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Theorems.Thm_ThreeSum_LightBlockQuery_meets
import Definitions.Def_WeightedCache3SUM_Alias_0d1a8110a0635644
import Definitions.Def_WeightedCache3SUM_Alias_e53bbf83b76e0442
import Theorems.Thm_ThreeSum_LightBlockSourceCatalog_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_244efc85702348f3
import Definitions.Def_WeightedCache3SUM_Alias_5f0dc31657648884
import Definitions.Def_WeightedCache3SUM_Alias_a7dfb79b11046052
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_443601c744eb157d
import Definitions.Def_WeightedCache3SUM_Alias_84a6d1c69132a490
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_f318d8b49c9fc733
import Definitions.Def_WeightedCache3SUM_Alias_2b9c97c844160a97
import Theorems.Thm_ThreeSum_LightCoverSelect_Procs_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_meets
import Definitions.Def_WeightedCache3SUM_Alias_7c6295bca57f98dc
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_f8e3ce9eb3f48862
import Definitions.Def_WeightedCache3SUM_Alias_2ae6d2b4167e20c4
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightExplicitSum_meets
import Theorems.Thm_ThreeSum_LightHashHistogram_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightLeafSum_meets
import Definitions.Def_WeightedCache3SUM_Alias_d5eaa25d4585cc6b
import Definitions.Def_WeightedCache3SUM_Alias_da105011ac4dcdd4
import Definitions.Def_WeightedCache3SUM_Alias_04fc0611b78e7896
import Definitions.Def_WeightedCache3SUM_Alias_a64b3be7ea8b7b19
import Definitions.Def_WeightedCache3SUM_Alias_82db098e10427a83
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_2ab790e73b946b9f
import Definitions.Def_WeightedCache3SUM_Alias_c287aeb916bf4368
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Definitions.Def_WeightedCache3SUM_Alias_d98593d0ef804094
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Definitions.Def_WeightedCache3SUM_Alias_9176929b72776235
import Definitions.Def_WeightedCache3SUM_Alias_e3ff37f6db941441
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_7aba91d69ad782cd
import Definitions.Def_WeightedCache3SUM_Alias_4b224c9ee30c137c
import Definitions.Def_WeightedCache3SUM_Alias_dc0a334da481a327
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_meets
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_meets
import Theorems.Thm_ThreeSum_LightSignedLeafCell_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9b8d9638683d951
import Theorems.Thm_ThreeSum_LightSignedLeafTable_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_f253b70ba796e513
import Definitions.Def_WeightedCache3SUM_Alias_f8ab785e9a2d0c30
import Definitions.Def_WeightedCache3SUM_Alias_ec1662cc9a5130f8
import Definitions.Def_WeightedCache3SUM_Alias_30a2b7a89dd0955f
import Definitions.Def_WeightedCache3SUM_Alias_27ed780ce9327add
import Definitions.Def_WeightedCache3SUM_Alias_8826bf5763f0492d
import Definitions.Def_WeightedCache3SUM_Alias_e1f50da99510448e
import Definitions.Def_WeightedCache3SUM_Alias_366cab045a6bd6be
import Definitions.Def_WeightedCache3SUM_Alias_15941a0ec739ebe6
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_2968a7144f4e39f0
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
import Theorems.Thm_ThreeSum_LightSourceBuild_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_bff01fd4b2900a53
import Definitions.Def_WeightedCache3SUM_Alias_8f9b8fc511f535d5
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Definitions.Def_WeightedCache3SUM_Alias_4bb45babfe810a30
import Definitions.Def_WeightedCache3SUM_Alias_5dbf6f5b0c2deb9c
import Definitions.Def_WeightedCache3SUM_Alias_a076d5b93ecac4d9
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Definitions.Def_WeightedCache3SUM_Alias_ce5ff1e60c39fd21
import Definitions.Def_WeightedCache3SUM_Alias_e80b8f80e26e0eba
import Definitions.Def_WeightedCache3SUM_Alias_d4ec36c7dcd9fa6e
import Theorems.Thm_ThreeSum_LightSourceStages_Procs_meets
import Theorems.Thm_ThreeSum_LightSourceStages_ZetaProcs_meets
import Definitions.Def_WeightedCache3SUM_Alias_b9dca0c4b48e489f
import Theorems.Thm_ThreeSum_LightSparseQuery_meets
import Definitions.Def_WeightedCache3SUM_Alias_5c1e55e66cf081b7
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_66dd70707634c020
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80
import Definitions.Def_WeightedCache3SUM_Alias_de9d37b5900d1a92
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5
import Definitions.Def_WeightedCache3SUM_Alias_470e48753c64c7fc
import Theorems.Thm_ThreeSum_SourceBandBankLayout_At_of_kept
import Theorems.Thm_ThreeSum_SourceBandData_At_of_kept
import Definitions.Def_WeightedCache3SUM_Alias_78e5c19e1b3827d6
import Theorems.Thm_ThreeSum_SourceBandPairData_ordered
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandHost
open Light GlobalEncoding BlockSourceEncoding LocalCoverBounds SubsetAddress
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBandHost
namespace Procs
theorem _root_.solution {pMain : ℕ} (C : Procs P pMain) {μ : ℕ → ℤ}
    {srcL headL srcR headR shiftCell base NL NR g p h J cut U D maps candidates histL histR : ℕ} {shift : ℤ}
    (fL fR : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + J * (512 * h) + 15 ≤ lim.depth) (hg : 0 < g)
    (hp : 0 < p) (hcut : cut ≤ J * (512 * h)) (hsrcL : srcL + NL ≤ base) (hsrcR : srcR + NR ≤ base)
    (hheadL : headL + 2 ≤ base) (hheadR : headR + 2 ≤ base) (hshiftCell : shiftCell < base)
    (hmaps : maps + 2 * (512 * h) * scheduleSize h ≤ base) (hcandidates : candidates + scheduleSize h ≤ base)
    (hleft : histL + LightLocalCoverSchedule.rows h * localPrime h ≤ base)
    (hright : histR + LightLocalCoverSchedule.rows h * localPrime h ≤ base)
    (hspace : space base NL NR g p h J cut U D ≤ lim.space) (hword : (word NL NR g p h J U D : ℤ) ≤ lim.word)
    (hshift : |shift| ≤ (D : ℤ)) (hlenL : μ headL = (NL : ℤ)) (hlenR : μ headR = (NR : ℤ))
    (hcountL : μ (headL + 1) = (BandPartition.size NL g : ℤ)) (hcountR : μ (headR + 1) = (BandPartition.size NR g : ℤ))
    (hshiftRead : μ shiftCell = shift) (hreadL : ∀ j < NL, μ (srcL + j) = fL j) (hreadR : ∀ j < NR, μ (srcR + j) = fR j)
    (hvaluesL : ∀ j < NL, |fL j| ≤ (U : ℤ)) (hvaluesR : ∀ j < NR, |fR j| ≤ (U : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Meets lim P pMain d
      [J, 512 * h, h, localPrime h, localBucketCap h, cut, modulus h J, maps, candidates, histL, histR, srcL, headL,
        srcR, headR, g, p, shiftCell, base, downsetCap (J * (512 * h)) cut, LightBlockSourceCatalog.count h J,
        scheduleSize h, SourceBandBankLayout.span h J cut]
      μ (time NL NR g p h J cut U D)
      (fun r ν =>
        r = (finish base NL NR g h J cut : ℤ) ∧
          SourceBandPairData.Stored ν fL fR base NL NR g p (modulus h J) shift ∧
            SourceBandBankData.Stored ν fL fR (bankHeader base NL NR g h J) NL NR g h J cut
                (occurrenceBase base NL NR g h J) (p : ℤ) shift ∧
              Kept μ ν base) :=
  by
  have hm := modulus_pos h J
  have hsPair : LightSourceBandPair.space base NL NR g p (modulus h J) U D ≤ lim.space := (le_max_left _ _).trans hspace
  have hsBanks : LightSourceBandBanks.space (bankHeader base NL NR g h J) NL NR g h J cut ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hwPair : (LightSourceBandPair.word NL NR g p (modulus h J) U D : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hwBanks : (LightSourceBandBanks.word NL NR h J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  have hsDigits := (le_max_left _ _).trans hsBanks
  have hsEnd : finish base NL NR g h J cut ≤ lim.space :=
    by
    unfold LightOutputDecodeDigits.space at hsDigits
    unfold finish
    omega
  have hheader : bankHeader base NL NR g h J + 5 ≤ finish base NL NR g h J cut := Nat.le_add_right _ _
  have hprod : (LightBlockSourceCatalog.count h J : ℤ) * (J : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show LightBlockSourceCatalog.count h J * J ≤ lim.space by unfold bankHeader at hheader; omega) :
          (LightBlockSourceCatalog.count h J : ℤ) * (J : ℤ) ≤ lim.space).trans
      hw
  have hprodNonneg : (0 : ℤ) ≤ (LightBlockSourceCatalog.count h J : ℤ) * (J : ℤ) := by positivity
  have hheaderAddr :
    (occurrenceBase base NL NR g h J : ℤ) + (LightBlockSourceCatalog.count h J : ℤ) * (J : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show bankHeader base NL NR g h J ≤ lim.space by omega) :
          (occurrenceBase base NL NR g h J : ℤ) + (LightBlockSourceCatalog.count h J : ℤ) * (J : ℤ) ≤ lim.space).trans
      hw
  have ho := SourceBandPairData.ordered base NL NR g (modulus h J)
  have hbaseOcc : base ≤ occurrenceBase base NL NR g h J :=
    by
    unfold SourceBandPairData.leftBase at ho
    change base ≤ SourceBandPairData.next base NL NR g (modulus h J)
    omega
  apply Meets.of_body C.main
  unfold body time
  have hrunPair :=
    C.pair.meets (d := d + 1) (μ := μ) (srcL := srcL) (headL := headL) (srcR := srcR) (headR := headR) (shiftCell :=
      shiftCell) (base := base) (NL := NL) (NR := NR) (g := g) (p := p) (m := modulus h J) (U := U) (D := D) (shift :=
      shift) fL fR hw (by omega) hg hp hm hsrcL hsrcR hheadL hheadR hshiftCell hsPair hwPair hshift hlenL hlenR hcountL
      hcountR hshiftRead hreadL hreadR hvaluesL hvaluesR
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
    | refine _root_.Light.Ends.callToThen (hrunPair _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hrunPair ?_ ?_ ?_ ?_
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
    on_goal -1 =>
      (rintro rPair ν₁ ⟨hrPair, pairData, keptPair⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hrPair' : rPair = (occurrenceBase base NL NR g h J : ℤ) := hrPair
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (bankHeader base NL NR g h J : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, bankHeader, hrPair']
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [bankHeader, hrPair'] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, bankHeader, hrPair'] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have cover₁ := hcover.of_kept keptPair hmaps hcandidates hleft hright
  have hrunBanks :=
    C.banks.meets (d := d + 1) (μ := ν₁) (base := bankHeader base NL NR g h J) (occ := occurrenceBase base NL NR g h J)
      pairData hw (by omega) hg hcut le_rfl le_rfl (hmaps.trans hbaseOcc) (hcandidates.trans hbaseOcc)
      (hleft.trans hbaseOcc) (hright.trans hbaseOcc) hsBanks hwBanks cover₁
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
    | refine _root_.Light.Ends.callToThen (hrunBanks _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hrunBanks ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrPair']
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hrPair'] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrPair'] <;> omega)
    on_goal -1 =>
      (rintro rBanks ν₂ ⟨hrBanks, bankData, keptBanks⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hrBanks' : rBanks = (finish base NL NR g h J cut : ℤ) := hrBanks
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (finish base NL NR g h J cut : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrBanks']
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hrBanks'] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrBanks'] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  exact
    ⟨rfl, pairData.of_kept hm keptBanks le_rfl, bankData, fun a ha => (keptBanks a (by omega)).trans (keptPair a ha)⟩
end Procs
end ThreeSum.LightSourceBandHost
