-- Prove2me | solution 1 for ThreeSum.LightBlockSourceCatalog.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:36:19.944799+00:00
-- url     : https://prove2.me/submissions/df7172d1-8999-4088-b480-a85ee16dabb2

import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatch
import Definitions.Def_Submission_ThreeSum_LightSourceOccurrenceArray
import Definitions.Def_Submission_ThreeSum_BlockSourceOccurrenceOrder
import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_00da40658bb1c003
import Theorems.Thm_ThreeSum_BlockSourceOccurrenceOrder_row_coordinate
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Theorems.Thm_ThreeSum_LightBlockQuery_meets
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_banks_le_work
import Definitions.Def_WeightedCache3SUM_Alias_0d1a8110a0635644
import Definitions.Def_WeightedCache3SUM_Alias_e53bbf83b76e0442
import Definitions.Def_WeightedCache3SUM_Alias_244efc85702348f3
import Definitions.Def_WeightedCache3SUM_Alias_5f0dc31657648884
import Definitions.Def_WeightedCache3SUM_Alias_a7dfb79b11046052
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_443601c744eb157d
import Definitions.Def_WeightedCache3SUM_Alias_84a6d1c69132a490
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceCatalog
open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding LightBlockSourceBatchLayout
open BlockSourceOccurrenceOrder OutputDecodeOrder OutputDecodeRecords
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBlockSourceCatalog
namespace Procs
theorem _root_.solution {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ] {pMain : ℕ}
    (C : Procs P pMain) {μ : ℕ → ℤ} {h J cut p NL NR occ maps candidates histL histR sourceHistL sourceHistR base : ℕ}
    {shift : ℤ} (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ) (vL vR : ℕ → ℤ) (eL : Fin NL ≃ B)
    (eR : Fin NR ≃ A) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + J * (512 * h) + 12 ≤ lim.depth)
    (hcut : cut ≤ J * (512 * h)) (hocc : occ + count h J * J ≤ base)
    (hmaps : maps + 2 * (512 * h) * scheduleSize h ≤ occ) (hcandidates : candidates + scheduleSize h ≤ occ)
    (hleft : histL + LightLocalCoverSchedule.rows h * localPrime h ≤ occ)
    (hright : histR + LightLocalCoverSchedule.rows h * localPrime h ≤ occ)
    (hsourceHistL : sourceHistL + modulus h J ≤ occ) (hsourceHistR : sourceHistR + modulus h J ≤ occ)
    (hspace : space base h J cut ≤ lim.space) (hword : (word NL NR h J : ℤ) ≤ lim.word)
    (hinputL : ∀ j : Fin NL, vL j.val = b (eL j)) (hinputR : ∀ j : Fin NR, vR j.val = a (eR j))
    (hhistReadL :
      ∀ r < modulus h J, μ (sourceHistL + r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) 0 vL NL r : ℤ))
    (hhistReadR :
      ∀ r < modulus h J,
        μ (sourceHistR + r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) shift vR NR r : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Meets lim P pMain d
      [J, 512 * h, h, localPrime h, localBucketCap h, cut, modulus h J, occ, maps, candidates, histL, histR,
        sourceHistL, sourceHistR, base, downsetCap (J * (512 * h)) cut, count h J, banks base (count h J),
        stride (J * (512 * h)) cut, maskBase base (count h J) (J * (512 * h)) cut,
        bitBase base (count h J) (J * (512 * h)) cut, rowOut base (count h J) (J * (512 * h)) cut,
        work base (count h J) (J * (512 * h)) cut, scheduleSize h]
      μ (time h J cut)
      (fun _ ν =>
        Stored ν h J base cut (p : ℤ) shift B b A a ∧
          (∀ i < count h J, ∀ j < J, ν (occ + i * J + j) = ((indices (scheduleSize h) J i).getD j 0 : ℤ)) ∧
            Kept μ ν occ) :=
  by
  have hs : LightBlockSourceRetainedHost.space (work base (count h J) (J * (512 * h)) cut) h J ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hsd : LightOutputDecodeDigits.space (work base (count h J) (J * (512 * h)) cut) (count h J) ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hws : (LightBlockSourceRetainedHost.word NL NR h J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hwd : (LightOutputDecodeDigits.word (count h J) (scheduleSize h) J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  have hbase : base ≤ work base (count h J) (J * (512 * h)) cut :=
    by
    have hb := banks_le_work base (count h J) (J * (512 * h)) cut
    unfold banks at hb
    omega
  have hrunRows :=
    LightSourceOccurrenceArray.meets (d := d + 1) (μ := μ) (N := count h J) (J := J) (m := scheduleSize h) (dst := occ)
      (work := work base (count h J) (J * (512 * h)) cut) C.rows C.digits C.divide hw (by omega)
      (by exact schedule_pos h) (hocc.trans hbase) hsd hwd
  apply Meets.of_body C.main
  unfold body time
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
    | refine _root_.Light.Ends.callToThen (hrunRows _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hrunRows ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro r ν ⟨rows, kept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hcover' := hcover.of_kept kept hmaps hcandidates hleft hright
  have hhistL' :
    ∀ r < modulus h J, ν (sourceHistL + r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) 0 vL NL r : ℤ) :=
    by
    intro r hr
    exact (kept _ (by omega)).trans (hhistReadL r hr)
  have hhistR' :
    ∀ r < modulus h J,
      ν (sourceHistR + r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) shift vR NR r : ℤ) :=
    by
    intro r hr
    exact (kept _ (by omega)).trans (hhistReadR r hr)
  have hrows :
    ∀ i < count h J,
      ∀ j < J, ν (occ + i * J + j) = (occurrenceIndices (outputOccurrences (representative h J i)) j : ℤ) :=
    by
    intro i hi j hj
    rw [row_coordinate hj]
    exact rows i hi j hj
  have hrunBatch :=
    C.batch.meets (d := d + 1) (μ := ν) (cut := cut) (p := p) (shift := shift) (occ := occ) (maps := maps)
      (candidates := candidates) (histL := histL) (histR := histR) (sourceHistL := sourceHistL) (sourceHistR :=
      sourceHistR) (base := base) (count := count h J) B b A a (representative h J) vL vR eL eR hw (by omega) hcut hocc
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hs hws hinputL hinputR hhistL' hhistR' hrows
      hcover'
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
    | refine _root_.Light.Ends.callToThen (hrunBatch _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hrunBatch ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro s ν' ⟨stored, kept'⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨stored, ?_, ?_⟩
  · intro i hi j hj
    have hm := Nat.mul_le_mul_right J (show i + 1 ≤ count h J by omega)
    exact (kept' _ (by nlinarith)).trans (rows i hi j hj)
  · intro a ha
    exact (kept' a (by omega)).trans (kept a ha)
end Procs
end ThreeSum.LightBlockSourceCatalog
