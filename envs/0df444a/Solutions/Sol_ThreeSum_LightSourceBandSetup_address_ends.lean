-- Prove2me | solution 1 for ThreeSum.LightSourceBandSetup.address_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:50:08.429518+00:00
-- url     : https://prove2.me/submissions/551fce94-a705-4add-a7ef-8daf7b179b7e

import Definitions.Def_Submission_ThreeSum_LightSourceBandBatch
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_244efc85702348f3
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_27ed780ce9327add
import Definitions.Def_WeightedCache3SUM_Alias_15941a0ec739ebe6
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_2968a7144f4e39f0
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
import Theorems.Thm_ThreeSum_LightSourceBuild_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Definitions.Def_WeightedCache3SUM_Alias_ce5ff1e60c39fd21
import Theorems.Thm_ThreeSum_LightSourceStages_Procs_meets
import Theorems.Thm_ThreeSum_LightSourceStages_ZetaProcs_meets
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5
import Theorems.Thm_ThreeSum_SourceBandLayout_data_le_hist
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandSetup
open Light BandPartition SourceBandLayout
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBandSetup
theorem _root_.solution {pBatch : ℕ} (C : LightSourceBandBatch.Procs P pBatch) {μ : ℕ → ℤ} {src n g p m base U D K : ℕ}
    {shift : ℤ} (f : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 5 < lim.depth) (hg : 0 < g) (hp : 0 < p)
    (hm : 0 < m) (hsrc : src + n ≤ base) (hK : K = size n g)
    (hspace : LightSourceResidues.space (work base n g m) p U D ≤ lim.space) (hshift : |shift| ≤ (D : ℤ))
    (hword : (LightSourceBandStep.word n g p m U D : ℤ) ≤ lim.word) (hread : ∀ j < n, μ (src + j) = f j)
    (hvalues : ∀ j < n, |f j| ≤ (U : ℤ)) :
    Ends lim P d (addressBody pBatch) ⟨frame [src, n, g, p, m, shift, base, cap n g, K], μ⟩ (addressTime n g p m U D)
      (fun σ =>
        σ.loc 0 = (work base n g m : ℤ) ∧
          (∀ i < size n g, SourceBandData.At σ.mem f base n g p m shift i) ∧ Kept μ σ.mem base) :=
  by
  subst K
  have hwork : work base n g m ≤ lim.space := by unfold LightSourceResidues.space at hspace; omega
  have hdata : data base n g ≤ work base n g m := data_le_hist base n g m (size n g)
  have hcapN : cap n g ≤ n := min_le_left _ _
  have hcapG : cap n g ≤ g := min_le_right _ _
  have hdataAddr : base + 6 * size n g ≤ lim.space := hdata.trans hwork
  have hcountprod : (6 : ℤ) * (size n g : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show 6 * size n g ≤ lim.space by omega) : (6 : ℤ) * (size n g : ℤ) ≤ lim.space).trans hw
  have hstrideN : 3 * m + 1 + 2 * cap n g ≤ LightSourceBandStep.word n g p m U D :=
    by
    unfold LightSourceBandStep.word LightSourceResidues.word
    omega
  have hstrideZ : (3 : ℤ) * (m : ℤ) + 1 + 2 * (cap n g : ℤ) ≤ lim.word :=
    (by exact_mod_cast hstrideN :
          (3 : ℤ) * (m : ℤ) + 1 + 2 * (cap n g : ℤ) ≤ (LightSourceBandStep.word n g p m U D : ℤ)).trans
      hword
  have h32 : (32 : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr
          (show 32 ≤ LightSourceBandStep.word n g p m U D by
            unfold LightSourceBandStep.word LightSourceResidues.word
            omega)).trans
      hword
  have hworkProd : (size n g : ℤ) * (stride n g m : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show size n g * stride n g m ≤ lim.space by unfold work hist at hwork; omega) :
          (size n g : ℤ) * (stride n g m : ℤ) ≤ lim.space).trans
      hw
  have hworkProdN : (0 : ℤ) ≤ (size n g : ℤ) * (stride n g m : ℤ) := by positivity
  have hworkAddr : (data base n g : ℤ) + (size n g : ℤ) * (stride n g m : ℤ) ≤ lim.word :=
    (by exact_mod_cast hwork : (data base n g : ℤ) + (size n g : ℤ) * (stride n g m : ℤ) ≤ lim.space).trans hw
  unfold addressBody addressTime
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (data base n g : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, data]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [data] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, data] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (stride n g m : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, stride]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [stride] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, stride] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (work base n g m : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, work, hist]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [work, hist] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, work, hist] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hrun :=
    C.meets (d := d + 1) (μ := μ) (src := src) (n := n) (g := g) (p := p) (m := m) (base := base) (U := U) (D := D)
      (shift := shift) f hw (by omega) hg hp hm hsrc hspace hshift hword hread hvalues
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
    | refine _root_.Light.Ends.callToThen (hrun _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hrun ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro r ν ⟨stored, kept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (work base n g m : ℕ) ?_ ?_ ?_
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
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  exact ⟨rfl, stored, kept⟩
end ThreeSum.LightSourceBandSetup
