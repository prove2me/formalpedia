-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedController.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:16:54.718566+00:00
-- url     : https://prove2.me/submissions/cae04425-b43e-45f2-9f13-aa50c09de062

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedController
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedController_program_length
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_meets
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_pick_le
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_pick_pos_iff
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScore_libraries_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScore_lift_span
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScore_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScore_spanAppend_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScore_wanted_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScore_withCollision_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScore_withDivision_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScore_withWanted_length
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScore.libraries_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScore.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScore.spanAppend_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScore.wanted_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScore.withCollision_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScore.withDivision_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScore.withWanted_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedController.program_length
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum
  WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedController
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedController
theorem _root_.solution {lim : Limits}
    {menu J catalog catalogRows p power Bmatrix Bold Bnew nB Cmatrix Cold Cnew nC Omatrix Oold Onew nO positions wanted
      work hashWork hist header leftTagged rightTagged leftWeights rightWeights tensor countOutput quadScratch
      quadPowers potentialColumns potentialPowers flags scoreB scoreC scorePaired prefixLength R S K d n U dB dC dP tB
      tC tP newSpan seedTime spanTime : ℕ}
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ) (μ : ℕ → ℤ) (flag fB fC fP : ℕ → ℤ)
    (I : ℕ → (ℕ → ℤ) → Prop) (Ready Final : (ℕ → ℤ) → Prop) (hw : (lim.space : ℤ) ≤ lim.word)
    (hFlags : flags + n ≤ lim.space) (hBs : scoreB + n ≤ lim.space) (hCs : scoreC + n ≤ lim.space)
    (hPs : scorePaired + n ≤ lim.space) (hWord : (LightTernaryRowSelector.word n U dB dC dP tB tC tP : ℤ) ≤ lim.word)
    (hLen : J + 2 ≤ lim.space)
    (hRow :
      menu +
          (LightTernaryRowSelector.pick (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n - 1) *
            (J + 2) ≤
        lim.space)
    (hd : d < lim.depth) (hstart : I 0 μ)
    (hstep :
      ∀ i < n,
        ∀ ν,
          I i ν →
            Meets lim (LightWeightedGlobalSeedScore.program p R S K raws words maps xl yl zl xr yr zr)
              LightWeightedGlobalSeedScore.entry (d + 1)
              (LightWeightedGlobalSeedScore.args menu i J catalog catalogRows p power Bmatrix Bold Bnew nB Cmatrix Cold
                Cnew nC Omatrix Oold Onew nO positions wanted work hashWork hist header leftTagged rightTagged
                leftWeights rightWeights tensor countOutput quadScratch quadPowers potentialColumns potentialPowers
                flags scoreB scoreC scorePaired prefixLength)
              ν seedTime (fun _ ξ => I (i + 1) ξ))
    (hread :
      ∀ ν,
        I n ν →
          (∀ i < n, ν (flags + i) = flag i ∧ |flag i| ≤ 1) ∧
            (∀ i < n, ν (scoreB + i) = fB i ∧ |fB i| ≤ U) ∧
              (∀ i < n, ν (scoreC + i) = fC i ∧ |fC i| ≤ U) ∧ (∀ i < n, ν (scorePaired + i) = fP i ∧ |fP i| ≤ U))
    (hexist : ∃ i < n, LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP i)
    (hselected :
      ∀ ν,
        I n ν →
          Meets lim (LightWeightedGlobalSeedScore.program p R S K raws words maps xl yl zl xr yr zr)
            LightWeightedGlobalSeedScore.entry (d + 1)
            (LightWeightedGlobalSeedScore.args menu
              (LightTernaryRowSelector.pick (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n - 1) J
              catalog catalogRows p power Bmatrix Bold Bnew nB Cmatrix Cold Cnew nC Omatrix Oold Onew nO positions
              wanted work hashWork hist header leftTagged rightTagged leftWeights rightWeights tensor countOutput
              quadScratch quadPowers potentialColumns potentialPowers flags scoreB scoreC scorePaired prefixLength)
            ν seedTime (fun _ ξ => Ready ξ))
    (hspan :
      ∀ ν,
        Ready ν →
          Meets lim LightStoredSpan.program 1 (d + 1)
            [catalog, catalogRows,
              menu +
                (LightTernaryRowSelector.pick (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n - 1) *
                  (J + 2),
              newSpan, J, p]
            ν spanTime (fun _ ξ => Final ξ)) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) entry d
      (args
        (LightWeightedGlobalSeedScore.args menu 0 J catalog catalogRows p power Bmatrix Bold Bnew nB Cmatrix Cold Cnew
          nC Omatrix Oold Onew nO positions wanted work hashWork hist header leftTagged rightTagged leftWeights
          rightWeights tensor countOutput quadScratch quadPowers potentialColumns potentialPowers flags scoreB scoreC
          scorePaired prefixLength)
        n dB dC dP tB tC tP newSpan)
      μ (time n seedTime spanTime)
      (fun r ν =>
        r = (LightTernaryRowSelector.pick (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n : ℤ) ∧
          Final ν) :=
  by
  let good := LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP
  let chosen := LightTernaryRowSelector.pick good n
  let argv :=
    args
      (LightWeightedGlobalSeedScore.args menu 0 J catalog catalogRows p power Bmatrix Bold Bnew nB Cmatrix Cold Cnew nC
        Omatrix Oold Onew nO positions wanted work hashWork hist header leftTagged rightTagged leftWeights rightWeights
        tensor countOutput quadScratch quadPowers potentialColumns potentialPowers flags scoreB scoreC scorePaired
        prefixLength)
      n dB dC dP tB tC tP newSpan
  have hcpos : 0 < chosen := (LightTernaryRowSelector.pick_pos_iff good n).mpr hexist
  have hcle : chosen ≤ n := LightTernaryRowSelector.pick_le good n
  have hchosenExpand :
    LightTernaryRowSelector.pick (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n = chosen := rfl
  have hnWord : (n : ℤ) ≤ lim.word := by omega
  have hcWord : (chosen : ℤ) ≤ lim.word := by omega
  have hRow' : menu + (chosen - 1) * (J + 2) ≤ lim.space := hRow
  have hrowWord : ((menu + (chosen - 1) * (J + 2) : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hRow).trans hw
  have hprodWord : ((chosen - 1 : ℕ) : ℤ) * ((J : ℤ) + 2) ≤ lim.word :=
    by
    have hprod : (chosen - 1) * (J + 2) ≤ lim.space := by omega
    exact_mod_cast (Int.ofNat_le.mpr hprod).trans hw
  have hprodNonneg : 0 ≤ ((chosen - 1 : ℕ) : ℤ) * ((J : ℤ) + 2) := by positivity
  have hprodNonnegFull :
    0 ≤
      ((LightTernaryRowSelector.pick (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n - 1 : ℕ) : ℤ) *
        ((J : ℤ) + 2) :=
    by positivity
  have hprodWordFull :
    ((LightTernaryRowSelector.pick (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n - 1 : ℕ) : ℤ) *
        ((J : ℤ) + 2) ≤
      lim.word :=
    by simpa only [chosen, good] using hprodWord
  have hrowWordFull :
    (menu : ℤ) +
        ((LightTernaryRowSelector.pick (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n - 1 : ℕ) : ℤ) *
          ((J : ℤ) + 2) ≤
      lim.word :=
    by exact_mod_cast (Int.ofNat_le.mpr hRow).trans hw
  have hrowIntWord : (menu : ℤ) + ((chosen - 1 : ℕ) : ℤ) * ((J : ℤ) + 2) ≤ lim.word := by exact_mod_cast hrowWord
  have hlenWord : ((J : ℤ) + 2) ≤ lim.word := by exact_mod_cast (Int.ofNat_le.mpr hLen).trans hw
  have hmain : (program p R S K raws words maps xl yl zl xr yr zr)[entry]? = some body :=
    by
    simp only [entry, LightWeightedGlobalSeedScore.entry, program, Nat.reduceAdd]
    rw [List.getElem?_append_right (by rw [LightWeightedGlobalSeedScore.program_length] <;> decide)]
    rw [LightWeightedGlobalSeedScore.program_length]
    rfl
  apply Meets.of_body hmain
  change Ends _ _ _ _ ⟨frame argv, μ⟩ _ _
  unfold body time
  refine
    Ends.pieceThen
      (Ends.for (T := n * (seedTime + 100) + 50) (Q := Inv argv I n) (Inv argv I) n (seedTime + 80) ?start ?round ?done
        ?bound)
      ?after (hT := by
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
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, μ, ?_, hstart⟩
    simp only [update_frame_setLocal]
    congr 1
    simp only [argv, args, LightWeightedGlobalSeedScore.args, setLocal]
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro i _ hi _ ⟨ret, ν, rfl, hI⟩
    have hcall := (hstep i hi ν hI).append [LightTernaryRowSelector.body, body]
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
      | refine _root_.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, argv, args,
              LightWeightedGlobalSeedScore.args, seedArgs, LightWeightedGlobalSeedScore.entry]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [argv, args, LightWeightedGlobalSeedScore.args, seedArgs, LightWeightedGlobalSeedScore.entry] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, argv, args, LightWeightedGlobalSeedScore.args,
              seedArgs, LightWeightedGlobalSeedScore.entry] <;> omega)
      on_goal -1 => (rintro r ξ hnext; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp [argv, args, LightWeightedGlobalSeedScore.args, setLocal], r, ξ, ?_, hnext⟩
    simp [argv, args, LightWeightedGlobalSeedScore.args, update_frame_setLocal]
  case done => intro σ _ hI; exact hI
  case bound =>
    rintro i _ hi _ ⟨ret, ν, rfl, hI⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, argv, args, LightWeightedGlobalSeedScore.args] <;> omega)
  case after =>
    rintro σ ⟨ret, ν, rfl, hI⟩
    obtain ⟨hflag, hb, hc, hp⟩ := hread ν hI
    have hsel :=
      (LightTernaryRowSelector.meets (d := d + 1)
        (by
          unfold program
          rw [List.getElem?_append_right (by rw [LightWeightedGlobalSeedScore.program_length] <;> decide)]
          rw [LightWeightedGlobalSeedScore.program_length]
          rfl : (program p R S K raws words maps xl yl zl xr yr zr)[177]? = some LightTernaryRowSelector.body) ν flag
        fB fC fP hw hFlags hBs hCs hPs hflag hb hc hp hWord)
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
      | refine _root_.Light.Ends.callToThen (hsel _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hsel ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, argv, args,
              LightWeightedGlobalSeedScore.args, LightWeightedGlobalSeedScore.entry, chosen, good]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [argv, args, LightWeightedGlobalSeedScore.args, LightWeightedGlobalSeedScore.entry, chosen, good] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, argv, args, LightWeightedGlobalSeedScore.args,
              LightWeightedGlobalSeedScore.entry, chosen, good] <;> omega)
      on_goal -1 => (rintro picked ξ ⟨hpicked, hξ⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ξ
    have hpositive : (0 : ℤ) < picked := by rw [hpicked]; exact_mod_cast hcpos
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.iteIffThen ((0 : ℤ) < picked) (fun hyes => ?_) (fun hno => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, argv, args,
              LightWeightedGlobalSeedScore.args]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [argv, args, LightWeightedGlobalSeedScore.args] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, argv, args,
              LightWeightedGlobalSeedScore.args] <;> omega)
      all_goals
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
    · focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        refine _root_.Light.Ends.setToThen (chosen - 1 : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, argv, args,
                LightWeightedGlobalSeedScore.args, chosen, good, hpicked]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [argv, args, LightWeightedGlobalSeedScore.args, chosen, good, hpicked] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, argv, args,
                LightWeightedGlobalSeedScore.args, chosen, good, hpicked] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      have hs := (hselected ν hI).append [LightTernaryRowSelector.body, body]
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
        | refine _root_.Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen hs ?_ ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, argv, args,
                LightWeightedGlobalSeedScore.args, seedArgs, LightWeightedGlobalSeedScore.entry, chosen, good]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [argv, args, LightWeightedGlobalSeedScore.args, seedArgs, LightWeightedGlobalSeedScore.entry, chosen,
                  good] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, argv, args,
                LightWeightedGlobalSeedScore.args, seedArgs, LightWeightedGlobalSeedScore.entry, chosen, good] <;> omega)
        on_goal -1 => (rintro r ξ hr; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      have hsp := LightWeightedGlobalSeedScore.lift_span p R S K raws words maps xl yl zl xr yr zr (hspan ξ hr)
      have hsp' := hsp.append [LightTernaryRowSelector.body, body]
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
        | refine _root_.Light.Ends.callToThen (hsp' _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen hsp' ?_ ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, argv, args,
                LightWeightedGlobalSeedScore.args, seedArgs, chosen, good]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [argv, args, LightWeightedGlobalSeedScore.args, seedArgs, chosen, good] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, argv, args,
                LightWeightedGlobalSeedScore.args, seedArgs, chosen, good] <;> omega)
        on_goal -1 => (rintro r ζ hfinal; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        refine _root_.Light.Ends.setToThen chosen ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, argv, args,
                LightWeightedGlobalSeedScore.args, seedArgs, chosen, good, hpicked]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [argv, args, LightWeightedGlobalSeedScore.args, seedArgs, chosen, good, hpicked] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, argv, args,
                LightWeightedGlobalSeedScore.args, seedArgs, chosen, good, hpicked] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      exact ⟨by simp [argv, args, LightWeightedGlobalSeedScore.args, setLocal, chosen, good], hfinal⟩
    · exact (hno hpositive).elim
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedController
