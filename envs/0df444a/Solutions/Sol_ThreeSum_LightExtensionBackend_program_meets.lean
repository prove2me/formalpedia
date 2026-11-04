-- Prove2me | solution 1 for ThreeSum.LightExtensionBackend.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:41:06.317081+00:00
-- url     : https://prove2.me/submissions/156f0eca-4dbe-4952-ac95-80b171968566

import Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuMatrix
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuSemantics
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightExtensionBackend
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightArgumentTable_meets
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightCoefficientDecode_program_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorSearch_program_meets
import Theorems.Thm_ThreeSum_LightExtensionFieldMultiply_actual_quotient_spec
import Theorems.Thm_ThreeSum_LightExtensionMenuMatrix_program_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyCell_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyCell_program_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyTable_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyTable_program_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientSearch_program_meets
import Theorems.Thm_ThreeSum_LightExtensionSeedMatrix_meets
import Theorems.Thm_ThreeSum_LightExtensionSeedRow_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_program_length
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_setup_meets
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightNaturalDot_meets
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Theorems.Thm_ThreeSum_LightOutputDecodeDigits_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Theorems.Thm_ThreeSum_LightPairSearch_meets
import Theorems.Thm_ThreeSum_LightPairSearch_program_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_LightPolynomialProductArray_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
import Theorems.Thm_ThreeSum_LightPolynomialQuotientCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeAddArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Theorems.Thm_ThreeSum_LightSignedCoefficientLayout_meets
import Theorems.Thm_ThreeSum_LightSignedCoefficientMatrix_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_meets
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_encodedMul_lt
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicCandidate_degree
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightIrreducibleFinder.program_length
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionBackend
open Light TernaryExtensionEncoding
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
attribute [local instance] ThreeSum.LightExtensionBackend._p2m_local_instance_a49b488cb7_11
variable {lim : Limits}
namespace ThreeSum.LightExtensionBackend
theorem _root_.solution (F : LightExtensionFactorPredicate.Layout) [Fact F.p.Prime]
    {q fctx ctx table logical physical J a b h r prod sum T depth : ℕ} (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : depth + 13 < lim.depth) (B : Budget lim F q fctx ctx table logical physical J a b h r prod sum T)
    (hq : q = F.p ^ F.dim) :
    Meets lim program 37 depth
      [F.p, F.dim, q, F.powers, F.target, fctx, F.left, F.right, ctx, table, logical, physical, a, b, h, r, prod, sum,
        J]
      μ (time F q J a b h r prod sum T)
      (fun z ν =>
        ∃ c < q,
          z = (c + 1 : ℕ) ∧
            Irreducible (monicOfCode (p := F.p) F.dim c) ∧
              (∀ s < q * q,
                  ∀ i < J + 2,
                    ν (physical + s * (J + 2) + i) =
                      (LightExtensionSeedMatrix.value (encodedMul (modulusMonic F c)) q F.p s
                          (TernarySignedLayout.offset J i) :
                        ℤ)) ∧
                Kept μ ν F.powers) :=
  by
  let C := quotientLayout F a b h r prod sum
  have hpow := B.finder.powersTarget
  have hdim := B.finder.dimpos
  have hp := B.finder.primeBase
  have hqpos := B.finder.qpos
  have htarget := B.targetCtx
  have hctx := B.ctxTable
  have ht := B.tableLogical
  have hl := B.logicalPhysical
  have hph := B.physicalA
  have hab := B.aB
  have hbh := B.bH
  have hhr := B.hR
  have hrp := B.rProduct
  have hps := B.productSum
  have hspace := B.space
  have hcontrols := B.finder.controls
  have hcontrolsWord := B.seedWord
  unfold LightExtensionSeedMatrix.word at hcontrolsWord
  have hfind :=
    ((ReportingHostRelocation.meets
          (LightIrreducibleFinder.setup_meets F (depth := depth + 1) μ hw (by omega) B.finder hq)
          LightExtensionMenuMatrix.program)).append
      [LightArgumentTable.stores 0 10, body]
  apply Meets.of_body (show program[37]? = some body from rfl)
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (hfind _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hfind ?_ ?_ ?_ ?_
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
      (rintro chosen μ₁ ⟨c, hc, hchosen, hirred, targetValues, powerValues, keep₁⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hcOneWord : ((c + 1 : ℕ) : ℤ) ≤ lim.word := by omega
  have hhead :=
    LightArgumentTable.meets (P := program) (depth := depth + 1) (proc := 36) (N := 10) rfl
      (LightExtensionQuotientPredicate.header C) rfl ctx μ₁ hw (by omega)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (hhead _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hhead ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, C, quotientLayout,
            LightExtensionQuotientPredicate.header]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [C, quotientLayout, LightExtensionQuotientPredicate.header] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, C, quotientLayout,
            LightExtensionQuotientPredicate.header] <;> omega)
    on_goal -1 =>
      (rintro headerResult μ₂ ⟨hheaderResult, headerValues, keep₂⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have pows₂ (i : ℕ) (hi : i ≤ 2 * F.dim) : μ₂ (F.powers + i) = ((F.p ^ i : ℕ) : ℤ) := by
    rw [keep₂ _ (Or.inl (by omega)), powerValues i hi]
  have target₂ (i : ℕ) (hi : i < F.dim + 1) : μ₂ (F.target + i) = (codeDigits (p := F.p) (c + q) i : ℤ) := by
    rw [keep₂ _ (Or.inl (by omega)), targetValues i (by omega)]
  have hdegree : (monicOfCode (p := F.p) F.dim c).natDegree = F.dim := monicCandidate_degree _
  have hm : monicOfCode (p := F.p) (monicOfCode (p := F.p) F.dim c).natDegree c = monicOfCode (p := F.p) F.dim c := by
    rw [hdegree]
  have hspec :=
    LightExtensionFieldMultiply.actual_quotient_spec (p := F.p) (f := monicOfCode (p := F.p) F.dim c) C rfl hdegree.symm
      (modulusMonic F c) (by omega) (by simpa [hdegree, ← hq] using hc) hm
  have hspec' :
    ∀ x < q,
      ∀ y < q,
        let z :=
          LightPairSearch.first
            (LightPairSearch.goodCode q
              (LightExtensionQuotientSearch.good C (LightExtensionQuotientPredicate.digits C.p x)
                (LightExtensionQuotientPredicate.digits C.p y) (codeDigits (p := F.p) (c + q))))
            (q * q)
        0 < z ∧ z ≤ q * q ∧ (z - 1) % q = encodedMul (modulusMonic F c) x y :=
    by simpa [hdegree, ← hq] using hspec
  have hmul : ∀ x < q, ∀ y < q, encodedMul (modulusMonic F c) x y < q :=
    by
    intro x hx y hy
    simpa [hdegree, ← hq] using encodedMul_lt (modulusMonic F c) x y
  have targetBound (i : ℕ) (_hi : i < F.dim + 1) : codeDigits (p := F.p) (c + q) i < F.p := Nat.mod_lt _ (by omega)
  have hmenu :=
    (LightExtensionMenuMatrix.program_meets (depth := depth + 1) C μ₂ (codeDigits (p := F.p) (c + q))
          (encodedMul (modulusMonic F c)) hw (by omega) hp hqpos headerValues hctx (by dsimp [C, quotientLayout]; omega)
          (by dsimp [C, quotientLayout]; omega) ht hl hph hab hbh hhr hrp hps hspace pows₂ target₂ targetBound
          B.tableWord B.cellWord B.seedWord hmul hspec').append
      (LightIrreducibleFinder.program.map (ReportingHostRelocation.relocate 20) ++
        [LightArgumentTable.stores 0 10, body])
  have hmenu' :
    Meets lim program 19 (depth + 1) [q, ctx, F.p, F.dim, F.powers, a, b, table, logical, physical, J] μ₂
      (LightExtensionMenuMatrix.time C q J)
      (fun _ ν =>
        (∀ s < q * q,
            ∀ i < J + 2,
              ν (physical + s * (J + 2) + i) =
                (LightExtensionSeedMatrix.value (encodedMul (modulusMonic F c)) q F.p s
                    (TernarySignedLayout.offset J i) :
                  ℤ)) ∧
          Kept μ₂ ν table) :=
    by
    have hlen : LightExtensionMenuMatrix.program.length = 20 := rfl
    simpa only [program, prefixProgram, ReportingHostRelocation.program, hlen, List.append_assoc, C,
      quotientLayout] using hmenu
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (hmenu' _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hmenu' ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, C, quotientLayout]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [C, quotientLayout] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, C, quotientLayout] <;> omega)
    on_goal -1 => (rintro out ν ⟨values, keep₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (c + 1 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hchosen, C, quotientLayout]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hchosen, C, quotientLayout] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hchosen, C, quotientLayout] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨c, hc, by simp, hirred, values, ?_⟩
  intro x hx
  exact (keep₃ x (by omega)).trans ((keep₂ x (Or.inl (by omega))).trans (keep₁ x hx))
end ThreeSum.LightExtensionBackend
