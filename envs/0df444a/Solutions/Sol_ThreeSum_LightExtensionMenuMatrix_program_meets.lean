-- Prove2me | solution 1 for ThreeSum.LightExtensionMenuMatrix.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:33:38.587802+00:00
-- url     : https://prove2.me/submissions/470c87d2-aaf5-415b-a062-e157bfa188c3

import Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyTable
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedMatrix
import Definitions.Def_Submission_ThreeSum_LightSignedCoefficientMatrix
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuMatrix
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightCoefficientDecode_program_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyCell_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyCell_program_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyTable_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyTable_program_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientSearch_program_meets
import Theorems.Thm_ThreeSum_LightExtensionSeedMatrix_meets
import Theorems.Thm_ThreeSum_LightExtensionSeedRow_meets
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Theorems.Thm_ThreeSum_LightOutputDecodeDigits_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Theorems.Thm_ThreeSum_LightPairSearch_meets
import Theorems.Thm_ThreeSum_LightPairSearch_program_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
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
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionMenuMatrix
open Light
set_option maxHeartbeats 5000000
set_option maxRecDepth 6000
attribute [local instance] ThreeSum.LightExtensionMenuMatrix._p2m_local_instance_68cd7abcc2_10
variable {lim : Limits}
namespace ThreeSum.LightExtensionMenuMatrix
theorem _root_.solution {ctx q table logical physical J depth : ℕ} (C : LightExtensionQuotientPredicate.Layout)
    (μ : ℕ → ℤ) (f : ℕ → ℕ) (mul : ℕ → ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth + 9 < lim.depth)
    (hp : 1 < C.p) (hq : 0 < q) (H : Seg μ ctx (LightExtensionQuotientPredicate.header C)) (hctx : ctx + 10 ≤ table)
    (hpow : C.powers + (2 * C.dim + 1) ≤ table) (hmod : C.modulus + (C.dim + 1) ≤ table)
    (htable : table + q * q ≤ logical) (hlogical : logical + q * q * (J + 2) ≤ physical)
    (hphysical : physical + q * q * (J + 2) ≤ C.a) (hab : C.a + C.dim ≤ C.b) (hbh : C.b + C.dim ≤ C.h)
    (hh : C.h + C.dim ≤ C.remainder) (hr : C.remainder + 2 * C.dim ≤ C.productWork)
    (hprod : C.productWork + 2 * C.dim ≤ C.sumWork) (hspace : C.sumWork + 2 * C.dim ≤ lim.space)
    (hpowRead : ∀ i ≤ 2 * C.dim, μ (C.powers + i) = ((C.p ^ i : ℕ) : ℤ))
    (hfRead : ∀ i < C.dim + 1, μ (C.modulus + i) = (f i : ℤ)) (hfBound : ∀ i < C.dim + 1, f i < C.p)
    (hword : (LightExtensionMultiplyTable.word q ctx C.p C.dim C.powers C.a C.b : ℤ) ≤ lim.word)
    (hcellWord : (LightExtensionMultiplyCell.word C q ctx : ℤ) ≤ lim.word)
    (hseedWord : (LightExtensionSeedMatrix.word (J + 2) q C.p : ℤ) ≤ lim.word) (hmul : ∀ x < q, ∀ y < q, mul x y < q)
    (hspec :
      ∀ a < q,
        ∀ b < q,
          let z :=
            LightPairSearch.first
              (LightPairSearch.goodCode q
                (LightExtensionQuotientSearch.good C (LightExtensionQuotientPredicate.digits C.p a)
                  (LightExtensionQuotientPredicate.digits C.p b) f))
              (q * q)
          0 < z ∧ z ≤ q * q ∧ (z - 1) % q = mul a b) :
    Meets lim program 19 depth [q, ctx, C.p, C.dim, C.powers, C.a, C.b, table, logical, physical, J] μ (time C q J)
      (fun _ ν =>
        (∀ r < q * q,
            ∀ i < J + 2,
              ν (physical + r * (J + 2) + i) =
                (LightExtensionSeedMatrix.value mul q C.p r (TernarySignedLayout.offset J i) : ℤ)) ∧
          Kept μ ν table) :=
  by
  have hqWord : ((q * q : ℕ) : ℤ) ≤ lim.word := by unfold LightExtensionSeedMatrix.word at hseedWord; omega
  have hJWord : ((J + 2 : ℕ) : ℤ) ≤ lim.word := by unfold LightExtensionSeedMatrix.word at hseedWord; omega
  have hpWord : (C.p : ℤ) ≤ lim.word := by unfold LightExtensionSeedMatrix.word at hseedWord; omega
  have hc :=
    (LightExtensionMultiplyTable.program_meets C μ f mul hw (by omega) hp hq H hctx hpow hmod (by omega) hab hbh hh hr
          hprod hspace hpowRead hfRead hfBound hword hcellWord hmul hspec).append
      extra
  apply Meets.of_body (show program[19]? = some (body 14 16 18) from rfl)
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
    | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro X μ₁ ⟨tableValues, keep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightExtensionSeedMatrix.meets (depth := depth + 1) (table := table) (q := q) (p := C.p) (dst := logical)
              (len := J + 2) (show program[16]? = some (LightExtensionSeedMatrix.body 15 2 3) from rfl)
              (show program[15]? = some (LightExtensionSeedRow.body 2) from rfl)
              (show program[2]? = some (LightRadixDigit.body 3) from rfl)
              (show program[3]? = some LightSmallDivide.body from rfl) μ₁ mul hw (by omega) hq (by omega) htable
              (by omega) tableValues hmul hseedWord)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightExtensionSeedMatrix.meets (depth := depth + 1) (table := table) (q := q) (p := C.p) (dst := logical)
            (len := J + 2) (show program[16]? = some (LightExtensionSeedMatrix.body 15 2 3) from rfl)
            (show program[15]? = some (LightExtensionSeedRow.body 2) from rfl)
            (show program[2]? = some (LightRadixDigit.body 3) from rfl)
            (show program[3]? = some LightSmallDivide.body from rfl) μ₁ mul hw (by omega) hq (by omega) htable
            (by omega) tableValues hmul hseedWord)
          ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro Y μ₂ ⟨seedValues, keep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  let coeff := fun r i => (LightExtensionSeedMatrix.value mul q C.p r i : ℤ)
  have coeffBound (r : ℕ) (hr : r < q * q) (i : ℕ) (hi : i < J + 2) : |coeff r i| ≤ (C.p : ℤ) :=
    by
    change |((LightExtensionSeedMatrix.value mul q C.p r i : ℕ) : ℤ)| ≤ (C.p : ℤ)
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    unfold LightExtensionSeedMatrix.value
    exact_mod_cast (Nat.mod_lt (LightExtensionSeedRow.trajectory mul (r / q) (r % q) i) (by omega)).le
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightSignedCoefficientMatrix.meets (depth := depth + 1) (src := logical) (dst := physical) (rows := q * q)
              (J := J) (U := C.p) (show program[18]? = some (LightSignedCoefficientMatrix.body 17) from rfl)
              (show program[17]? = some LightSignedCoefficientLayout.body from rfl) μ₂ coeff hw (by omega) hlogical
              (by omega) seedValues coeffBound hpWord hqWord hJWord)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightSignedCoefficientMatrix.meets (depth := depth + 1) (src := logical) (dst := physical) (rows := q * q)
            (J := J) (U := C.p) (show program[18]? = some (LightSignedCoefficientMatrix.body 17) from rfl)
            (show program[17]? = some LightSignedCoefficientLayout.body from rfl) μ₂ coeff hw (by omega) hlogical
            (by omega) seedValues coeffBound hpWord hqWord hJWord)
          ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro Z ν ⟨values, keep₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨values, ?_⟩
  intro a ha
  exact (keep₃ a (Or.inl (by omega))).trans ((keep₂ a (Or.inl (by omega))).trans (keep₁ a ha))
end ThreeSum.LightExtensionMenuMatrix
