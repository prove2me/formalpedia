-- Prove2me | solution 1 for ThreeSum.LightSpanCatalogBlock.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:48:42.424353+00:00
-- url     : https://prove2.me/submissions/daedddb3-5675-4868-a268-cee51ba61036

import Definitions.Def_Submission_ThreeSum_LightSpanAxpy
import Definitions.Def_Submission_ThreeSum_LightSpanCatalogStep
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSpanAxpy_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
set_option autoImplicit false
open ThreeSum ThreeSum.LightSpanCatalogBlock
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSpanCatalogBlock
theorem _root_.solution {pMain pAxpy pMulAdd pDivide src n rowBase dst J a p d : ℕ}
    (hmain : P[pMain]? = some (body pAxpy)) (haxpy : P[pAxpy]? = some (LightSpanAxpy.body pMulAdd))
    (hmul : P[pMulAdd]? = some (LightPrimeCoefficient.mulAddBody pDivide))
    (hdivide : P[pDivide]? = some LightSmallDivide.body) (μ : ℕ → ℤ) (f : ℕ → ℕ → ℕ) (row : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + J * n ≤ dst) (hrow : rowBase + J ≤ dst)
    (hdst : dst + J * n ≤ lim.space) (hp : 0 < p) (ha : a < p) (hword : (LightPrimeCoefficient.word p : ℤ) ≤ lim.word)
    (hcontrols : ((n + J + 16 : ℕ) : ℤ) ≤ lim.word) (hf : ∀ k < n, ∀ i < J, f k i < p) (hr : ∀ i < J, row i < p)
    (hread : ∀ k < n, ∀ i < J, μ (src + J * k + i) = (f k i : ℤ)) (hreadRow : ∀ i < J, μ (rowBase + i) = (row i : ℤ))
    (hd : d + 3 ≤ lim.depth) :
    Meets lim P pMain d [src, n, rowBase, dst, J, a, p] μ (time J p n)
      (fun _ ν =>
        (∀ k < n, ∀ i < J, ν (dst + J * k + i) = LightSpanAxpy.values (f k) row a p i) ∧ SameOutside μ ν dst (J * n)) :=
  by
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for (Inv μ src n rowBase dst J a p f row) n (LightSpanAxpy.time J p + 120) ?start ?round ?done ?bound (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, μ, ?_, SameOn.refl, ?_⟩
    · simp [update_frame_setLocal]
      change frame [(src : ℤ), n, rowBase, dst, J, a, p, 0] = frame ([(src : ℤ), n, rowBase, dst, J, a, p, 0] ++ [0])
      exact (frame_append_zeros _ 1).symm
    · intro t ht; omega
  case round =>
    rintro k _ hk _ ⟨result, ν, rfl, H, hrdone⟩
    have hkn : J * k + J ≤ J * n :=
      by
      have hh := Nat.mul_le_mul_left J (show k + 1 ≤ n by omega)
      simpa only [Nat.mul_add, Nat.mul_one] using hh
    have hRead : ∀ i < J, ν (src + J * k + i) = (f k i : ℤ) := by
      intro i hi
      rw [H _ (Or.inl (by omega)), hread k hk i hi]
    have hRowRead : ∀ i < J, ν (rowBase + i) = (row i : ℤ) := by intro i hi; rw [H _ (Or.inl (by omega)), hreadRow i hi]
    have hc :=
      LightSpanAxpy.meets (d := d + 1) (src := src + J * k) (rowBase := rowBase) (dst := dst + J * k) (J := J) haxpy
        hmul hdivide ν (f k) row hw (by omega) (by omega) (by omega) hp ha hword (hf k hk) hr hRead hRowRead (by omega)
    unfold roundBody
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
      | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSpanAxpy.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightSpanAxpy.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSpanAxpy.time] <;> omega)
      on_goal -1 => (rintro out ξ ⟨hNew, hOutside⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, out, ξ, ?_, ?_, ?_⟩
    · simp [update_frame_setLocal]
    · intro x hx
      rw [hOutside x (by rcases hx with hx | hx <;> omega), H x hx]
    · intro t ht i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | he
      · have htk : J * t + J ≤ J * k :=
          by
          have hh := Nat.mul_le_mul_left J (show t + 1 ≤ k by omega)
          simpa only [Nat.mul_add, Nat.mul_one] using hh
        rw [hOutside _ (Or.inl (by omega))]
        exact hrdone t ht i hi
      · subst t
        exact hNew i hi
  case done =>
    rintro _ _ ⟨result, ν, rfl, H, hdone⟩
    exact ⟨hdone, H⟩
  case bound =>
    rintro k _ hk _ ⟨result, ν, rfl, H, hdone⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightSpanCatalogBlock
