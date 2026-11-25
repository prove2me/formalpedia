-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_of_exactDivide_polyOfDiffs_7209b2ce9cfd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:53:15.122246+00:00
-- url     : https://prove2.me/submissions/b74dbb05-8ccc-4670-ae72-d2610b01f4bc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_HilbEventuallyPolyQualified
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_isMultiHomog_X_410350c0267f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_isMultiHomogIdeal_colon_X_8d27cbe0e333
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_isMultiHomogIdeal_sup_span_e78dfa2b1c24
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_hilbFn_eq_zero_of_block_4ff705798091
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_eventually_sub_9d8fc527ac76
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_eval_shift_c0b41e6fe1b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_cast_single_504a09db5994

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace HilbEventuallyPoly
theorem _root_.solution (h1 : HilbExactDivide.Statement.{u})
    (h2 : PolyOfDiffs.Statement) : HilbEventuallyPoly.Statement.{u} := by
  intro F _ K _ _ ι _ I hI
  refine IsNoetherian.induction
    (P := fun J : Ideal (MRing ι F) => IsMultiHomogIdeal J → ∃ p, EventuallyPoly (hilbFn J) p)
    (fun J ih hJ => ?_) I hI
  by_cases hA : ∃ v : Σ k, ι k, (X v : MRing ι F) ∉ J ∧
      J.colon (Ideal.span {(X v : MRing ι F)}) ≠ J
  ·
    obtain ⟨v, hvJ, hne⟩ := hA
    have hle : J ≤ J.colon (Ideal.span {(X v : MRing ι F)}) := fun f hf => by
      rw [Submodule.mem_colon_span_singleton, smul_eq_mul]
      exact Ideal.mul_mem_right _ J hf
    have hlt2 : J < J ⊔ Ideal.span {(X v : MRing ι F)} :=
      lt_of_le_of_ne le_sup_left fun h =>
        hvJ (h ▸ Ideal.mem_sup_right (Ideal.subset_span rfl))
    obtain ⟨p1, hp1⟩ := ih _ (lt_of_le_of_ne hle (Ne.symm hne)) (isMultiHomogIdeal_colon_X hJ v)
    obtain ⟨p2, hp2⟩ := ih _ hlt2 (isMultiHomogIdeal_sup_span hJ (isMultiHomog_X v))
    have hex := h1 F K ι J hJ _ (X v) (isMultiHomog_X v)
    rw [cast_single] at hex
    refine ⟨bind₁ (fun j => X j - C (((Pi.single v.1 1 : K → ℤ) j : ℤ) : ℚ)) p1 + p2, ?_⟩
    filter_upwards [eventually_sub hp1 (Pi.single v.1 1), hp2] with m hm1 hm2
    have hz := hex m
    rw [map_add, ← eval_shift, ← hm1, ← hm2]
    have hz' : hilbFn J m = hilbFn (J.colon (Ideal.span {(X v : MRing ι F)})) (m - Pi.single v.1 1)
        + hilbFn (J ⊔ Ideal.span {(X v : MRing ι F)}) m := by linarith
    rw [hz']
    push_cast
    rfl
  ·
    have hA' : ∀ v : Σ k, ι k, (X v : MRing ι F) ∉ J →
        J.colon (Ideal.span {(X v : MRing ι F)}) = J := fun v hv => by
      by_contra hne
      exact hA ⟨v, hv, hne⟩
    have hdiff : ∀ k, ∃ q : MvPolynomial K ℚ,
        EventuallyPoly (diffStep (Pi.single k 1) (hilbFn J)) q := by
      intro k
      by_cases hk : ∃ i, (X ⟨k, i⟩ : MRing ι F) ∉ J
      · obtain ⟨i, hi⟩ := hk
        have hlt : J < J ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι F)} :=
          lt_of_le_of_ne le_sup_left fun h =>
            hi (h ▸ Ideal.mem_sup_right (Ideal.subset_span rfl))
        obtain ⟨q, hq⟩ := ih _ hlt (isMultiHomogIdeal_sup_span hJ (isMultiHomog_X ⟨k, i⟩))
        refine ⟨q, ?_⟩
        have hex := h1 F K ι J hJ _ (X ⟨k, i⟩) (isMultiHomog_X ⟨k, i⟩)
        rw [cast_single, hA' _ hi] at hex
        filter_upwards [hq] with m hm
        rw [← hm]
        unfold diffStep
        rw [hex m]
      · simp only [not_exists, not_not] at hk
        refine ⟨0, ?_⟩
        rw [EventuallyPoly, Filter.eventually_atTop]
        refine ⟨Pi.single k 2, fun m hm => ?_⟩
        have hmk : 2 ≤ m k := by simpa using hm k
        unfold diffStep
        rw [hilbFn_eq_zero_of_block k hk m (by omega),
          hilbFn_eq_zero_of_block k hk _ (by simp only [Pi.sub_apply, Pi.single_eq_same]; omega)]
        simp
    choose q hq using hdiff
    obtain ⟨p, -, hp⟩ := h2 K (hilbFn J) (Finset.univ.sup fun k => (q k).totalDegree + 1)
      fun k => ⟨q k, Or.inr (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (Finset.le_sup (f := fun k => (q k).totalDegree + 1) (Finset.mem_univ k))), hq k⟩
    exact ⟨p, hp⟩
end HilbEventuallyPoly
end GroundTheory.Heights₂.Heights.FieldNumbers
