-- Prove2me | solution 1 for UpperTheory.Reformulated.B.SeriesSubgroup.XTShape_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:21:09.209561+00:00
-- url     : https://prove2.me/submissions/1a3e5a6d-6ef0-47de-a737-de46bcf96370

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvOfUnitCoeffMem
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FormalGroupCoeffMem
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SeriesSubgroup
import Theorems.Thm_Formalism_ELL_wSeriesLead
import Theorems.Thm_Formalism_ELL_wSeriesUnique
import Theorems.Thm_UpperTheory_formal_group_coeff_mem
import Theorems.Thm_UpperTheory_invOfUnit_coeff_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open PowerSeries
namespace UpperTheory.Reformulated.B.SeriesSubgroup
private lemma C_mem {R : Type} [CommRing R] (S : Subring R) {a : R} (ha : a ∈ S) :
    (C a : R⟦X⟧) ∈ ser S := fun n => by
  rw [coeff_C]
  split_ifs
  exacts [ha, S.zero_mem]
private lemma X_mem {R : Type} [CommRing R] (S : Subring R) : (X : R⟦X⟧) ∈ ser S := fun n => by
  rw [coeff_X]
  split_ifs
  exacts [S.one_mem, S.zero_mem]
private lemma inv_mem {R : Type} [CommRing R] (S : Subring R) {f : R⟦X⟧} (hf : f ∈ ser S)
    (h : constantCoeff f = 1) : invOfUnit f 1 ∈ ser S := UpperTheory.invOfUnit_coeff_mem R S f hf h
open Formalism.L2.Th1.A in
private lemma xS_const {R : Type} [CommRing R] (W : WeierstrassCurve R) :
    constantCoeff (xS W) = 1 := by
  simp [xS]
open Formalism.L2.Th1.A in
private lemma xS_mem {R : Type} [CommRing R] (S : Subring R) (W : WeierstrassCurve R)
    (h₁ : W.a₁ ∈ S) (h₂ : W.a₂ ∈ S) (h₃ : W.a₃ ∈ S) (h₄ : W.a₄ ∈ S) (h₆ : W.a₆ ∈ S) :
    xS W ∈ ser S := by
  have hw : Formalism.ELL.WFixed W (wSer W) := (Formalism.ELL.wSeriesUnique R W).choose_spec.1
  have hm := UpperTheory.formal_group_coeff_mem R S W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ (wSer W) h₁ h₂ h₃ h₄ h₆ hw.1 hw.2
  refine inv_mem S (fun n => ?_) ?_
  · rw [wU, coeff_mk]
    exact hm _
  · rw [← coeff_zero_eq_constantCoeff_apply, wU, coeff_mk]
    exact (Formalism.ELL.wSeriesLead R W _ hw).2.2.2
open Formalism.L2.Th1.A in
private lemma xPlus_mem {R : Type} [CommRing R] (S : Subring R) (W : WeierstrassCurve R)
    (h₁ : W.a₁ ∈ S) (h₂ : W.a₂ ∈ S) (h₃ : W.a₃ ∈ S) (h₄ : W.a₄ ∈ S) (h₆ : W.a₆ ∈ S)
    {x y : R} (hx : x ∈ S) (hy : y ∈ S) : xPlus W x y ∈ ser S := by
  have hs := xS_mem S W h₁ h₂ h₃ h₄ h₆
  have hX := X_mem S
  have two : (2 : R) ∈ S := ofNat_mem S 2
  have three : (3 : R) ∈ S := ofNat_mem S 3
  have hd : invOfUnit (tDen W x) 1 ∈ ser S :=
    inv_mem S (sub_mem hs (mul_mem (C_mem S hx) (pow_mem hX 2))) (by simp [tDen, xS_const])
  have hn : nS W x y ∈ ser S :=
    add_mem (sub_mem
      (mul_mem (mul_mem (C_mem S (add_mem (add_mem (sub_mem h₄ (mul_mem h₁ hy))
        (mul_mem (mul_mem two h₂) hx)) (mul_mem three (pow_mem hx 2)))) hX) hs)
      (mul_mem (C_mem S (add_mem (add_mem (mul_mem two hy) (mul_mem h₁ hx)) h₃)) (neg_mem hs)))
      (mul_mem (C_mem S (sub_mem (sub_mem (add_mem (mul_mem two h₆) (mul_mem h₄ hx))
        (mul_mem h₃ hy)) (pow_mem hx 3))) (pow_mem hX 3))
  exact add_mem (C_mem S hx) (mul_mem (mul_mem hX hn) (pow_mem hd 2))
open Formalism.L2.Th1.A in
private lemma xPlus_coeff {R : Type} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    coeff 0 (xPlus W x y) = x ∧ coeff 1 (xPlus W x y) = 2 * y + W.a₁ * x + W.a₃ ∧
      (2 * y + W.a₁ * x + W.a₃ = 0 →
        coeff 2 (xPlus W x y) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) := by
  refine ⟨by simp [xPlus], ?_, fun h => ?_⟩
  · rw [xPlus, mul_assoc, map_add, coeff_succ_X_mul, coeff_C, if_neg one_ne_zero, zero_add,
      coeff_zero_eq_constantCoeff_apply]
    simp [nS, yS, xS_const]
  · have e : xPlus W x y = C x + X ^ 2 *
        ((C (W.a₄ - W.a₁ * y + 2 * W.a₂ * x + 3 * x ^ 2) * xS W
          + C (2 * W.a₆ + W.a₄ * x - W.a₃ * y - x ^ 3) * X ^ 2) *
          invOfUnit (tDen W x) 1 ^ 2) := by
      rw [xPlus, nS, h, map_zero]
      ring
    rw [e, map_add, coeff_C, if_neg two_ne_zero, zero_add, coeff_X_pow_mul', if_pos le_rfl,
      Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
    simp only [map_mul, map_add (constantCoeff (R := R)), map_pow, constantCoeff_C, constantCoeff_X,
      xS_const, constantCoeff_invOfUnit]
    simp
    ring
end UpperTheory.Reformulated.B.SeriesSubgroup
end

set_option autoImplicit false
open PowerSeries
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.SeriesSubgroup
namespace UpperTheory.Reformulated.B.SeriesSubgroup
theorem _root_.solution : Formalism.L2.Th1.E.XTShape := by
  intro K _ _ _ W hW P _ hx hy
  obtain ⟨h₁, h₂, h₃, h₄, h₆, -⟩ := hW
  exact ⟨xPlus_mem (ball K) W h₁ h₂ h₃ h₄ h₆ hx hy, xPlus_coeff W _ _⟩
end UpperTheory.Reformulated.B.SeriesSubgroup
