-- Prove2me | solution 1 for OddOrder.BG.AppC.FieldNormalizerData.right_component_of_step4_sigma_inr_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:24:31.517772+00:00
-- url     : https://prove2.me/submissions/96be1f0a-c49e-451c-aebb-eaa67d55c248

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_LemmaC3_Setup.lean
--   OddOrder/BG/AppC_LemmaC3_ScalarCalculus.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_FrobeniusBasics
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ConjugateLine
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Setup
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ScalarCalculus

-- ===== OddOrder/BG/AppC_LemmaC3_Setup.lean =====
namespace OddOrder.BG.AppC

open scoped Pointwise

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

/-- The transported element `s` lies in the transported additive kernel `P`. -/
theorem s_mem_P (data : FieldNormalizerData p q G) :
    data.s ∈ data.P := by
  rw [← data.sigma_P_eq_P]
  refine ⟨primeLineGenerator p q, ?_, rfl⟩
  dsimp [primeLineGenerator, NormSet.normOneFrobeniusKernel]
  exact ⟨Multiplicative.ofAdd (1 : GaloisField p q), rfl⟩

/-- Integer powers of `s` remain in `P`. -/
theorem s_zpow_mem_P (data : FieldNormalizerData p q G)
    (n : ℤ) :
    data.s ^ n ∈ data.P :=
  data.P.zpow_mem data.s_mem_P n

end FieldNormalizerData

end OddOrder.BG.AppC

-- ===== OddOrder/BG/AppC_LemmaC3_ScalarCalculus.lean =====
namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

/-- BG Appendix C, Lemma C.3 Step 4 "mod `P`" bridge in a neutral form: if a
word `s^m · σ(inr w) · s^r` is written in Step 1 normal form `u₁ s₁ v₁`, then the
right component is `w = u₁ v₁`.  This is the reusable right-projection step behind
both the forward and backward `k = 3` `(C.5)` equations. -/
theorem _root_.solution
    (data : FieldNormalizerData p q G)
    (m r : ℤ) (w u₁ v₁ : NormSet.normOneUnits p q) (c : ZMod p)
    (hdec : data.s ^ m *
          data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q)) :
    w = u₁ * v₁ := by
  have hmP : data.s ^ m ∈ data.P := data.s_zpow_mem_P m
  rw [← data.sigma_P_eq_P] at hmP
  rcases hmP with ⟨pm, hpmP, hpm⟩
  have hrP : data.s ^ r ∈ data.P := data.s_zpow_mem_P r
  rw [← data.sigma_P_eq_P] at hrP
  rcases hrP with ⟨pr, hprP, hpr⟩
  have hpm_right : SemidirectProduct.rightHom pm = 1 := by
    rcases hpmP with ⟨x, rfl⟩
    simp
  have hpr_right : SemidirectProduct.rightHom pr = 1 := by
    rcases hprP with ⟨x, rfl⟩
    simp
  have hline_right :
      SemidirectProduct.rightHom (primeLineElement p q c) = 1 := by
    simp [primeLineElement]
  have hσ :
      data.sigma (pm * (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) * pr) =
        data.sigma
          ((SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
            primeLineElement p q c * SemidirectProduct.inr v₁) := by
    calc
      data.sigma (pm * (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) * pr) =
          data.s ^ m *
              data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) *
            data.s ^ r := by
        simp [map_mul, hpm, hpr]
      _ = data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
            data.sigma (primeLineElement p q c) *
              data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q) := hdec
      _ = data.sigma
          ((SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
            primeLineElement p q c * SemidirectProduct.inr v₁) := by
        simp [map_mul]
  have hH := data.sigma_injective hσ
  have hright := congrArg (SemidirectProduct.rightHom :
      NormSet.normOneFrobeniusGroup p q →* NormSet.normOneUnits p q) hH
  simpa [map_mul, hpm_right, hpr_right, hline_right, mul_assoc] using hright

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
