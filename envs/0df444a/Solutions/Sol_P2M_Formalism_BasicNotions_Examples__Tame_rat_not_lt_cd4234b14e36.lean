-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__Tame_rat_not_lt_cd4234b14e36
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:46:54.200426+00:00
-- url     : https://prove2.me/submissions/a024c246-b59a-4aac-86b7-ce8c176f5a4d

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsTameGen
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.Tame
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
namespace Formalism.BasicNotions.Examples₂.Tame
theorem _root_.solution {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) (y : Ω) (hy : y ≠ 0) (N : ℕ) (hN : 0 < N)
    (hfix : (σ ^ N) y = y) : ¬ A.valuation (σ y) < A.valuation y := by
  intro h
  have step : ∀ j : ℕ, A.valuation ((σ ^ j) (σ y)) < A.valuation ((σ ^ j) y) := fun j => by
    have h1 : A.valuation (σ y / y) < 1 := by
      rw [map_div₀, div_lt_one₀ (zero_lt_iff.mpr (by simpa using hy))]; exact h
    have h2 := (valuation_apply_lt_one_iff (pow_mem hσ j) (σ y / y)).mpr h1
    rwa [map_div₀, map_div₀, div_lt_one₀ (zero_lt_iff.mpr
      ((Valuation.ne_zero_iff _).mpr ((map_ne_zero (σ ^ j)).mpr hy)))] at h2
  have all : ∀ j : ℕ, A.valuation ((σ ^ (j + 1)) y) < A.valuation y := fun j => by
    induction j with
    | zero => simpa using h
    | succ j ih =>
      refine lt_trans ?_ ih
      rw [pow_succ σ (j + 1), AlgEquiv.mul_apply]
      exact step (j + 1)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have := all j
  rw [hfix] at this
  exact lt_irrefl _ this
end Formalism.BasicNotions.Examples₂.Tame
