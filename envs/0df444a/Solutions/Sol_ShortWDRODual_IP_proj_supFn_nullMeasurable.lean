-- Prove2me | solution 1 for ShortWDRODual.IP.proj_supFn_nullMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:17:12.896047+00:00
-- url     : https://prove2.me/submissions/b149561d-228b-43e6-ad55-ea85b53f0b5e

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.IP
open scoped ENNReal

theorem solution {X : Type*} [MeasurableSpace X] (Phat : Measure X)
    [IsProbabilityMeasure Phat] (hProj : Proj Phat) (φ : X × X → EReal) (hφ : DiagDomFun φ)
    (hφtop : ∀ p, φ p ≠ ⊤) :
    NullMeasurable (ShortWDRODual.Legendre.supFn φ) Phat := by
  refine measurable_of_Ioi (δ := NullMeasurableSpace X Phat)
    (f := (ShortWDRODual.Legendre.supFn φ : NullMeasurableSpace X Phat → EReal)) (fun α => ?_)
  change NullMeasurableSet (ShortWDRODual.Legendre.supFn φ ⁻¹' Set.Ioi α) Phat
  have hpre : ShortWDRODual.Legendre.supFn φ ⁻¹' Set.Ioi α = Prod.fst '' {p | α < φ p} := by
    ext xh
    simp only [Set.mem_preimage, Set.mem_Ioi, ShortWDRODual.Legendre.supFn, lt_iSup_iff,
      Set.mem_image, Set.mem_setOf_eq, Prod.exists, exists_and_right, exists_eq_right]
  rw [hpre]
  exact hProj _ ⟨measurableSet_lt measurable_const hφ.1,
    fun xh x h => lt_of_lt_of_le h (hφ.2 xh x)⟩
