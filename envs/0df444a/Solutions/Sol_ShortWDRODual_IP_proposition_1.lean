-- Prove2me | solution 1 for ShortWDRODual.IP.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:08:42.71644+00:00
-- url     : https://prove2.me/submissions/d8aff48e-b366-43f0-8d17-5bc8ce8dbd3c

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting
import Theorems.Thm_ShortWDRODual_IP_proj_selStar_imp_IP
import Theorems.Thm_ShortWDRODual_IP_IP_imp_proj
import Theorems.Thm_ShortWDRODual_IP_IP_imp_selStar

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.IP
open scoped ENNReal

theorem solution {X : Type*} [MeasurableSpace X] (Phat : Measure X)
    [IsProbabilityMeasure Phat] :
    (∀ φ : X × X → EReal, DiagDomFun φ → (∀ p, φ p ≠ ⊤) → ShortWDRODual.Legendre.IP Phat φ) ↔
      (Proj Phat ∧ SelStar Phat) :=
  ⟨fun h => ⟨IP_imp_proj Phat h, IP_imp_selStar Phat h⟩,
    fun h => proj_selStar_imp_IP Phat h.1 h.2⟩
