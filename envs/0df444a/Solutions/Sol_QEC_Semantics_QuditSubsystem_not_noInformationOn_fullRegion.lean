-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.not_noInformationOn_fullRegion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:19:54.770958+00:00
-- url     : https://prove2.me/submissions/0b9a284d-e7cb-411a-8f62-1bb54b1f28a6

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Theorems.Thm_QEC_Semantics_QuditSubsystem_fullRegion_extension_surjective
import Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_iff_allLocalScalarCompression
import Theorems.Thm_QEC_Semantics_QuditSubsystem_scalarCompression_iff_detectableOn


set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.QuditSubsystem
open scoped BigOperators
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] (q : J → Nat)
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (C : QuantumCode (Qudit.QuditRegister q))
    (hq : ∀ j, 0 < q j) (x y : Qudit.QuditRegister q)
    (hx : x ∈ C.carrier) (hy : y ∈ C.carrier)
    (hxx : inner Complex x x = 1) (hyy : inner Complex y y = 1)
    (hxy : inner Complex x y = 0) : ¬ NoInformationOn C (fullRegion q) := by
  intro hinfo
  obtain ⟨E, hE⟩ := fullRegion_extension_surjective q hq
    (InnerProductSpace.rankOne Complex x x).toLinearMap
  have hs := (noInformationOn_iff_allLocalScalarCompression C (fullRegion q)).mp hinfo E
  rw [hE] at hs
  obtain ⟨c, hc⟩ := (scalarCompression_iff_detectableOn _ _).mp hs
  have h0 := hc x hx x hx
  have h1 := hc y hy y hy
  have hc0 : (1 : Complex) = c := by
    change inner Complex x (inner Complex x x • x) = c * inner Complex x x at h0
    rw [hxx, one_smul, mul_one, hxx] at h0
    exact h0
  have hc1 : (0 : Complex) = c := by
    change inner Complex y (inner Complex x y • x) = c * inner Complex y y at h1
    rw [hxy, zero_smul, inner_zero_right, hyy, mul_one] at h1
    exact h1
  exact one_ne_zero (hc0.trans hc1.symm)
end QEC.Semantics.QuditSubsystem
