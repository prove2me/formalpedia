-- Prove2me | solution 1 for PI.LevelKSplit.W.NC.coord_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:32:46.327213+00:00
-- url     : https://prove2.me/submissions/47f7178b-e2a8-457e-841f-c9cd62ab90d1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCIface
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_CoordinateHomeomorphism

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NC
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Q : Type} [AddCommGroup Q] [TopologicalSpace Q] [ContinuousAdd Q]
variable {N A N1 Z : Subgroup G} {Lev : G → G} {sH : Q → G} {yQ : N1 → Q}
namespace PI.LevelKSplit.W.NC
theorem _root_.solution (H : CoordHyp N A N1 Z Lev sH yQ) (n0 : N) :
    ∃ (a0 : A) (t : A → Q) (c : A × Q → Z), Continuous t ∧ Continuous c ∧
      ∀ u y z, n0 * cHomeo H (u, y, z) = cHomeo H (a0 * u, y + t u, c (u, y) * z) := by
  set a0 : A := ⟨Lev n0, H.lev_mem n0 n0.2⟩
  set n1 : G := (Lev n0)⁻¹ * (n0 : G) with hn1
  have hn1m : n1 ∈ N1 := H.lev_rest n0 n0.2
  have hmf : ∀ u : A, (u : G)⁻¹ * n1 * u ∈ N1 := fun u => by
    have := H.norm1 ((u : G)⁻¹) (N.inv_mem (H.hAN u.2)) n1 hn1m
    simpa using this
  let mf : A → N1 := fun u => ⟨(u : G)⁻¹ * n1 * u, hmf u⟩
  have cmf : Continuous mf := Continuous.subtype_mk
    ((continuous_subtype_val.inv.mul continuous_const).mul continuous_subtype_val) _
  let t : A → Q := fun u => yQ (mf u)
  have ct : Continuous t := H.cyQ.comp cmf
  let zm : A → G := fun u => (sH (t u))⁻¹ * (mf u : G)
  have hzm : ∀ u, zm u ∈ Z := fun u => H.dec (mf u)
  let k : A × Q → G := fun p => sH (t p.1) * sH p.2 * (sH (t p.1 + p.2))⁻¹
  have hk : ∀ p, k p ∈ Z := fun p => H.mul _ _
  let c : A × Q → Z := fun p => ⟨k p * zm p.1, Z.mul_mem (hk p) (hzm p.1)⟩
  have cc : Continuous c := by
    refine Continuous.subtype_mk ?_ _
    have ct1 : Continuous (fun p : A × Q => t p.1) := ct.comp continuous_fst
    refine (((H.csH.comp ct1).mul (H.csH.comp continuous_snd)).mul
      (H.csH.comp (ct1.add continuous_snd)).inv).mul ?_
    exact (H.csH.comp ct1).inv.mul (continuous_subtype_val.comp (cmf.comp continuous_fst))
  refine ⟨a0, t, c, ct, cc, fun u y z => ?_⟩
  apply Subtype.ext
  show (n0 : G) * ((u : G) * sH y * (z : G)) = (Lev n0 * u) * sH (y + t u) * (k (u, y) * zm u * z)
  have e2 : (mf u : G) = sH (t u) * zm u := by
    show (mf u : G) = sH (t u) * ((sH (t u))⁻¹ * (mf u : G)); group
  have e3 : zm u * sH y = sH y * zm u := H.cent _ (hzm u) _ (H.sH_mem y)
  have e4 : sH (t u) * sH y = sH (t u + y) * k (u, y) := by
    have h := H.cent _ (hk (u, y)) _ (H.sH_mem (t u + y))
    calc sH (t u) * sH y = k (u, y) * sH (t u + y) := by show _ = sH (t u) * sH y * (sH (t u + y))⁻¹ * sH (t u + y); group
      _ = sH (t u + y) * k (u, y) := h
  have e1 : (n0 : G) * ((u : G) * sH y * (z : G)) = Lev n0 * u * (mf u : G) * sH y * z := by
    show _ = Lev n0 * u * ((u : G)⁻¹ * ((Lev n0)⁻¹ * (n0 : G)) * u) * sH y * z
    group
  rw [e1, e2, add_comm y (t u)]
  calc Lev n0 * (u : G) * (sH (t u) * zm u) * sH y * (z : G)
      = Lev n0 * u * sH (t u) * (zm u * sH y) * z := by group
    _ = Lev n0 * u * sH (t u) * (sH y * zm u) * z := by rw [e3]
    _ = Lev n0 * u * (sH (t u) * sH y) * zm u * z := by group
    _ = Lev n0 * u * (sH (t u + y) * k (u, y)) * zm u * z := by rw [e4]
    _ = (Lev n0 * u) * sH (t u + y) * (k (u, y) * zm u * z) := by group
end PI.LevelKSplit.W.NC
