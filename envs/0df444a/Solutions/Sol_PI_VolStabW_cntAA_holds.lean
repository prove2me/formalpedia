-- Prove2me | solution 1 for PI.VolStabW.cntAA_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:58:10.661136+00:00
-- url     : https://prove2.me/submissions/2dfdc0c0-3b80-49b0-8186-35a88a0eee68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCnt
import Theorems.Thm_PI_VolStabW_cnt_at
import Theorems.Thm_PI_VolStabW_ev_int
import Theorems.Thm_PI_VolStabW_ev_unit
import Theorems.Thm_PI_VolStabW_exists_basis_anti
import Theorems.Thm_PI_VolStabW_latFacts_holds
import Theorems.Thm_PI_VolStabW_sigma_invol


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution : CntAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet d b
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨δ, D0, c, hδ0, hσδ, hδ, hD0, hc0, hc1⟩ := exists_basis_anti σ hCM
  let A : AntiB F E σ := ⟨δ, D0, c, hc0, hc1, hδ, hσδ, hD0⟩
  have hJdet : J.det ≠ 0 := hJ.2
  filter_upwards [ev_int (F := F) D0, ev_unit hD0, ev_unit (two_ne_zero : (2 : F) ≠ 0),
    eventually_all.2 fun j => eventually_all.2 fun k => ev_int (F := F) (b.repr (c j) k),
    eventually_all.2 fun k => eventually_all.2 fun j => ev_int (F := F) (c.repr (b k) j),
    eventually_all.2 fun p => eventually_all.2 fun q => eventually_all.2 fun j =>
      ev_int (F := F) (c.repr (J p q) j),
    eventually_all.2 fun p => eventually_all.2 fun q => eventually_all.2 fun j =>
      ev_int (F := F) (c.repr (gramE σ J X0 p q) j),
    eventually_all.2 fun j => ev_int (F := F) (c.repr (J.det)⁻¹ j),
    eventually_all.2 fun j => ev_int (F := F) (c.repr ((gramE σ J X0).det)⁻¹ j)]
    with v hD hDu h2 hbc hcb hJi hTi hJu hTu
  intro μ hμ
  haveI := hμ
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have hNm : MeasurableSet (lamF b v a M 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    ((latFacts_holds F E σ d b a M v).1 0).measurableSet
  obtain ⟨k, K, i1, i2, i3, i4, σ', J', T', hQ, h2k, hJ', hJu', hT', hTu', hcard, hmeas⟩ :=
    cnt_at v A (sigma_invol σ hCM.2.2.2) J hJ.1 (gramE σ J X0) hT b hbc hcb hD hDu h2 hJi hTi
      hNm μ
  exact ⟨k, K, i1, i2, i3, i4, σ', J', T', hQ, h2k, hJ', hJu' _ (mul_inv_cancel₀ hJdet) hJu, hT',
    hTu' _ (mul_inv_cancel₀ hdet) hTu, hcard, hmeas⟩
end PI.VolStabW
