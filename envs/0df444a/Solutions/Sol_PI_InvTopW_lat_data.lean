-- Prove2me | solution 1 for PI.InvTopW.lat_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:22:02.3228+00:00
-- url     : https://prove2.me/submissions/870b7fa6-aefe-4bae-bb95-ebce92fa4c73

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LatticeOfEntriesIntegral
import Theorems.Thm_PI_InvTopW_exists_good_den
import Theorems.Thm_PI_InvTopW_lat_den
import Theorems.Thm_PI_InvTopW_int_vec_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
namespace PI.InvTopW
theorem _root_.solution (I : AutInst) : ∃ c : ℕ, 1 ≤ c ∧
    (∀ y ∈ I.Lf, ∀ i, (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * y i ∈ Formalism.MainNotions.S.IntAf I.F I.E) ∧
    ∀ u : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F, (∀ i, u i ∈ Formalism.MainNotions.S.IntAf I.F I.E) →
      (fun i => (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * u i) ∈ I.Lf := by
  obtain ⟨c, hc, h1, h2⟩ := exists_good_den I.L I.L_fg I.L_span
  exact ⟨c, hc, lat_den I.L c h1, fun u hu => int_vec_mem I.L c h2 u hu⟩
end PI.InvTopW
