-- Prove2me | solution 1 for PI.WAU.Cpt.isCompact_Kset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:20:34.681382+00:00
-- url     : https://prove2.me/submissions/0d373e7b-acec-4223-ae34-0119fcfae93e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_IsCompactCset
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_NatSmulMulEq
import Theorems.Thm_PI_WAU_Cpt_mem_range_psi
import Theorems.Thm_PI_WAU_Cpt_continuous_psi
import Theorems.Thm_PI_WAU_Cpt_isCompact_Cset
import Theorems.Thm_PI_WAU_Cpt_psi_mem
import Theorems.Thm_PI_WAU_coord_incl
import Theorems.Thm_PI_WAU_exists_den_fin
import Theorems.Thm_PI_WAU_exists_den_mul
import Theorems.Thm_PI_WAU_exists_lower
import Theorems.Thm_PI_WAU_exists_upper


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix
open PI.WAU.Cpt
variable (I : AutInst)
namespace PI.WAU.Cpt
theorem _root_.solution : IsCompact I.Kset := by
  obtain ⟨d, hd, hlow⟩ := exists_lower (bs I) I.L I.L_span
  obtain ⟨D, hD, hup⟩ := exists_upper (bs I) I.L I.L_fg
  obtain ⟨m, hm, hmul⟩ := exists_den_mul (bs I)
  obtain ⟨D1, hD1, h1F⟩ := exists_den_fin (fun k : ιb I => (bs I).repr 1 k)
  have h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F)) := by
    intro k
    rw [map_nsmul, ← map_one (Algebra.TensorProduct.includeLeftRingHom (R := I.F) (A := I.E) (B := Af I.F)),
      coord_incl, Pi.smul_apply, nsmul_eq_mul, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul]
    exact h1F k
  have hN : 0 < D * (d * D1) := Nat.mul_pos hD (Nat.mul_pos hd hD1)
  haveI : CompactSpace (Cset I (D * (d * D1))) :=
    isCompact_iff_compactSpace.mp (isCompact_Cset I _ d hd hlow)
  have : I.Kset = Set.range (psi I (D * (d * D1))) := by
    ext x
    constructor
    · intro hx; exact mem_range_psi I d D D1 hN hlow hup h1 hx
    · rintro ⟨p, rfl⟩; exact psi_mem I _ p
  rw [this]
  exact isCompact_range (continuous_psi I _ d D m hd hD hm hlow hup hmul)
end PI.WAU.Cpt
