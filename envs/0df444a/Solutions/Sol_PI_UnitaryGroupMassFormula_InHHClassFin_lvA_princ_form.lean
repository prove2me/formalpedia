-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.lvA_princ_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:26.727185+00:00
-- url     : https://prove2.me/submissions/859cb123-2c3d-4139-b287-611fe471b047

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelA
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {R : Type} [CommRing R] (S : Subring R) {n : ℕ}
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (d : S) (u : GL ι R)
    (hu : u ∈ Formalism.UG.princ (n := ι) S.subtype (Ideal.span {d})) :
    ∃ N : Matrix ι ι R, (∀ i j, N i j ∈ S) ∧ (u : Matrix ι ι R) = 1 + (d : R) • N := by
  obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
  have h1 : Formalism.UG.redGL (Ideal.span {d}) u' = 1 := Subgroup.mem_bot.1 (Subgroup.mem_comap.1 hu')
  have hent : ∀ i j, ∃ a : S, a * d = (u' : Matrix ι ι S) i j - (1 : Matrix ι ι S) i j := by
    intro i j
    have h2 := congrArg (fun g : GL ι (S ⧸ Ideal.span {d}) => (g : Matrix ι ι (S ⧸ Ideal.span {d})) i j) h1
    simp only [Formalism.UG.redGL, Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Units.val_one] at h2
    have h3 : (u' : Matrix ι ι S) i j - (1 : Matrix ι ι S) i j ∈ Ideal.span {d} := by
      rw [← Ideal.Quotient.eq]
      have h2' : Ideal.Quotient.mk (Ideal.span {d}) ((u' : Matrix ι ι S) i j) =
          (1 : Matrix ι ι (S ⧸ Ideal.span {d})) i j := h2
      rw [h2', Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    exact Ideal.mem_span_singleton'.1 h3
  choose a ha using hent
  refine ⟨fun i j => (a i j : R), fun i j => (a i j).2, ?_⟩
  ext i j
  have h4 := congrArg (fun s : S => (s : R)) (ha i j)
  push_cast at h4
  show S.subtype ((u' : Matrix ι ι S) i j) = (1 : Matrix ι ι R) i j + (d : R) * (a i j : R)
  rw [Subring.coe_subtype, Matrix.one_apply]
  rw [Matrix.one_apply] at h4
  split_ifs at h4 ⊢ <;> simp at h4 ⊢ <;> linear_combination -h4
end PI.UnitaryGroupMassFormula.InHHClassFin
