-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.locSplitP_dec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:19:27.929498+00:00
-- url     : https://prove2.me/submissions/71ebd6c1-219a-45ed-b786-cb15cc9b7cb8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SplitGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_NatCastTmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SplitLoc
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_spl_sig_fix
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_spl_sig_sig
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_eps_orth
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_exists_adapted_first_projection


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (Rf : RefData I g r k e f)
    (v : HeightOneSpectrum (𝓞 I.F)) (hsum : SumOne I v (PI.FinKW.psiV I v Rf.ew)) :
    ∃ p1 : RV I v →+* KV I v, IsAdaptedFirstProjection I v (PI.FinKW.psiV I v Rf.ew) p1 ∧
      ∀ x : RV I v, x = algebraMap (KV I v) (RV I v) (p1 x) * PI.FinKW.psiV I v Rf.ew +
        algebraMap (KV I v) (RV I v) (p1 (PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v x)) *
          PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) := by
  have : CharZero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :=
    charZero_of_injective_algebraMap (algebraMap I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v)).injective
  have h2K : (2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ≠ 0 := two_ne_zero
  obtain ⟨p1, h1, h2, h3, h4⟩ := exists_adapted_first_projection (K := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) I.cm.sig
    (PI.UnitaryGroupMassFormula.AdIndexEq.spl_sig_sig I) (PI.UnitaryGroupMassFormula.AdIndexEq.spl_sig_fix I) I.cm.deg2 h2K
    (PI.FinKW.psiV I v Rf.ew) hsum (eps_orth Rf v)
  refine ⟨p1, ⟨h1, h2, h3, ?_⟩, h4⟩
  rintro x ⟨z, rfl⟩
  obtain ⟨fp, hm, hf⟩ := NumberField.RingOfIntegers.isIntegral_coe z
  have hf' : Polynomial.eval₂ (algebraMap ℤ I.E) (algebraMap (𝓞 I.E) I.E z) fp = 0 := hf
  show (p1.comp (PI.UnitaryGroupMassFormula.AdIndexEq.inclV I v)) (algebraMap (𝓞 I.E) I.E z) ∈ OV I v
  refine (Valuation.valuationSubring.integers (Valued.v (R := v.adicCompletion I.F))).mem_of_integral
    ⟨fp.map (Int.castRingHom _), hm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hc : (algebraMap (Valued.v (R := v.adicCompletion I.F)).valuationSubring (v.adicCompletion I.F)).comp
      (Int.castRingHom (Valued.v (R := v.adicCompletion I.F)).valuationSubring) =
      (p1.comp (PI.UnitaryGroupMassFormula.AdIndexEq.inclV I v)).comp (algebraMap ℤ I.E) := RingHom.ext_int _ _
  rw [hc, ← Polynomial.hom_eval₂, hf', map_zero]
end PI.UnitaryGroupMassFormula.ScXuExists
