-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveNormalisationQuotientLength_proof_6387e7bb79eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:54:45.400864+00:00
-- url     : https://prove2.me/submissions/78434f30-9dee-4b54-8b43-93fcb1ee1b6d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveNormalisationQuotientLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_withBot_enat_le_zero_of_add_one_le_one_373baced907a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
namespace GroundTheory.Heights₂.Heights
namespace CurveNormalisationQuotientLength
theorem _root_.solution (hF : CurveNormalisationFinite.Statement) :
    CurveNormalisationQuotientLength.Statement := by
  intro n I q hrad hdim
  set O := curveLocalRing I q
  set N := curveNormalisation I q
  set M := N ⧸ LinearMap.range (Algebra.linearMap O N)
  have hfin : Module.Finite O N := hF n I q hrad

  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := N)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) s
    (fun x : N ↦ ((show ↥(integralClosure O (FractionRing O)) from x) : FractionRing O))
  have hmul : ∀ y : N, (b : O) • y ∈ LinearMap.range (Algebra.linearMap O N) := by
    intro y
    have hle : Submodule.span O (s : Set N) ≤
        (LinearMap.range (Algebra.linearMap O N)).comap ((b : O) • LinearMap.id) := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨a, ha⟩ := hb x hx
      refine ⟨a, Subtype.ext ?_⟩
      exact ha
    exact hle (hs ▸ Submodule.mem_top : y ∈ Submodule.span O (s : Set N))
  have hann : (b : O) ∈ Module.annihilator O M := by
    rw [Module.mem_annihilator]
    intro m
    induction m using Submodule.Quotient.induction_on with
    | H y => rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact hmul y

  have hd := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (Module.annihilator O M))
    Ideal.Quotient.mk_surjective b.2 (Ideal.Quotient.eq_zero_iff_mem.2 hann)
  rw [hdim] at hd
  have : Ring.KrullDimLE 0 (O ⧸ Module.annihilator O M) :=
    Ring.krullDimLE_iff.2 (by exact_mod_cast withBot_enat_le_zero_of_add_one_le_one hd)
  have : IsArtinianRing (O ⧸ Module.annihilator O M) := isArtinianRing_iff_krullDimLE_zero.2 inferInstance
  let := Module.quotientAnnihilator (R := O) (M := M)
  have := (Module.isTorsionBySet_annihilator O M).isScalarTower (S := O)
  have : Module.Finite (O ⧸ Module.annihilator O M) M := Module.Finite.of_restrictScalars_finite O _ _
  have : IsArtinian O M := isArtinian_of_surjective_algebraMap (S := O) (R := O ⧸ Module.annihilator O M)
    (show Function.Surjective (algebraMap O (O ⧸ Module.annihilator O M)) from Ideal.Quotient.mk_surjective)
  exact Module.length_ne_top
end CurveNormalisationQuotientLength
end GroundTheory.Heights₂.Heights
