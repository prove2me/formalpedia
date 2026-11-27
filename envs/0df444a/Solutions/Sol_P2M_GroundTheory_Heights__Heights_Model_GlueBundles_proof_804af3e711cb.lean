-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_GlueBundles_proof_804af3e711cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:03:30.619216+00:00
-- url     : https://prove2.me/submissions/b04e5875-ae3c-418a-a7f5-ccb257c57f04

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueBundles
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueBundles_localPiece_b8db47c49997
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_of_iso_15fe1f0a6e57
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsVectorBundle_of_iso_efcac834adba


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable {X : Scheme.{0}}
namespace GroundTheory.Heights₂.Heights.Model
namespace GlueBundles
theorem _root_.solution (hSB : SpreadBundle.Statement) (hSI : SpreadIso.Statement)
    (hPC : PrimeOpensCover.Statement) (hGS : GlueModulesStar.Statement)
    (hVR : VectorBundleRestrict.Statement) (hVL : VectorBundleLocal.Statement) :
    GlueBundles.Statement := by
  classical
  intro X f _ _ S E₀ Ep hE₀ hEp β
  have key := fun p : S => GlueBundles.localPiece hSB hSI hVR f S E₀ hE₀ p (Ep p) (hEp p) (β p)
  choose n hn hqdiv F hF ψ' δ hcompat using key
  let mp : Nat.Primes → ℤ := fun q => if h : q ∈ S then (n ⟨q, h⟩ : ℤ) else 1
  have hmp : ∀ p : S, mp p = (n p : ℤ) := fun p => dif_pos p.2
  obtain ⟨hcover, hpair⟩ := hPC X f S mp
    (fun p hp => by rw [show mp p = (n ⟨p, hp⟩ : ℤ) from dif_pos hp]; exact hn ⟨p, hp⟩)
    (fun p hp q hq hqp => by
      rw [show mp p = (n ⟨p, hp⟩ : ℤ) from dif_pos hp]
      exact hqdiv ⟨p, hp⟩ q hq hqp)
  let U : S → X.Opens := fun p => invOpen f (n p)
  have hUsup : (⨆ q ∈ S, invOpen f (mp q)) = ⨆ p : S, U p := by
    rw [iSup_subtype']
    exact iSup_congr fun p => by rw [hmp]
  have hcov : invOpen f (primeProd S) ⊔ ⨆ p : S, U p = ⊤ := by
    rw [← hUsup]
    exact hcover
  have hpairU : ∀ i j : S, i ≠ j → U i ⊓ U j ≤ invOpen f (primeProd S) := by
    intro i j hij
    have := (hpair i i.2 j j.2 (fun h => hij (Subtype.ext h))).1
    rwa [hmp, hmp] at this
  obtain ⟨E, e₀, e, hglue⟩ := hGS X (invOpen f (primeProd S)) S U hcov hpairU E₀ F ψ'
  have hVB : IsVectorBundle E := by
    refine hVL X (Option S) (fun o => o.elim (invOpen f (primeProd S)) U) ?_ E ?_
    · rw [iSup_option]
      exact hcov
    · intro o
      cases o with
      | none => exact hE₀.of_iso e₀.symm
      | some p => exact (hF p).of_iso (e p).symm
  exact ⟨E, hVB, e₀, fun p => pullbackCompIso (toInvOpen_ι f (ZLoc p) (n p)
      (isUnit_intCast_zLoc p (n p) (hn p))) (e p) ≪≫ δ p,
    fun p => hcompat p E e₀ (e p) (hglue p)⟩
end GlueBundles
end GroundTheory.Heights₂.Heights.Model
