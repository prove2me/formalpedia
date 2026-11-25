-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_LocalInClosure_proof_837219d902a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:16:39.996991+00:00
-- url     : https://prove2.me/submissions/0bf3eef0-f3bf-4075-81da-b0282f3a9088

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PLocalInClosure
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_locGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
namespace GroundTheory.Heights₂.Heights.StrongApprox
namespace LocalInClosure
theorem _root_.solution (hHP : HypPairExists.Statement) (hCl : ClosureIsSubmonoid.Statement)
    (hLR : LocalRingHypotheses.Statement) (hPM : PlaceMaps.Statement)
    (hEA : EichlerAtPlace.Statement) : LocalInClosure.Statement := by
  intro F E _ _ _ _ _ c hrk hc N J hJ hdet ⟨e, he0, hee⟩ _ _ v g hg
  obtain ⟨hinv, hfix, hrank2, hred, h2, hcomm, hform⟩ := hLR F E c hrk hc v

  have hinj : Function.Injective (inclV E v) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F (v.adicCompletion F)).injective
  have hcinv : ∀ x, c.toRingHom (c.toRingHom x) = x := fun x =>
    hinj (by
      change inclV E v (c (c x)) = inclV E v x
      rw [← hcomm, ← hcomm, hinv])

  obtain ⟨f, hff, hef⟩ := hHP E c.toRingHom hcinv two_ne_zero N J hJ hdet e he0 hee
  obtain ⟨-, h1, hmul, heich⟩ := hCl F E c hrk hc N J hJ hdet e f hee hff hef

  have hJv : (J.map (inclV E v))ᵀ = (J.map (inclV E v)).map (sigV c v) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    rw [hcomm]
    have h := Matrix.ext_iff.mpr hJ i j
    simp only [Matrix.transpose_apply, Matrix.map_apply] at h
    rw [h]
  have hdetv : IsUnit (J.map (inclV E v)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet.map _
  have hzero : ∀ x y : Fin N → E, hf c.toRingHom J x y = 0 →
      hf (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ x) (inclV E v ∘ y) = 0 :=
    fun x y h => by rw [← hform, h, map_zero]
  have hefv : hf (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ e) (inclV E v ∘ f) = 1 := by
    rw [← hform, hef, map_one]
  have hg' := hg
  rw [locGen _ _ (sigV c v) hinv hfix hrank2 hred h2 N _ hJv hdetv _ _ (hzero e e hee)
    (hzero f f hff) hefv] at hg'
  clear hg

  obtain ⟨-, hPv⟩ := hPM F E c hrk hc
  obtain ⟨-, -, -, -, -, -, -, -, hPN⟩ := hPv v
  obtain ⟨hemb1, hembmul, -⟩ := hPN N
  induction hg' using Submonoid.closure_induction with
  | mem x hx => exact heich ((hEA F E c hrk hc v N J).2 hJ e f hee hff hef x hx)
  | one => rw [hemb1]; exact h1
  | mul x y _ _ hx hy => rw [hembmul]; exact hmul _ hx _ hy
end LocalInClosure
end GroundTheory.Heights₂.Heights.StrongApprox
