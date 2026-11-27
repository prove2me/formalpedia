-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_HilbW_proof_be9b81aca3f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:02:41.117576+00:00
-- url     : https://prove2.me/submissions/d3f9f7fc-586c-4d8a-8174-2803fc77b308

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropHilbWSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleEmbedSectionsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleEmbedNumbersSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechH0SectionsHypothesesLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumPointSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropHilbW
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_hilbW_X_mem_primeOf_2a2bd2d723a9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_hilbW_ne_zero_0045b71f9b51

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SectionCount.Drop.HilbW
theorem _root_.solution
    (hPt : PrimeFiltration.Point.Statement.{u, w})
    (hRes : Restriction.Statement.{u, w})
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w})
    (hLT : LineTwist.Statement.{u, w})
    (hRT : RestrictTwist.Statement.{u, w})
    (hIR : InterNumRestrict.Statement.{u, w})
    (hES : VeryAmpleEmbed.Sections.Statement.{u, w})
    (hEN : VeryAmpleEmbed.Numbers.Statement.{u, w})
    (hH0 : CechZerothCohomologySections.Statement.{u, w, w})
    (hHP : HilbertPositive.Statement.{u, w})
    (hHPt : HilbertPoint.Statement.{u, w})
    (hTie : InterNumTie.Statement.{u, w})
    (hIP : InterNumPoint.Statement.{u, w}) :
    SectionCount.Drop.HilbW.Statement.{u, w} := by
  intro k _ Ω _ _ N x Nb pp e hVA hW
  obtain ⟨r, h, hVh⟩ := hVA
  obtain ⟨j, hj'⟩ := hW.relevant
  have hj : x j ≠ 0 := fun h0 => hj' (hW.le (hilbW_X_mem_primeOf x h0))
  have hPtj := hPt k Ω N x pp hW.isPrime hW.homog hW.le j hj hj'

  obtain ⟨K', _, _, ψ, hker⟩ : ∃ (K' : Type w) (_ : Field K') (_ : Algebra k K')
      (ψ : chartRing k x (singleChart hj) →ₐ[k] K'), RingHom.ker ψ = chartPrime pp hj := by
    have : (chartPrime pp hj).IsPrime := hPtj.1
    have : IsDomain (chartRing k x (singleChart hj) ⧸ chartPrime pp hj) := Ideal.Quotient.isDomain _
    refine ⟨FractionRing (chartRing k x (singleChart hj) ⧸ chartPrime pp hj), inferInstance, inferInstance,
      (IsScalarTower.toAlgHom k _ _).comp (Ideal.Quotient.mkₐ k (chartPrime pp hj)), ?_⟩
    ext a
    rw [RingHom.mem_ker]
    change algebraMap _ (FractionRing (chartRing k x (singleChart hj) ⧸ chartPrime pp hj))
      (Ideal.Quotient.mk (chartPrime pp hj) a) = 0 ↔ _
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0 := by
    intro i hi h0
    apply hi
    have : ratio (S := k) hj i = 0 := Subtype.ext (show x i / x j = 0 by rw [h0, zero_div])
    rw [this, map_zero]
  have hpy : primeOf (S := k) (fun i => ψ (ratio hj i)) = pp := hPtj.2 K' ψ hker
  have hle : primeOf (S := k) x ≤ primeOf (S := k) (fun i => ψ (ratio hj i)) := by
    rw [hpy]; exact hW.le
  have hWy : IsSubvar (fun i => ψ (ratio hj i)) pp e := ⟨hW.isPrime, hW.homog, hpy.le, hW.relevant, hW.dim⟩
  have hWy' : IsSubvar (fun i => ψ (ratio hj i)) (primeOf (S := k) (fun i => ψ (ratio hj i))) e := by
    rw [hpy]; exact hWy

  obtain ⟨Q', ρ, hRD, hVA', -⟩ := hRes k Ω N x Nb r h hVh pp hW.isPrime hW.homog hW.le j hj hj' K' ψ hker hxy
  obtain ⟨hWh, hnum⟩ := hEN k K' N _ Q' r (ρ ∘ h) hVA' e hWy'

  have hpow : ∀ m : ℕ, ∃ (Nm : LineBundle k x) (Qm : LineBundle k (fun i => ψ (ratio hj i))) (rm : Ω → K'),
      Nm.toSubSystem = Nb.toSubSystem.pow m ∧ Qm.toSubSystem = Q'.toSubSystem.pow m ∧
        RestrictData Nm.toSubSystem hxy Qm.toSubSystem rm := by
    intro m
    induction m with
    | zero =>
      obtain ⟨r0, hr0⟩ := hRT.1 k Ω N x K' _ hxy hle 0
      exact ⟨twistBundle k x 0, twistBundle k _ 0, r0, rfl, rfl, hr0⟩
    | succ m ih =>
      obtain ⟨Nm, Qm, rm, hN, hQ, hr⟩ := ih
      obtain ⟨N1, hN1⟩ := hLT k Ω N x Nm Nb
      obtain ⟨Q1, hQ1⟩ := hLT k K' N _ Qm Q'
      obtain ⟨r1, hr1⟩ := hRT.2 k Ω N x K' _ hxy Nm Nb Qm Q' rm ρ hr hRD
      refine ⟨N1, Q1, r1, ?_, ?_, ?_⟩
      · rw [hN1, hN]; rfl
      · rw [hQ1, hQ]; rfl
      · rw [hN1, hQ1]; exact hr1

  have hdim : ∀ m : ℕ, Module.finrank k (SubSystem.quotH (twistMul Nb.toSubSystem m 0)
      ((twistMul Nb.toSubSystem m 0).twist (idealSys x pp)) 0) =
        Module.finrank k (twistSys k (ρ ∘ h) (m : ℤ)).secs := by
    intro m
    obtain ⟨Nm, Qm, rm, hN, hQ, hr⟩ := hpow m
    obtain ⟨E1⟩ := hRQ k Ω N x pp hW.isPrime hW.homog hW.le j hj hj' K' ψ hker hxy Nm Qm rm hr 0 0
    obtain ⟨E2⟩ := hH0 k K' N _ K' (Q'.toSubSystem.pow m) (hilbW_ne_zero hWy)
    have e1 : Nm.toSubSystem.twist (twistSys k x 0) = twistMul Nb.toSubSystem m 0 := by rw [hN]; rfl
    have e2 : Qm.toSubSystem.twist (twistSys k (fun i => ψ (ratio hj i)) 0) = Q'.toSubSystem.pow m := by
      rw [hQ, SubSystem.twist_twistSys_zero]
    rw [← hES k K' N _ Q' r (ρ ∘ h) (hilbW_ne_zero hWy) hVA' m, ← e1, ← E2.finrank_eq, ← e2]
    exact E1.finrank_eq

  have hI : interNum pp (fun _ : Fin e => Nb.toSubSystem) =
      interNum (primeOf (S := k) (ρ ∘ h)) (fun _ : Fin e => twistSys k (ρ ∘ h) 1) := by
    have h1 : interNum pp (fun _ : Fin e => Q'.toSubSystem) = interNum pp (fun _ : Fin e => Nb.toSubSystem) :=
      hIR k Ω N x K' _ hxy hle pp e hWy (fun _ => Nb) (fun _ => Q') (fun _ => ρ) (fun _ => hRD)
    rw [← h1, ← hnum, hpy]
  rcases Nat.eq_zero_or_pos e with rfl | he
  · obtain ⟨-, hpc, hsecs⟩ := hHPt k K' r (ρ ∘ h) hWh
    have hI0 : interNum pp (fun _ : Fin 0 => Nb.toSubSystem) =
        (Module.finrank k (funField (k := k) (ρ ∘ h)) : ℤ) := by
      rw [hI]; exact hIP k K' r (ρ ∘ h) hWh _
    refine ⟨0, ?_⟩
    filter_upwards [hpc, hsecs] with m h1 h2
    rw [hdim m, h2, h1, hI0]
    simp
  · obtain ⟨⟨C, hC⟩, -, hsecs⟩ := hHP k K' r (ρ ∘ h) e he hWh
    have hc : (primeOf (S := k) (ρ ∘ h)).comap (oneBlock (S := k) (N := r)).toRingHom =
        primeOfOne (S := k) (ρ ∘ h) := Ideal.ext fun _ => Iff.rfl
    have hIe : interNum pp (fun _ : Fin e => Nb.toSubSystem) =
        NumbersDVR.intNum k (primeOfOne (S := k) (ρ ∘ h)) (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) := by
      rw [hI, ← hc]
      exact hTie k K' r (ρ ∘ h) e (primeOf (S := k) (ρ ∘ h)) (fun _ => 1) hWh
    refine ⟨C, ?_⟩
    filter_upwards [hC, hsecs, eventually_ge_atTop 1] with m h1 h2 hm
    rw [hdim m, h2, hIe]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hpow' : (m : ℝ) ^ e / m = (m : ℝ) ^ (e - 1) := by
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      rw [pow_succ, mul_div_assoc, div_self hm0, mul_one, Nat.add_sub_cancel]
    have hCm : C * (m : ℝ) ^ e / m = C * (m : ℝ) ^ (e - 1) := by rw [mul_div_assoc, hpow']
    rw [hCm]
    exact h1
end SectionCount.Drop.HilbW
end GroundTheory.Heights₂.Heights.Kleiman
