-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_algebraMap_surjective_46fcacb94b77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:13:37.707828+00:00
-- url     : https://prove2.me/submissions/e05f0486-7a2e-4917-b931-cb03db8c3e57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConstantsDescend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConstantsDescend
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_sub_mem_map_f2a0783dec19

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra ℚ A] [Algebra.FiniteType ℚ A]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
theorem _root_.solution (hinj : Function.Injective (algebraMap A B)) (θ : B)
    (hgen : Algebra.adjoin A {θ} = ⊤) (p : ℚ[X]) (hpm : p.Monic) (hps : p.Separable)
    (hp : aeval θ (p.map (algebraMap ℚ A)) = 0)
    (huniq : ∀ w w' : B →+* ℂ, w.comp (algebraMap A B) = w'.comp (algebraMap A B) → w θ = w' θ) :
    Function.Surjective (algebraMap A B) := by
  classical
  have hθA : IsIntegral A θ := ⟨p.map (algebraMap ℚ A), hpm.map _, hp⟩
  haveI : Algebra.IsIntegral A B :=
    ⟨fun b => adjoin_le_integralClosure hθA (hgen ▸ Algebra.mem_top : b ∈ Algebra.adjoin A {θ})⟩
  haveI : Algebra.FiniteType A B := ⟨⟨{θ}, by simpa using hgen⟩⟩
  haveI : Module.Finite A B := Algebra.finite_iff_isIntegral_and_finiteType.2 ⟨inferInstance, inferInstance⟩
  set N := LinearMap.range (Algebra.linearMap A B) with hN
  have hann : Module.annihilator A (B ⧸ N) = ⊤ := by
    by_contra hne
    obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal _ hne
    have hIB : I.map (algebraMap A B) ≠ ⊤ := by
      have hk : RingHom.ker (algebraMap A B) ≤ I := by
        rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
        exact bot_le
      obtain ⟨Q, hQ, hQI⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral I hk
      intro htop
      apply hQ.ne_top
      rw [eq_top_iff, ← htop, Ideal.map_le_iff_le_comap, hQI]
    have hsmul : (⊤ : Submodule A (B ⧸ N)) ≤ I • ⊤ := by
      rintro x -
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective N x
      obtain ⟨a, ha⟩ := exists_sub_mem_map θ hgen p hpm hps hp huniq I hIB b
      have h1 : b - algebraMap A B a ∈ I • (⊤ : Submodule A B) := by
        rw [Ideal.smul_top_eq_map]
        exact ha
      have h2 : N.mkQ (b - algebraMap A B a) ∈ I • (⊤ : Submodule A (B ⧸ N)) := by
        have := Submodule.mem_map_of_mem (f := N.mkQ) h1
        rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
      have h3 : N.mkQ (algebraMap A B a) = 0 := (Submodule.Quotient.mk_eq_zero N).2 ⟨a, rfl⟩
      rw [map_sub, h3, sub_zero] at h2
      exact h2
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤
      (Module.finite_def.1 inferInstance) hsmul
    have hr' : r ∈ I := hle (Module.mem_annihilator.2 fun x => hr x Submodule.mem_top)
    exact hI.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using I.sub_mem hr' hr1))
  intro b
  have h1 : (1 : A) ∈ Module.annihilator A (B ⧸ N) := hann ▸ Submodule.mem_top
  have h0 : (Submodule.Quotient.mk b : B ⧸ N) = 0 := by
    simpa using Module.mem_annihilator.1 h1 (Submodule.Quotient.mk b)
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero N).1 h0
  exact ⟨a, ha⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
