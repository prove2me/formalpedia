-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_iSup_span_secZ_eq_dc1f599cdd89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:50.258277+00:00
-- url     : https://prove2.me/submissions/54407554-d8ee-4629-9600-ab38352cba45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NotTwistFiniteAtZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistPowZeroSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution {r n : ℕ} (η : Fin (r + 1) → Ω) (bk : Fin n → ℕ) (s : Fin n → Ω) (b : ℕ) :
    (⨆ k, Submodule.span S (Set.image2 (· * ·) (IndefiniteRowSideFullHecke.Kleiman.secZ S η ((b : ℤ) - bk k) : Set Ω) {s k})) =
      Submodule.span S {z | ∃ (k : Fin n) (f : MvPolynomial (Fin (r + 1)) S) (e : ℕ), f.IsHomogeneous e ∧
        e + bk k = b ∧ z = aeval η f * s k} := by
  apply le_antisymm
  · rw [iSup_le_iff]
    intro k
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, _, rfl, rfl⟩
    rw [SetLike.mem_coe] at ha
    unfold IndefiniteRowSideFullHecke.Kleiman.secZ at ha
    split_ifs at ha with hd
    · obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp ha
      exact Submodule.subset_span
        ⟨k, f, ((b : ℤ) - bk k).toNat, (mem_homogeneousSubmodule _ _).mp hf, by omega, rfl⟩
    · rw [Submodule.mem_bot] at ha
      simp [ha]
  · rw [Submodule.span_le]
    rintro _ ⟨k, f, e, hf, he, rfl⟩
    refine Submodule.mem_iSup_of_mem k (Submodule.subset_span ⟨aeval η f, ?_, s k, rfl, rfl⟩)
    have hd : ((b : ℤ) - bk k) = (e : ℤ) := by omega
    rw [hd, SetLike.mem_coe]
    unfold IndefiniteRowSideFullHecke.Kleiman.secZ
    rw [if_pos (by positivity), Int.toNat_natCast]
    exact Submodule.mem_map.mpr ⟨f, (mem_homogeneousSubmodule _ _).mpr hf, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
