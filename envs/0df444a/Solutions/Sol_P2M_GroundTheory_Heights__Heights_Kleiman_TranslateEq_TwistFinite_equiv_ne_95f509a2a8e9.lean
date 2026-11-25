-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_TwistFinite_equiv_ne_95f509a2a8e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:34:41.387904+00:00
-- url     : https://prove2.me/submissions/0733b41a-207d-4b71-938f-346b56ffdc4a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NotTwistFiniteAtZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistPowZeroSub
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_lmul_lpow_e0b30fd3fd3d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_isGeneratedBy_iff_f2e7bac6fb36
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_iSup_span_secZ_eq_dc1f599cdd89
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_aeval_mem_pow_9aee5e0ba8ce

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
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
namespace TwistFinite
theorem _root_.solution (hL : TranslateEq.LineBundle.Statement) :
    Kleiman.TwistFinite.Statement.{0, 0} ↔ TwistFiniteNe.Statement := by
  constructor
  · intro hA S _ _ N Ω _ _ x G' B' r η hx hgen
    obtain ⟨G, hG⟩ := (hL S N Ω x).2 G'
    obtain ⟨B, hB⟩ := (hL S N Ω x).2 B'
    have hgen' := (isGeneratedBy_iff B.toSubFamily B'.mods hB η).mp hgen
    obtain ⟨n, deg, gen, hgen1, hle⟩ := hA S Ω N x G B r η hx hgen'.1 hgen'.2
    have hsecs := secs_lmul_lpow G.toSubSystem B.toSubSystem G'.mods B'.mods hG hB
    refine ⟨n, deg, gen, fun k => ?_, fun b => ?_⟩
    · rw [hsecs]
      exact hgen1 k
    · rw [iSup_span_secZ_eq]
      apply le_antisymm
      · rw [hsecs]
        exact hle b
      · rw [Submodule.span_le]
        rintro _ ⟨k, f, e, hf, he, rfl⟩
        have hk := hgen1 k
        rw [← hsecs] at hk
        simp only [IndefiniteRowSideFullHecke.Kleiman.secs, SetLike.mem_coe, Submodule.mem_iInf] at hk ⊢
        intro i hi
        have hη : ∀ j, η j ∈ B'.mods i := by
          intro j
          have := hgen.1 j
          simp only [IndefiniteRowSideFullHecke.Kleiman.secs, Submodule.mem_iInf] at this
          exact this i hi
        have ha := aeval_mem_pow hη hf
        have hki := hk i hi
        show aeval η f * gen k ∈ G'.mods i * B'.mods i ^ b
        change gen k ∈ G'.mods i * B'.mods i ^ deg k at hki
        have hmul : B'.mods i ^ e * (G'.mods i * B'.mods i ^ deg k) = G'.mods i * B'.mods i ^ (e + deg k) := by
          rw [pow_add, mul_left_comm]
        rw [← he, ← hmul]
        exact Submodule.mul_mem_mul ha hki
  · intro hB' S _ _ Ω _ _ N x G B r η hx hη hspan
    obtain ⟨G', hG⟩ := (hL S N Ω x).1 G
    obtain ⟨B', hB⟩ := (hL S N Ω x).1 B
    have hgen : IndefiniteRowSideFullHecke.Kleiman.IsGeneratedBy S x B'.mods η :=
      (isGeneratedBy_iff B.toSubFamily B'.mods (fun i _ => hB i) η).mpr ⟨hη, hspan⟩
    obtain ⟨n, bk, s, hs, heq⟩ := hB' S N Ω x G' B' r η hx hgen
    have hsecs := secs_lmul_lpow G.toSubSystem B.toSubSystem G'.mods B'.mods
      (fun i _ => hG i) (fun i _ => hB i)
    refine ⟨n, bk, s, fun k => ?_, fun b => ?_⟩
    · rw [← hsecs]
      exact hs k
    · rw [← hsecs, heq b, iSup_span_secZ_eq]
end TwistFinite
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
