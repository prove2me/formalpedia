-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_filtPiece_sup_19ebee9ad0cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:07:15.064877+00:00
-- url     : https://prove2.me/submissions/dd898dcb-11b8-415d-8507-4a0daa61c151

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltGraded
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_filtPiece_mono_1da95a728efe

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
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
variable {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
variable (M₁ M₂ : FinGradedSub (S := S) (x := x) E)
variable {M₁ M₂}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {A : Submodule (Poly S N) (quotLaurent M₁ M₂)} (hA : IsProjStable M₁ M₂ A) {e : ℤ}
    (g : M₁.piece e) (c : ℤ) :
    filtPiece M₁ M₂ (A ⊔ Submodule.span (Poly S N) {quotIota M₁ M₂ e g}) c =
      filtPiece M₁ M₂ A c ⊔ Submodule.span S
        {z | ∃ (f : Poly S N) (d : ℕ), f.IsHomogeneous d ∧ e + d = c ∧ z = aeval x f • (g : E)} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨hz1, hzA⟩ := mem_filtPiece.mp hz
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hzA
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hb
    set w : E := (r • laurentSingle x e (g : E)) c with hwdef
    have hw : w ∈ Submodule.span S
        {z | ∃ (f : Poly S N) (d : ℕ), f.IsHomogeneous d ∧ e + d = c ∧ z = aeval x f • (g : E)} := by
      rw [hwdef, laurent_smul_apply]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [laurentSingle_apply]
      split_ifs with h
      · exact Submodule.subset_span ⟨_, i, homogeneousComponent_isHomogeneous i r, by omega, rfl⟩
      · rw [smul_zero]
        exact zero_mem _
    have hw1 : w ∈ M₁.piece c :=
      FinGradedSub.mem_laurent.mp (M₁.laurent.smul_mem r (laurentSingle_mem g.2)) c
    have key : quotIota M₁ M₂ c ⟨z, hz1⟩ = quotProj M₁ M₂ c a + quotIota M₁ M₂ c ⟨w, hw1⟩ := by
      rw [← quotProj_iota_self M₁ M₂ c ⟨z, hz1⟩, ← hab, map_add]
      congr 1
    have hzw : z - w ∈ filtPiece M₁ M₂ A c := by
      refine mem_filtPiece.mpr ⟨sub_mem hz1 hw1, ?_⟩
      have hs : (⟨z - w, sub_mem hz1 hw1⟩ : M₁.piece c) = ⟨z, hz1⟩ - ⟨w, hw1⟩ := rfl
      rw [hs, map_sub, key, add_sub_cancel_right]
      exact hA a ha c
    rw [← sub_add_cancel z w]
    exact add_mem (Submodule.mem_sup_left hzw) (Submodule.mem_sup_right hw)
  · refine sup_le (filtPiece_mono le_sup_left c) ?_
    rw [Submodule.span_le]
    rintro _ ⟨f, d, hf, rfl, rfl⟩
    refine mem_filtPiece.mpr ⟨M₁.smul_mem d e f g hf g.2, ?_⟩
    have h2 : f • quotIota M₁ M₂ e g ∈ A ⊔ Submodule.span (Poly S N) {quotIota M₁ M₂ e g} :=
      Submodule.smul_mem _ f (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    rw [smul_quotIota M₁ M₂ hf] at h2
    exact h2
end GroundTheory.Heights₂.Heights.Kleiman
