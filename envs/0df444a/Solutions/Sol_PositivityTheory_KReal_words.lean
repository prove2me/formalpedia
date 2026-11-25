-- Prove2me | solution 1 for PositivityTheory.KReal.words
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:26.540196+00:00
-- url     : https://prove2.me/submissions/1084cf76-8e0a-4c22-becd-8ac4ead1de99

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ (Module.End ℂ M))
    (hS : ∀ E ∈ S, ∀ F ∈ S, E * F - F * E ∈ S) (L : Set (Module.End ℂ M)) (hL : L ⊆ S) (z : M)
    (hz : ∀ E ∈ S, ∃ F ∈ Submodule.span ℂ L, ∃ c : ℂ, E z = F z + c • z)
    (W : Submodule ℂ M) (hW : W = sInf {N | z ∈ N ∧ ∀ F ∈ L, ∀ x ∈ N, F x ∈ N}) :
    z ∈ W ∧ (∀ E ∈ S, ∀ x ∈ W, E x ∈ W) ∧ W = Submodule.span ℂ {z} ⊔ ⨆ F ∈ L, W.map F := by
  have hz0 : z ∈ W := by rw [hW]; exact Submodule.mem_sInf.2 fun N hN => hN.1
  have hLW : ∀ F ∈ L, ∀ x ∈ W, F x ∈ W := by
    intro F hF x hx
    rw [hW] at hx ⊢
    exact Submodule.mem_sInf.2 fun N hN => hN.2 F hF x (Submodule.mem_sInf.1 hx N hN)
  have hmin : ∀ N : Submodule ℂ M, z ∈ N → (∀ F ∈ L, ∀ x ∈ N, F x ∈ N) → W ≤ N := by
    intro N h1 h2
    rw [hW]
    exact sInf_le ⟨h1, h2⟩
  have hspan : ∀ F ∈ Submodule.span ℂ L, F z ∈ W := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F hF => exact hLW F hF z hz0
    | zero => simp
    | add F G _ _ h1 h2 => exact W.add_mem h1 h2
    | smul c F _ h1 => exact W.smul_mem c h1
  refine ⟨hz0, ?_, ?_⟩
  · have hle : W ≤ W ⊓ ⨅ E ∈ S, W.comap E := by
      refine hmin _ ?_ ?_
      · refine ⟨hz0, ?_⟩
        simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap]
        intro E hE
        obtain ⟨F, hF, c, hc⟩ := hz E hE
        rw [hc]
        exact W.add_mem (hspan F hF) (W.smul_mem c hz0)
      · intro F hF x hx
        obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
        simp only [Submodule.mem_iInf, Submodule.mem_comap] at hx2
        refine Submodule.mem_inf.2 ⟨hLW F hF x hx1, ?_⟩
        simp only [Submodule.mem_iInf, Submodule.mem_comap]
        intro E hE
        have e : E (F x) = F (E x) + (E * F - F * E) x := by
          simp [Module.End.mul_apply]
        rw [e]
        exact W.add_mem (hLW F hF _ (hx2 E hE)) (hx2 _ (hS E hE F (hL hF)))
    intro E hE x hx
    have h2 := (Submodule.mem_inf.1 (hle hx)).2
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at h2
    exact h2 E hE
  · have hge : Submodule.span ℂ {z} ⊔ ⨆ F ∈ L, W.map F ≤ W := by
      refine sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hz0) (iSup₂_le fun F hF => ?_)
      rintro _ ⟨x, hx, rfl⟩
      exact hLW F hF x hx
    refine le_antisymm (hmin _ ?_ ?_) hge
    · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self z)
    · intro F hF x hx
      refine Submodule.mem_sup_right ?_
      exact (le_iSup₂_of_le (f := fun F (_ : F ∈ L) => W.map F) F hF le_rfl) ⟨x, hge hx, rfl⟩
end PositivityTheory.KReal
