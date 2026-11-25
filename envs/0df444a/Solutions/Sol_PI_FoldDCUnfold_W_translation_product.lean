-- Prove2me | solution 1 for PI.FoldDCUnfold.W.translation_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:40:28.364804+00:00
-- url     : https://prove2.me/submissions/2528e63a-3b46-47ac-b8cc-3116053c30c4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FoldingUnfolding_TransExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FoldingUnfolding_TranslationIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
open PI PI.FoldDCUnfold PI.FoldDCUnfold.W
universe u
namespace PI.FoldDCUnfold.W
theorem _root_.solution : TransProd.{u} := by
  intro G _ Γ S H E D hHS hSΓ hE hD
  have key : ∀ (e₁ e₂ : E) (d₁ d₂ : D), (e₁ : G) * d₁ = e₂ * d₂ → e₁ = e₂ ∧ d₁ = d₂ := by
    intro e₁ e₂ d₁ d₂ h
    have hγ : (e₁ : G) * d₁ ∈ Γ := Γ.mul_mem (hSΓ (hE.1 e₁.2)) (hD.1 d₁.2)
    have u := (hD.2 _ hγ).unique (y₁ := (⟨e₁, hE.1 e₁.2⟩, d₁)) (y₂ := (⟨e₂, hE.1 e₂.2⟩, d₂))
      rfl h.symm
    have hd : d₁ = d₂ := congrArg Prod.snd u
    have he : (e₁ : G) = e₂ := congrArg (fun p : S × D => ((p.1 : S) : G)) u
    exact ⟨Subtype.ext he, hd⟩
  refine ⟨fun p q h => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := key p.1 q.1 p.2 q.2 h
    exact Prod.ext h1 h2
  · rintro _ ⟨p, rfl⟩
    exact Γ.mul_mem (hSΓ (hE.1 p.1.2)) (hD.1 p.2.2)
  · intro γ hγ
    obtain ⟨⟨s, d⟩, hsd, hsd_u⟩ := hD.2 γ hγ
    obtain ⟨⟨h, e⟩, hhe, hhe_u⟩ := hE.2 s s.2
    have hsd' : (s : G) * d = γ := hsd
    have hhe' : (h : G) * e = s := hhe
    refine ⟨(h, ⟨(e : G) * d, ⟨(e, d), rfl⟩⟩), ?_, ?_⟩
    · show (h : G) * ((e : G) * d) = γ
      rw [← mul_assoc, hhe']
      exact hsd'
    · rintro ⟨h', ⟨x, ⟨⟨e', d'⟩, rfl⟩⟩⟩ hx
      have hx' : (h' : G) * ((e' : G) * d') = γ := hx
      have hs' : (h' : G) * e' ∈ S := S.mul_mem (hHS h'.2) (hE.1 e'.2)
      have u1 := hsd_u (⟨(h' : G) * e', hs'⟩, d')
        (by show (h' : G) * e' * d' = γ; rw [mul_assoc]; exact hx')
      have hd' : d' = d := congrArg Prod.snd u1
      have hs1 : (h' : G) * e' = s := congrArg (fun p : S × D => ((p.1 : S) : G)) u1
      have u2 := hhe_u (h', e') hs1
      have hh : h' = h := congrArg Prod.fst u2
      have he : e' = e := congrArg Prod.snd u2
      subst hd' hh he
      rfl
end PI.FoldDCUnfold.W
