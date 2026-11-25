-- Prove2me | solution 1 for PI.SqPairLocal.FixD.hens_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:29:22.883981+00:00
-- url     : https://prove2.me/submissions/7cedfccf-9b00-425b-a864-ea01e611d8ff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnitIffSub
import Theorems.Thm_PI_SqPairLocal_FixD_mem_max_sub
import Theorems.Thm_PI_SqPairLocal_FixD_root_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open PI PI.SqPairLocal PI.SqPairLocal.FixD
variable {R : Type} [CommRing R] [IsDomain R] (σ : R ≃+* R)
namespace PI.SqPairLocal.FixD
theorem _root_.solution [HenselianLocalRing R] [IsLocalRing (fixSub σ)] : HenselianLocalRing (fixSub σ) where
  is_henselian f hf a₀ h₁ h₂ := by
    set φ : fixSub σ →+* R := (fixSub σ).subtype with hφ
    set g : R[X] := f.map φ with hgdef
    have hev : ∀ a : fixSub σ, g.eval (a : R) = φ (f.eval a) := fun a => by
      rw [hgdef, eval_map]; exact eval₂_at_apply φ a
    have hevd : ∀ a : fixSub σ, g.derivative.eval (a : R) = φ (f.derivative.eval a) := fun a => by
      rw [hgdef, derivative_map, eval_map]; exact eval₂_at_apply φ a
    have hcomp : (σ : R →+* R).comp φ = φ := by
      ext x; exact x.2
    have hσev : ∀ b : R, σ (g.eval b) = g.eval (σ b) := fun b => by
      rw [hgdef, eval_map, eval_map]
      have := hom_eval₂ f φ (σ : R →+* R) b
      rw [hcomp] at this
      exact this
    have hg : g.Monic := hf.map φ
    have h₁' : g.eval (a₀ : R) ∈ maximalIdeal R := by
      rw [hev]; exact (mem_max_sub σ _).1 h₁
    have h₂' : IsUnit (g.derivative.eval (a₀ : R)) := by
      rw [hevd]; exact h₂.map φ
    obtain ⟨b, hb, hba⟩ := HenselianLocalRing.is_henselian g hg (a₀ : R) h₁' h₂'
    have hσb : g.IsRoot (σ b) := by
      show g.eval (σ b) = 0
      rw [← hσev, hb.eq_zero, map_zero]
    have hσa : σ (a₀ : R) = a₀ := a₀.2
    have hσba : σ b - a₀ ∈ maximalIdeal R := by
      have e : σ b - a₀ = σ (b - a₀) := by rw [map_sub, hσa]
      rw [e]
      by_contra hn
      rw [notMem_maximalIdeal] at hn
      have hu := hn.map (σ.symm : R →+* R)
      have hu' : IsUnit (b - (a₀ : R)) := by simpa using hu
      exact (notMem_maximalIdeal.2 hu') hba
    have hfix : σ b = b := root_unique g a₀ (σ b) b hσb hb hσba hba h₂'
    refine ⟨⟨b, hfix⟩, ?_, ?_⟩
    · show f.eval _ = 0
      apply Subtype.ext
      have := hev ⟨b, hfix⟩
      rw [show ((⟨b, hfix⟩ : fixSub σ) : R) = b from rfl, hb.eq_zero] at this
      exact this.symm
    · rw [mem_max_sub]
      exact hba
end PI.SqPairLocal.FixD
