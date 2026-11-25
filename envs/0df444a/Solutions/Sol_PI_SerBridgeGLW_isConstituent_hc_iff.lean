-- Prove2me | solution 1 for PI.SerBridgeGLW.isConstituent_hc_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:10.489925+00:00
-- url     : https://prove2.me/submissions/b8389889-c54d-48c7-bcba-567188afdee8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
noncomputable section
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
open PI PI.SerBridgeGLW
namespace PI.SerBridgeGLW
theorem _root_.solution (K : Type) [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {s : ℕ} (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (V : FDRep ℂ (GL ι K)) :
    IsConstituent V (hcRep K b lam) ↔
      ∃ ψ : V →ₗ[ℂ] PiTensorProduct ℂ (fun c => (lam c : Type)), ψ ≠ 0 ∧
        ∀ p : parab K b, ψ ∘ₗ V.ρ p.1 = infl K b lam p ∘ₗ ψ := by
  have key : ∀ (f : hcSpace K b lam) (g x : GL ι K),
      ((hcRep K b lam g f : hcSpace K b lam) : GL ι K → PiTensorProduct ℂ (fun c => (lam c : Type))) x =
        (f : GL ι K → PiTensorProduct ℂ (fun c => (lam c : Type))) (x * g) := fun _ _ _ => rfl
  constructor
  · rintro ⟨φ, hφ, hne⟩
    have hφ' : ∀ g, φ ∘ₗ V.ρ g = hcRep K b lam g ∘ₗ φ := hφ
    have hval : ∀ (v : V) (x : GL ι K),
        ((φ (V.ρ x v) : hcSpace K b lam) : GL ι K → PiTensorProduct ℂ (fun c => (lam c : Type))) 1 =
          ((φ v : hcSpace K b lam) : GL ι K → PiTensorProduct ℂ (fun c => (lam c : Type))) x := by
      intro v x
      have := congrArg (fun F : V →ₗ[ℂ] hcSpace K b lam =>
        ((F v : hcSpace K b lam) : GL ι K → PiTensorProduct ℂ (fun c => (lam c : Type))) 1) (hφ' x)
      simpa [key] using this
    refine ⟨LinearMap.proj (R := ℂ) (φ := fun _ : GL ι K => PiTensorProduct ℂ (fun c => (lam c : Type))) 1 ∘ₗ
      (hcSpace K b lam).subtype ∘ₗ φ, ?_, ?_⟩
    · intro h0
      apply hne
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      funext x
      rw [← hval v x]
      exact LinearMap.congr_fun h0 (V.ρ x v)
    · intro p
      apply LinearMap.ext
      intro v
      show ((φ (V.ρ p.1 v) : hcSpace K b lam) : GL ι K → PiTensorProduct ℂ (fun c => (lam c : Type))) 1 =
        infl K b lam p (((φ v : hcSpace K b lam) : GL ι K → PiTensorProduct ℂ (fun c => (lam c : Type))) 1)
      rw [hval, ← (φ v).2 p 1, mul_one]
  · rintro ⟨ψ, hne, hψ⟩
    let φ : V →ₗ[ℂ] hcSpace K b lam :=
      { toFun := fun v => ⟨fun x => ψ (V.ρ x v), fun p x => by
            show ψ (V.ρ (p.1 * x) v) = infl K b lam p (ψ (V.ρ x v))
            rw [map_mul, Module.End.mul_apply]
            exact LinearMap.congr_fun (hψ p) (V.ρ x v)⟩
        map_add' := fun v w => by
          apply Subtype.ext
          funext x
          simp
        map_smul' := fun c v => by
          apply Subtype.ext
          funext x
          simp }
    refine ⟨φ, ?_, ?_⟩
    · intro g
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      funext x
      show ψ (V.ρ x (V.ρ g v)) = ψ (V.ρ (x * g) v)
      rw [map_mul, Module.End.mul_apply]
    · intro h0
      apply hne
      apply LinearMap.ext
      intro v
      have := congrArg (fun f : hcSpace K b lam =>
        (f : GL ι K → PiTensorProduct ℂ (fun c => (lam c : Type))) 1) (LinearMap.congr_fun h0 v)
      simpa [φ] using this
end PI.SerBridgeGLW
