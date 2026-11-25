-- Prove2me | solution 1 for PI.VolStabSW.witt_tuple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:29.533882+00:00
-- url     : https://prove2.me/submissions/5ec27fee-fe5a-4139-a235-99d77f6310b2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_HformSmulRight
import Theorems.Thm_PI_VolStabSW_hSes_apply
import Theorems.Thm_PI_VolStabSW_hSes_herm
import Theorems.Thm_PI_VolStabSW_hSes_nondeg
import Theorems.Thm_Formalism_UG_P_hform_mulVec
import Theorems.Thm_Formalism_UG_P_hform_single
import Theorems.Thm_witt_extension_theorem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
variable {E : Type} [Field E] {M : ℕ}
variable [StarRing E]
variable [CharZero E]
namespace PI.VolStabSW
theorem _root_.solution (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, starRingEnd E (J j i) = J i j)
    (hdet : J.det ≠ 0) {a : ℕ} (X0 X : Fin a → Fin M → E) (h0 : LinearIndependent E X0)
    (h1 : LinearIndependent E X)
    (hG : ∀ i j, Formalism.UG.hform (starRingEnd E) J (X i) (X j) =
      Formalism.UG.hform (starRingEnd E) J (X0 i) (X0 j)) :
    ∃ g ∈ Formalism.UG.UJ (starRingEnd E) J, ∀ i, (g : Matrix (Fin M) (Fin M) E) *ᵥ X0 i = X i := by
  let U := Submodule.span E (Set.range X0)
  let bU : Module.Basis (Fin a) E U := Module.Basis.span h0
  have hb : ∀ i, ((bU i : U) : Fin M → E) = X0 i := fun i => by
    show ((Module.Basis.span h0 i : U) : Fin M → E) = X0 i
    rw [Module.Basis.span_apply]
  let f : U →ₗ[E] (Fin M → E) := bU.constr E X
  have hf : ∀ i, f (bU i) = X i := fun i => bU.constr_basis E X i
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hs := bU.sum_repr u
    rw [← hs] at hu
    simp only [map_sum, map_smul, hf] at hu
    have hc := (Fintype.linearIndependent_iff.mp h1) _ hu
    rw [← hs]
    simp [hc]
  have key : ((hSes J).comp f).compl₂ f = ((hSes J).comp U.subtype).compl₂ U.subtype := by
    refine LinearMap.ext_basis bU bU fun i j => ?_
    show hSes J (f (bU i)) (f (bU j)) = hSes J ((bU i : U) : Fin M → E) ((bU j : U) : Fin M → E)
    rw [hf, hf, hb, hb]
    exact hG i j
  have hiso : ∀ x y : U, hSes J (f x) (f y) = hSes J x y := fun x y =>
    DFunLike.congr_fun (DFunLike.congr_fun key x) y
  obtain ⟨g, hgiso, hgf⟩ :=
    witt_extension_theorem E (Fin M → E) (hSes J) (hSes_herm J hJ) (hSes_nondeg J hdet) U f hinj hiso
  let m : Matrix (Fin M) (Fin M) E := LinearMap.toMatrix' (g : (Fin M → E) →ₗ[E] (Fin M → E))
  let mi : Matrix (Fin M) (Fin M) E :=
    LinearMap.toMatrix' (g.symm : (Fin M → E) →ₗ[E] (Fin M → E))
  have hc1 : (g : (Fin M → E) →ₗ[E] (Fin M → E)).comp (g.symm : (Fin M → E) →ₗ[E] (Fin M → E)) =
      LinearMap.id := LinearMap.ext fun x => by simp
  have hc2 : (g.symm : (Fin M → E) →ₗ[E] (Fin M → E)).comp (g : (Fin M → E) →ₗ[E] (Fin M → E)) =
      LinearMap.id := LinearMap.ext fun x => by simp
  have hm1 : m * mi = 1 := by
    simp only [m, mi]
    rw [← LinearMap.toMatrix'_comp, hc1, LinearMap.toMatrix'_id]
  have hm2 : mi * m = 1 := by
    simp only [m, mi]
    rw [← LinearMap.toMatrix'_comp, hc2, LinearMap.toMatrix'_id]
  have hmv : ∀ v, m *ᵥ v = g v := fun v => by
    simp only [m]
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  refine ⟨⟨m, mi, hm1, hm2⟩, ?_, ?_⟩
  · show Formalism.UG.cT (starRingEnd E) m * J * m = J
    ext i j
    have h := hgiso (Pi.single i 1) (Pi.single j 1)
    rw [hSes_apply, hSes_apply, ← hmv, ← hmv, Formalism.UG.P.hform_mulVec, Formalism.UG.P.hform_single,
      Formalism.UG.P.hform_single] at h
    exact h
  · intro i
    show m *ᵥ X0 i = X i
    rw [hmv, ← hb i]
    exact (hgf (bU i)).trans (hf i)
end PI.VolStabSW
