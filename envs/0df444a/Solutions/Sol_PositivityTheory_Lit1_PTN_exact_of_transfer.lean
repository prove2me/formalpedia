-- Prove2me | solution 1 for PositivityTheory.Lit1.PTN.exact_of_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:31:38.693945+00:00
-- url     : https://prove2.me/submissions/eba3484e-0d24-4dfd-bfc3-7187ff87aec6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsDefs
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsTransfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion
open PositivityTheory PositivityTheory.Lit1 PositivityTheory.Lit1.PTN
variable {R : Type} [CommRing R]
namespace PositivityTheory.Lit1.PTN
theorem _root_.solution {A B C A' B' C' : Type} [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup A'] [Module R A'] [AddCommGroup B']
    [Module R B'] [AddCommGroup C'] [Module R C'] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (f' : A' →ₗ[R] B') (g' : B' →ₗ[R] C') (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B') (eC : C ≃ₗ[R] C')
    (u v : Rˣ) (hf : ∀ a, f' (eA a) = u • eB (f a)) (hg : ∀ b, g' (eB b) = v • eC (g b))
    (h : Function.Exact f' g') : Function.Exact f g := by
  unfold Function.Exact at h ⊢
  intro b
  constructor
  · intro hb
    have h1 : g' (eB b) = 0 := by rw [hg, hb, map_zero, smul_zero]
    obtain ⟨a', ha'⟩ := (h (eB b)).1 h1
    refine ⟨(u : R) • eA.symm a', eB.injective ?_⟩
    have := hf (eA.symm a')
    rw [LinearEquiv.apply_symm_apply, ha'] at this
    rw [map_smul, map_smul, this, Units.smul_def]
  · rintro ⟨a, rfl⟩
    have h2 : g' (f' (eA a)) = 0 := (h _).2 ⟨_, rfl⟩
    rw [hf, Units.smul_def, map_smul, hg, ← Units.smul_def, smul_eq_zero_iff_eq,
      smul_eq_zero_iff_eq, LinearEquiv.map_eq_zero_iff] at h2
    exact h2
end PositivityTheory.Lit1.PTN
