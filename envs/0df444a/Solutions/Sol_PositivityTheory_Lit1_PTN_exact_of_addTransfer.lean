-- Prove2me | solution 1 for PositivityTheory.Lit1.PTN.exact_of_addTransfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:31:36.598055+00:00
-- url     : https://prove2.me/submissions/c64b424a-60c5-471c-a10e-cb7f4ae73b27

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsAddTransfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Lit1 PositivityTheory.Lit1.PTN
namespace PositivityTheory.Lit1.PTN
theorem _root_.solution {A B C A' B' C' : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C'] {f : A → B} {g : B → C}
    (hf0 : ∀ a a', f (a + a') = f a + f a') (hg0 : ∀ b b', g (b + b') = g b + g b')
    (f' : A' →+ B') (g' : B' →+ C') (eA : A ≃+ A') (eB : B ≃+ B') (eC : C ≃+ C') (u v : ℤˣ)
    (hf : ∀ a, f' (eA a) = (u : ℤ) • eB (f a)) (hg : ∀ b, g' (eB b) = (v : ℤ) • eC (g b))
    (h : Function.Exact f' g') : Function.Exact f g := by
  let F : A →+ B := AddMonoidHom.mk' f hf0
  have hu : (u : ℤ) * u = 1 := by rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  have hv : (v : ℤ) * v = 1 := by rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  intro b
  constructor
  · intro hb
    have h1 : g' (eB b) = 0 := by rw [hg, show g b = 0 from hb, map_zero, smul_zero]
    obtain ⟨a', ha'⟩ := (h (eB b)).1 h1
    refine ⟨(u : ℤ) • eA.symm a', ?_⟩
    have h2 := hf (eA.symm a')
    rw [AddEquiv.apply_symm_apply, ha'] at h2
    have h3 : f ((u : ℤ) • eA.symm a') = (u : ℤ) • f (eA.symm a') := map_zsmul F _ _
    apply eB.injective
    rw [h3, map_zsmul, h2]
  · rintro ⟨a, rfl⟩
    have h1 : eB (f a) = (u : ℤ) • f' (eA a) := by
      rw [hf, smul_smul, hu, one_smul]
    have h2 : g' (f' (eA a)) = 0 := (h _).2 ⟨_, rfl⟩
    have h3 : (v : ℤ) • eC (g (f a)) = 0 := by
      rw [← hg, h1, map_zsmul, h2, smul_zero]
    have h4 : eC (g (f a)) = 0 := by
      rw [← one_smul ℤ (eC (g (f a))), ← hv, ← smul_smul, h3, smul_zero]
    exact (map_eq_zero_iff eC eC.injective).1 h4
end PositivityTheory.Lit1.PTN
