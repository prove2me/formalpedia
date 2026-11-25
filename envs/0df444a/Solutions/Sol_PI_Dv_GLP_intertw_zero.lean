-- Prove2me | solution 1 for PI.Dv.GLP.intertw_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:39:16.810826+00:00
-- url     : https://prove2.me/submissions/6d96ff7f-3661-4182-81b2-0dd9c9c47c9f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw
import Theorems.Thm_PI_Dv_GLP_intertw_alg
import Theorems.Thm_PI_Dv_GLP_exists_end_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Representation
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLP
theorem _root_.solution (T : GoodSet K G) {s t : T.S} (hst : s ≠ t) (f : T.W s →ₗ[K] T.W t)
    (hf : ∀ g x, f (T.tau s g x) = T.tau t g (f x)) : f = 0 := by
  by_contra hne
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    apply hne
    ext y
    obtain ⟨b, hb⟩ := exists_end_map (K := K) hx0 y
    obtain ⟨a, rfl⟩ := T.irr s b
    rw [← hb, intertw_alg _ _ f hf a x, LinearMap.mem_ker.1 hx, map_zero]
    rfl
  have hsurj : Function.Surjective f := by
    obtain ⟨y0, hy0⟩ : ∃ y0, f y0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (LinearMap.ext h)
    intro z
    obtain ⟨b, hb⟩ := exists_end_map (K := K) hy0 z
    obtain ⟨a, rfl⟩ := T.irr t b
    exact ⟨(T.tau s).asAlgebraHom a y0, by rw [intertw_alg _ _ f hf a y0, hb]⟩
  let e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  apply hst
  apply T.inj
  funext g
  have : T.tau t g = e.conj (T.tau s g) := by
    ext z
    obtain ⟨x, rfl⟩ := hsurj z
    have hx : e.symm (f x) = x := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hx]
    rw [← hf g x]
    rfl
  simp only
  rw [this, LinearMap.trace_conj']
end PI.Dv.GLP
