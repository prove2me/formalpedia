-- Prove2me | solution 1 for PI.OpWords.divide_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:45.612428+00:00
-- url     : https://prove2.me/submissions/73d97bc9-d310-4fcf-985c-313221d1380e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_DivideAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords
namespace PI.OpWords
theorem _root_.solution (hV : Vanish) (hD : DivT) (hRB : RBihom) (hRT : RTT) (hTW : TTWt)
    (K : Type) [Field K] [CharZero K] (k c : ℕ) : ∀ n : ℕ, ∀ (W : Submodule K (Pol K k)),
    W ≤ Bihom K k (c + n) → (∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W) → (∀ f ∈ W, WtLe K k c f) →
    ∀ f ∈ W, ∃ g ∈ Bihom K k c, f = tt K k ^ n * g := by
  intro n
  induction n with
  | zero =>
    intro W hW _ _ f hf
    exact ⟨f, by simpa using hW hf, by simp⟩
  | succ n ih =>
    intro W hW hst hwt f hf
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      have hf' : f ∈ weightedHomogeneousSubmodule K (wx 0) (c + (n + 1)) ⊓
          weightedHomogeneousSubmodule K (wxi 0) (c + (n + 1)) := hW hf
      have h1 := (Submodule.mem_inf.1 hf').1
      rw [mem_weightedHomogeneousSubmodule] at h1
      rw [mul_zero]
      ext m
      rw [coeff_zero]
      by_contra h
      have h2 := h1 h
      have h3 : m = 0 := by
        ext v
        rcases v with i | i <;> exact i.elim0
      rw [h3, map_zero] at h2
      omega
    · have htt : tt K k ≠ 0 := by
        intro h
        have h1 := congrArg (eval (fun _ : Fin k ⊕ Fin k => (1 : K))) h
        simp [tt] at h1
        omega
      have hdiv : ∀ f ∈ W, ∃ g ∈ Bihom K k (c + n), f = tt K k * g := by
        intro f hf
        have hv := hV K k (c + (n + 1)) c W hW hst hwt (by omega) f hf
        obtain ⟨g, hg, rfl⟩ := hD K k (c + (n + 1)) (by omega) f (hW hf) hv
        exact ⟨g, by simpa using hg, rfl⟩
      let W' : Submodule K (Pol K k) := W.comap (LinearMap.mulLeft K (tt K k))
      have hmem : ∀ g, g ∈ W' ↔ tt K k * g ∈ W := fun g => Iff.rfl
      have hW' : W' ≤ Bihom K k (c + n) := by
        intro g hg
        obtain ⟨g', hg', he⟩ := hdiv _ ((hmem g).1 hg)
        rw [mul_left_cancel₀ htt he]
        exact hg'
      have hst' : ∀ f ∈ W', ∀ a b, Rop K k a b f ∈ W' := by
        intro g hg a b
        rw [hmem, ← hRT K k a b g]
        exact hst _ ((hmem g).1 hg) a b
      have hwt' : ∀ f ∈ W', WtLe K k c f := by
        intro g hg
        exact hTW K k c g (hwt _ ((hmem g).1 hg))
      obtain ⟨g, hg, rfl⟩ := hdiv f hf
      obtain ⟨g'', hg'', rfl⟩ := ih W' hW' hst' hwt' g ((hmem g).2 hf)
      exact ⟨g'', hg'', by ring⟩
end PI.OpWords
