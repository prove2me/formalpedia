-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.unfolding_matrix_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:38:35.56598+00:00
-- url     : https://prove2.me/submissions/e60bdd51-0741-4305-8f60-c1a9657f6497

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnfoldingMatrixFreeCoordinate
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_gh_eN_lt
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_gh_eN_ge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain Module
noncomputable section
namespace PI.TwistedEisensteinNonvanishing.W
open Loc LocE
section Vec
variable {E : Type} [Field E]
private theorem xx1_eN_apply {n' c' n c : ℕ} (y : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t : FC n' c' n c → E) {s : ℕ} (hs : s < n' + c') (l : Fin (n + c)) :
    xx1 y t (eN E (n' + c') s) l =
      if hf : IsFree n' n c l.1 s then t ⟨(l, ⟨s, hs⟩), hf⟩
      else if hs' : s < n' then (if hl : l.1 < n then LinearMap.toMatrix' y ⟨l.1, hl⟩ ⟨s, hs'⟩ else 0)
      else if l.1 = n + (s - n') then 1 else 0 := by
  rw [gh_eN_lt hs]
  unfold xx1
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rfl
end Vec
section Bd
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
end Bd
end PI.TwistedEisensteinNonvanishing.W
end
end

set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E : Type} [Field E]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {n' c' n c : ℕ} (y : (Fin n' → E) →ₗ[E] (Fin n → E)) (t t' : FC n' c' n c → E) (s : ℕ) (l : Fin (n + c)) :
    (xx1 y t - xx1 y t') (eN E (n' + c') s) l =
      if hs : s < n' + c' then (if hf : IsFree n' n c l.1 s then t ⟨(l, ⟨s, hs⟩), hf⟩ - t' ⟨(l, ⟨s, hs⟩), hf⟩ else 0) else 0 := by
  by_cases hs : s < n' + c'
  · rw [dif_pos hs, LinearMap.sub_apply, Pi.sub_apply, xx1_eN_apply y t hs, xx1_eN_apply y t' hs]
    split_ifs <;> first | rfl | exact sub_self _
  · rw [dif_neg hs, gh_eN_ge (not_lt.mp hs)]
    simp
end PI.TwistedEisensteinNonvanishing.W
