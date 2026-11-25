-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_exists_eventually_const_1a8f49af4e5a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:08:25.405654+00:00
-- url     : https://prove2.me/submissions/df64d465-9cd5-4896-b4ed-81daf760340d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_mixedDiff_eq_3099f1494d11
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_totalDegree_foldr_dPoly_le_81b7dcde44bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_foldr_gStep_eval_12f62d633685
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_foldr_gStep_cast_247e25696281
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_foldr_gStep_congr_ea53fc887cec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
theorem _root_.solution (h : MultigradedHilbertPolynomial.Statement.{u}) (F : Type u)
    [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (q : Ideal (MRing ι F)) (d : ℕ) (hq : IsMultiProjPrime q)
    (hdim : ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞))
    (bs : Fin d → K → ℤ) : ∃ c, ∀ᶠ m in atTop, mixedDiff bs (hilbFn q) m = c := by
  obtain ⟨p, a₀, hdeg, hp⟩ := h F K ι q d hq hdim
  have hev : ∀ᶠ m in atTop, ((hilbFn q m : ℤ) : ℚ) = eval (fun k => (m k : ℚ)) p := by
    filter_upwards [eventually_ge_atTop (fun _ : K => (a₀ : ℤ))] with m hm
    have hm' : ∀ k, (a₀ : ℤ) ≤ m k := fun k => hm k
    have e1 : (fun k => (((m k).toNat : ℕ) : ℤ)) = m :=
      funext fun k => Int.toNat_of_nonneg (by have := hm' k; omega)
    have e2 : (fun k => (((m k).toNat : ℕ) : ℚ)) = fun k => (m k : ℚ) := by
      funext k
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by have := hm' k; omega)]
    have := hp (fun k => (m k).toNat) (fun k => by have := hm' k; omega)
    rw [e1, e2] at this
    exact this
  set P := (List.ofFn bs).foldr dPoly p with hP
  have hP0 : P.totalDegree = 0 := by
    have := totalDegree_foldr_dPoly_le (List.ofFn bs) p
    rw [List.length_ofFn, ← hP] at this
    exact Nat.eq_zero_of_le_zero (this.trans (Nat.sub_eq_zero_of_le hdeg).le)
  obtain ⟨c, hc⟩ : ∃ c, P = C c := ⟨_, totalDegree_eq_zero_iff_eq_C.1 hP0⟩
  have hconst : ∀ᶠ m in atTop, ((mixedDiff bs (hilbFn q) m : ℤ) : ℚ) = c := by
    filter_upwards [foldr_gStep_congr (List.ofFn bs) hev] with m hm
    rw [mixedDiff_eq, foldr_gStep_cast, hm, foldr_gStep_eval, ← hP, hc, eval_C]
  obtain ⟨m₀, hm₀⟩ := hconst.exists
  refine ⟨mixedDiff bs (hilbFn q) m₀, ?_⟩
  filter_upwards [hconst] with m hm
  exact_mod_cast hm.trans hm₀.symm
end GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
