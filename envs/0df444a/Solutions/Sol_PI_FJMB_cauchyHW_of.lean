-- Prove2me | solution 1 for PI.FJMB.cauchyHW_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:19:06.679979+00:00
-- url     : https://prove2.me/submissions/6d7c9bbf-bfe4-47e0-a6dc-b1fe5daec855

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurDiag
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurCauchy
import Theorems.Thm_PI_FJMB_exists_support_of_killS
import Theorems.Thm_PI_FJMB_aeval_killS_free
import Theorems.Thm_PI_FJMB_bRow_mul_free
import Theorems.Thm_PI_FJMB_bCol_mul_free
import Theorems.Thm_PI_FJMB_diag_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}
namespace PI.FJMB
theorem _root_.solution (hA : HypAnti) (hS : HypShape) (hD : HypDiag) (hF : HypFree) : PI.FJM.CauchyHW := by
  intro τ m n ι hι α β P hP hrow hcol hsum hα hβ
  have hinvP : HWB ι P := ⟨hrow, hcol⟩
  have hne : aeval (killS (offD ι)) P ≠ 0 := fun h0 =>
    hP (diag_zero m n ι hι P hinvP h0)
  obtain ⟨e, heP, he0⟩ := exists_support_of_killS hne
  have hoff : ∀ (i : Fin m) (k : Fin n), (i : ℕ) ≠ k → e (ι (i, k)) = 0 :=
    fun i k h => he0 _ ⟨i, k, rfl, h⟩
  have hrowsum : ∀ (i : Fin m) (k : Fin n), (i : ℕ) = k → α i = e (ι (i, k)) := by
    intro i k hik
    rw [← (hsum e heP).1 i, Finset.sum_eq_single k]
    · intro k' _ hk'
      exact hoff i k' fun h => hk' (Fin.ext (h.symm.trans hik))
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hcolsum : ∀ (i : Fin m) (k : Fin n), (i : ℕ) = k → β k = e (ι (i, k)) := by
    intro i k hik
    rw [← (hsum e heP).2 k, Finset.sum_eq_single i]
    · intro i' _ hi'
      exact hoff i' k fun h => hi' (Fin.ext (h.trans hik.symm))
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hrowlt : ∀ i : Fin m, (i : ℕ) < n := by
    intro i
    by_contra hi
    push_neg at hi
    have h0 : α i = 0 := by
      rw [← (hsum e heP).1 i]
      exact Finset.sum_eq_zero fun k _ => hoff i k (by have := k.isLt; omega)
    exact (hα i).ne' h0
  have hcollt : ∀ k : Fin n, (k : ℕ) < m := by
    intro k
    by_contra hk
    push_neg at hk
    have h0 : β k = 0 := by
      rw [← (hsum e heP).2 k]
      exact Finset.sum_eq_zero fun i _ => hoff i k (by have := i.isLt; omega)
    exact (hβ k).ne' h0
  have hmn : m = n := by
    apply le_antisymm
    · by_contra h
      push_neg at h
      exact lt_irrefl n (hrowlt ⟨n, h⟩)
    · by_contra h
      push_neg at h
      exact lt_irrefl m (hcollt ⟨m, h⟩)
  have hanti : Antitone α := hA τ m n ι hι α P hP hrow fun e he i => (hsum e he).1 i
  refine ⟨hmn, hanti, fun i k h => (hrowsum i k h).trans (hcolsum i k h).symm, ?_⟩
  subst n
  obtain ⟨hMinv, hMdiag⟩ := hS τ m ι hι α hanti
  obtain ⟨hMr, hMc⟩ := hMinv
  have hDP := hD τ m ι hι α P fun e he i => (hsum e he).1 i
  have hFP := hF τ m m ι hι P
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = aeval (diagOne' ι) P := ⟨_, rfl⟩
  rw [← hQ] at hDP hFP
  refine ⟨Q, hFP, ?_⟩
  rw [← sub_eq_zero]
  refine diag_zero m m ι hι _ ⟨fun a b hab => ?_, fun c d hcd => ?_⟩ ?_
  · rw [map_sub, bRow_mul_free ι a b _ Q hFP, hrow a b hab, hMr a b hab, zero_mul, sub_zero]
  · rw [map_sub, bCol_mul_free ι c d _ Q hFP, hcol c d hcd, hMc c d hcd, zero_mul, sub_zero]
  · have hQfree : ∀ f ∈ Q.support, ∀ v ∈ offD ι, f v = 0 := by
      rintro f hf v ⟨i, k, rfl, -⟩
      exact hFP f hf (i, k)
    rw [map_sub, map_mul, hMdiag, aeval_killS_free hQfree, hDP, sub_self]
end PI.FJMB
