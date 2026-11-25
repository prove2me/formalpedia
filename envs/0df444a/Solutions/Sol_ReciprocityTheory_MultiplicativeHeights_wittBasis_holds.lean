-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.wittBasis_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:12:19.440127+00:00
-- url     : https://prove2.me/submissions/a8a878fa-382e-483c-a6cd-eb9e4d896f30

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAB
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_witt_ker
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_waExt_last
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_waExt_mid
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_waExt_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_main
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.waExt_last
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.waExt_mid
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.waExt_zero



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : WittBasisStatement := by
  intro K _ _ r S hdet
  have hnd : ∀ x ∈ (⊤ : Submodule K (Fin r → K)),
      (∀ y ∈ (⊤ : Submodule K (Fin r → K)), S.h x y = 0) → x = 0 := by
    intro x _ hx
    have hrow : Matrix.vecMul (fun a => S.c (x a)) S.G = 0 := by
      funext b'
      have h1 := hx (Pi.single b' 1) Submodule.mem_top
      simpa [HermForm.h, Pi.single_apply, Matrix.vecMul, dotProduct] using h1
    have h2 : (fun a => S.c (x a)) = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hrow
    funext a
    have h3 := congrFun h2 a
    simp only [Pi.zero_apply, map_eq_zero] at h3
    exact h3
  obtain ⟨m, bb, g, -, hm, hW, hg⟩ := wa_main S r ⊤ (by rw [finrank_top, Module.finrank_fin_fun]) hnd
  have hgmid : ∀ k : Fin r, m ≤ (k : ℕ) → (k : ℕ) + m < r → g k ≠ 0 := by
    intro k hk1 hk2 hgk
    have ht := hg (Pi.single k 1) (fun i hi => by
      rw [Pi.single_apply, if_neg]
      rintro rfl
      omega) (by
      rw [Finset.sum_eq_single k]
      · simp [hgk]
      · intro i _ hik
        simp [Pi.single_eq_of_ne hik]
      · intro h
        exact absurd (Finset.mem_univ k) h)
    have := congrFun ht k
    simp at this
  have hlin : ∀ (x v : Fin r → K), S.h x (fun a => ∑ i, bb i a * v i) = ∑ i, v i * S.h x (bb i) := by
    intro x v
    simp only [HermForm.h, Finset.mul_sum]
    calc ∑ a, ∑ b', ∑ i, S.c (x a) * S.G a b' * (bb i b' * v i)
        = ∑ a, ∑ i, ∑ b', S.c (x a) * S.G a b' * (bb i b' * v i) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b', S.c (x a) * S.G a b' * (bb i b' * v i) := Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b', v i * (S.c (x a) * S.G a b' * bb i b') :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b' _ => by ring
  refine ⟨Matrix.of fun a i => bb i a, m, g, ?_, hm, ?_, hg⟩
  · intro hd
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    apply hv0
    have hPv : Matrix.mulVec (Matrix.of fun a i => bb i a) v = fun a => ∑ i, bb i a * v i := by
      funext a
      simp [Matrix.mulVec, dotProduct]
    refine wa_witt_ker r m g hgmid v fun p => ?_
    have h1 : S.h (bb p) (fun a => ∑ i, bb i a * v i) = 0 := by
      rw [← hPv, hv]
      simp [HermForm.h]
    rw [hlin] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun i _ => by rw [hW p i]
  · ext i j
    rw [← hW i j]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, HermForm.h,
      Finset.sum_mul]
    exact Finset.sum_comm
end ReciprocityTheory.MultiplicativeHeights
