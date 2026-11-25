-- Prove2me | solution 1 for PI.StabPairsW.Sset_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:53:10.716823+00:00
-- url     : https://prove2.me/submissions/1e071413-c095-4a04-bec2-faecd1caae6c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward
import Theorems.Thm_PI_StabPairsW_mul_of_col
import Theorems.Thm_PI_StabPairsW_expand_of_tail
import Theorems.Thm_PI_StabPairsW_coefOf_UT
import Theorems.Thm_PI_StabPairsW_uMap_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (hz : StdZ k r z) (s : B.Mat k r) (hs : s ∈ Sset k r z) :
    s ∈ B.GV k r ∧ s * Ff k r z = Ff k r z * uMap k r z s ∧ uMap k r z s ∈ UTset (r + 1) := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have hGV : h * m ∈ B.GV k r := by
    show (h * m)ᴴ * Hpk k r * (h * m) = Hpk k r
    have h1 : hᴴ * Hpk k r * h = Hpk k r := hh.1
    have h2 : mᴴ * Hpk k r * m = Hpk k r := hm.1
    rw [Matrix.conjTranspose_mul]
    calc mᴴ * hᴴ * Hpk k r * (h * m) = mᴴ * (hᴴ * Hpk k r * h) * m := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [h1, h2]
  have htail : ∀ b : Fin (r + 1), ∀ i : Fin (2 * r + k + 1), b.val ≤ i.val →
      (m *ᵥ fvec k r z b) i = fvec k r z b i := by
    intro b i hbi
    by_cases hbr : b.val < r
    · have hf : fvec k r z b = bvec (eI k r ⟨b.val, hbr⟩) := by simp [fvec, hbr]
      rw [hf]
      have e : (m *ᵥ bvec (eI k r ⟨b.val, hbr⟩)) i = m i (eI k r ⟨b.val, hbr⟩) := by
        simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [e, hm.2.1 ⟨b.val, hbr⟩ i hbi]
      simp [bvec, Pi.single_apply]
    · have hf : fvec k r z b = z := by simp [fvec, hbr]
      rw [hf]
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single i]
      · by_cases hik : i.val ≤ r + k
        · rw [hm.2.2 i i (by omega) hik (by omega), if_pos rfl, one_mul]
        · rw [hz.1 i (Or.inr (by omega)), mul_zero]
      · intro j _ hji
        by_cases hj1 : r ≤ j.val
        · by_cases hj2 : j.val ≤ r + k
          · rw [hm.2.2 i j hj1 hj2 (by omega), if_neg (Ne.symm hji), zero_mul]
          · rw [hz.1 j (Or.inr (not_le.1 hj2)), mul_zero]
        · rw [hz.1 j (Or.inl (not_le.1 hj1)), mul_zero]
      · simp
  have hmX : m * Ff k r z = Ff k r z *
      (Matrix.of fun a b => coefOf (k := k) b (m *ᵥ fvec k r z b) a) :=
    mul_of_col z m _ (fun b => expand_of_tail z hz.1 b _ (htail b))
  have hhF : h * Ff k r z = Ff k r z := by
    ext i a
    have e : h *ᵥ fvec k r z a = fvec k r z a := by
      unfold fvec
      split_ifs
      · exact (hh.2.1 _).1
      · exact hh.2.2
    have e2 := congrFun e i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Ff] using e2
  have hsF : h * m * Ff k r z = Ff k r z *
      (Matrix.of fun a b => coefOf (k := k) b (m *ᵥ fvec k r z b) a) := by
    rw [Matrix.mul_assoc, hmX, ← Matrix.mul_assoc, hhF]
  have hu := uMap_eq z hz _ _ hsF
  refine ⟨hGV, ?_, ?_⟩
  · rw [hu]
    exact hsF
  · rw [hu]
    exact coefOf_UT (fun b => m *ᵥ fvec k r z b)
end PI.StabPairsW
