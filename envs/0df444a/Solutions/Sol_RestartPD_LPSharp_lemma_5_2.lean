-- Prove2me | solution 2 for RestartPD.LPSharp.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T10:04:21.997525+00:00
-- url     : https://prove2.me/submissions/7a54536e-832e-42e1-a42b-da73371703de

import Mathlib
import Definitions.Def_RestartPD_LPSharp_LP
import Theorems.Thm_RestartPD_LPSharp_lemma_4

-- carved verbatim out of submission 14630b3e-f5ea-425e-80b7-395f30df9c74, lines 205-236

section
set_option autoImplicit false
open scoped InnerProductSpace Matrix
open RestartPD.LPSharp
variable {n m : ℕ}

lemma le_rho (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z w : PDSpace n m)
    (r : ℝ) (hr : 0 < r) (hw : w ∈ Wball lpX Set.univ r z) :
    ((gapAt (lpL A b c) z w / r : ℝ) : EReal) ≤ rho (lpL A b c) lpX Set.univ r z := by
  rw [rho, if_neg hr.ne']
  exact le_iSup_of_le w (le_iSup_of_le hw le_rfl)

lemma rho_nonneg (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z : PDSpace n m) (hz : z.1 ∈ lpX)
    (r : ℝ) (hr : 0 < r) : 0 ≤ rho (lpL A b c) lpX Set.univ r z := by
  have hw : z ∈ Wball lpX Set.univ r z := ⟨⟨hz,Set.mem_univ _⟩,by simpa using hr.le⟩
  simpa [gapAt] using le_rho A b c z z r hr hw

end

section
set_option autoImplicit false
open scoped InnerProductSpace Matrix
open RestartPD.LPSharp

lemma ball_diameter {n m : ℕ} (R : ℝ) :
    diamS (Wball (lpX : Set (EuclideanSpace ℝ (Fin n))) (Set.univ : Set (EuclideanSpace ℝ (Fin m))) R 0) ≤
      ((2*R : ℝ) : EReal) := by
  refine iSup_le fun s => iSup_le fun hs => iSup_le fun t => iSup_le fun ht => ?_
  apply EReal.coe_le_coe_iff.2
  have hs' : eucl n m s ≤ R := by simpa only [zero_sub,map_neg_eq_map] using hs.2
  have ht' : eucl n m t ≤ R := by simpa only [zero_sub,map_neg_eq_map] using ht.2
  calc
    eucl n m (s-t) ≤ eucl n m s + eucl n m t := map_sub_le_add _ _ _
    _ ≤ 2*R := by linarith

theorem solution {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (hsol : (Zstar (lpL A b c) lpX Set.univ).Nonempty)
    (H : ℝ) (hHpos : 0 < H)
    (hH : ∀ z : PDSpace n m, distZ (lpL A b c) lpX Set.univ z ≤ H * kktRes A b c z)
    (R : ℝ) (hR : 0 < R) :
    IsSharpOn (lpL A b c) lpX Set.univ (1 / (H * Real.sqrt (1 + 4 * R ^ 2)))
      (Wball lpX Set.univ R 0) := by
  refine ⟨fun z hz => hz.1,?_⟩
  intro r hr hrd z hz
  have hr2 : r ≤ 2*R := EReal.coe_le_coe_iff.1 (hrd.trans (ball_diameter R))
  have hz2 : z ∈ Wball lpX Set.univ (2*R) 0 := ⟨hz.1,hz.2.trans (by linarith)⟩
  have h := RestartPD.LPSharp.lemma_4 A b c hsol (2*R) r (by linarith) hr hr2 z hz2
  have heq : (1+(2*R)^2 : ℝ) = 1+4*R^2 := by ring
  rw [heq] at h
  have h0 := rho_nonneg A b c z hz.1.1 r hr
  have hs : 0 < Real.sqrt (1+4*R^2) := Real.sqrt_pos.2 (by positivity)
  generalize he : rho (lpL A b c) lpX Set.univ r z = e at h h0 ⊢
  cases e using EReal.rec with
  | bot => exact False.elim (by simpa using h0)
  | top => exact le_top
  | coe q =>
    rw [← EReal.coe_mul,EReal.coe_le_coe_iff] at h
    apply EReal.coe_le_coe_iff.2
    have he' : 1/(H*Real.sqrt (1+4*R^2))*distZ (lpL A b c) lpX Set.univ z =
        distZ (lpL A b c) lpX Set.univ z / (H*Real.sqrt (1+4*R^2)) := by ring
    rw [he']
    apply (div_le_iff₀ (mul_pos hHpos hs)).2
    calc
      distZ (lpL A b c) lpX Set.univ z ≤ H*kktRes A b c z := hH z
      _ ≤ H*(q*Real.sqrt (1+4*R^2)) := mul_le_mul_of_nonneg_left h hHpos.le
      _ = q*(H*Real.sqrt (1+4*R^2)) := by ring

end
