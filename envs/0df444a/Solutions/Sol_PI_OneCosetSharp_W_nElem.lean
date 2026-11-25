-- Prove2me | solution 1 for PI.OneCosetSharp.W.nElem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:13:43.922748+00:00
-- url     : https://prove2.me/submissions/cba408ac-e67b-4a15-900a-e499dc3b5197

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_GaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_EmbedMatrixBasisVecApplyOfNotFree
import Theorems.Thm_PI_OneCosetSharp_W_embedMatrix_basisVec_apply_of_not_free
import Theorems.Thm_PI_OneCosetSharp_W_mem_flagUnipotent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W
open Loc LocE
variable {k : Type} [Field k] {n' c n : ℕ}
namespace PI.OneCosetSharp.W
theorem _root_.solution : NElem := by
  intro k _ n' c n xj tt
  classical

  have heN : ∀ (N j : ℕ) (hj : j < N), eN k N j = Pi.single (⟨j, hj⟩ : Fin N) 1 := by
    intro N j hj
    funext s
    unfold eN
    by_cases h : (s : ℕ) = j
    · have : s = ⟨j, hj⟩ := Fin.ext h
      subst this
      simp
    · have : s ≠ ⟨j, hj⟩ := fun e => h (by rw [e])
      simp [h, this]
  have hnf : ∀ (l : Fin (n + c)) (i : ℕ), i < c → (i = 0 ∨ n + i ≤ l.1) →
      ¬ IsFree n' n c l.1 (n' + i) := by
    intro l i hi h
    unfold IsFree
    omega

  let M : Matrix (Fin (n + c)) (Fin (n + c)) k := Matrix.of fun l s =>
    if s.1 < n then (if l = s then 1 else 0)
    else xx1 xj tt (eN k (n' + (c + 1)) (n' + (s.1 - n))) l
  have hM_lt : ∀ l s : Fin (n + c), s.1 < n → M l s = if l = s then 1 else 0 := by
    intro l s hs
    simp [M, hs]
  have hM_ge : ∀ (l : Fin (n + c)) (j : ℕ) (hj : j < n + c), ¬ j < n →
      M l ⟨j, hj⟩ = xx1 xj tt (eN k (n' + (c + 1)) (n' + (j - n))) l := by
    intro l j hj hn
    simp [M, hn]
  have hT : ∀ l s : Fin (n + c), s < l → M l s = 0 := by
    intro l s hsl
    have hsl' : s.1 < l.1 := hsl
    by_cases hs : s.1 < n
    · rw [hM_lt l s hs, if_neg (fun h => by rw [h] at hsl'; exact lt_irrefl _ hsl')]
    · have hsc := s.2
      rw [show s = ⟨s.1, s.2⟩ from rfl, hM_ge l s.1 s.2 hs,
        embedMatrix_basisVec_apply_of_not_free xj tt (s.1 - n) (by omega) l (hnf l (s.1 - n) (by omega) (Or.inr (by omega))),
        if_neg (by omega)]
  have hD : ∀ s : Fin (n + c), M s s = 1 := by
    intro s
    by_cases hs : s.1 < n
    · rw [hM_lt s s hs, if_pos rfl]
    · have hsc := s.2
      rw [show s = ⟨s.1, s.2⟩ from rfl, hM_ge _ s.1 s.2 hs,
        embedMatrix_basisVec_apply_of_not_free xj tt (s.1 - n) (by omega) _ (hnf _ (s.1 - n) (by omega) (Or.inr (by simp; omega))),
        if_pos (by simp; omega)]
  have hUT : M.BlockTriangular id := fun i j hij => hT i j hij
  have hdet : IsUnit M.det := by
    rw [Matrix.det_of_upperTriangular hUT]
    simp [hD]
  let hinv : Invertible M := Matrix.invertibleOfIsUnitDet M hdet
  let ν := M.toLinearEquiv' hinv
  have hν : ∀ x, ν x = M.mulVec x := by
    intro x
    show (↑(M.toLinearEquiv' hinv) : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k)) x = _
    rw [Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
  have hcol : ∀ (j : ℕ) (hj : j < n + c), M.mulVec (eN k (n + c) j) = fun l => M l ⟨j, hj⟩ := by
    intro j hj
    rw [heN _ j hj, Matrix.mulVec_single_one]
    rfl
  have hνcol : ∀ i, i < c → ν (eN k (n + c) (n + i)) = xx1 xj tt (eN k (n' + (c + 1)) (n' + i)) := by
    intro i hi
    rw [hν, hcol (n + i) (by omega)]
    funext l
    rw [hM_ge l (n + i) (by omega) (by omega), Nat.add_sub_cancel_left]
  have hinX : ∀ (v : Fin n → k) (s : Fin (n + c)), ¬ s.1 < n → inX k n c v s = 0 := by
    intro v s hs
    simp [inX, hs]
  have hzero : ∀ i, ¬ i < c → eN k (n + c) (n + i) = 0 := by
    intro i hi
    funext l
    unfold eN
    split_ifs with h
    · have := l.2
      omega
    · rfl
  refine ⟨ν, mem_flagUnipotent ⟨?_, ?_, ?_⟩, ?_, hνcol⟩
  · intro i v hv
    have hv' : ∀ l : Fin (n + c), l.1 ∉ ({x : ℕ | x < n + i} : Set ℕ) → v l = 0 := hv
    show ∀ l : Fin (n + c), l.1 ∉ ({x : ℕ | x < n + i} : Set ℕ) → (ν v) l = 0
    intro l hl
    have hl' : n + i ≤ l.1 := by simpa using hl
    rw [hν]
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : s.1 < n + i
    · rw [hT l s (show s.1 < l.1 by omega), zero_mul]
    · rw [hv' s (by simpa using hs), mul_zero]
  · rcases Nat.eq_zero_or_pos c with hc | hc
    · rw [show eN k (n + c) n = 0 from by simpa using hzero 0 (by omega), map_zero]
    · have h0 := hνcol 0 hc
      have e1 : xx1 xj tt (eN k (n' + (c + 1)) (n' + 0)) = eN k (n + c) (n + 0) := by
        funext l
        rw [embedMatrix_basisVec_apply_of_not_free xj tt 0 hc l (hnf l 0 hc (Or.inl rfl))]
        rfl
      exact h0.trans e1
  · intro i
    show ∀ l : Fin (n + c), l.1 ∉ ({x : ℕ | x < n + i} : Set ℕ) →
      (ν (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) l = 0
    intro l hl
    have hl' : n + i ≤ l.1 := by simpa using hl
    by_cases hi : i < c
    · rw [hνcol i hi, Pi.sub_apply, embedMatrix_basisVec_apply_of_not_free xj tt i hi l (hnf l i hi (Or.inr hl'))]
      show (if l.1 = n + i then (1 : k) else 0) - (if l.1 = n + i then 1 else 0) = 0
      exact sub_self _
    · rw [hzero i hi, map_zero, sub_zero]
      rfl
  · intro v
    rw [hν]
    funext l
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single l]
    · rw [hD l, one_mul]
    · intro s _ hsl
      by_cases hs : s.1 < n
      · rw [hM_lt l s hs, if_neg (fun h => hsl h.symm), zero_mul]
      · rw [hinX v s hs, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ l) h
end PI.OneCosetSharp.W
