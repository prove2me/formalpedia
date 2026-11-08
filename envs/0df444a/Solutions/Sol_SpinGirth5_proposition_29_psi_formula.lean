-- Prove2me | solution 1 for SpinGirth5.proposition_29_psi_formula
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:41:13.902796+00:00
-- url     : https://prove2.me/submissions/dbc90f8a-d037-42e9-9891-6fe21d789a98

import Mathlib
import Definitions.Def_SpinGirth5_starModel

open Matrix

open SpinGirth5 in
theorem solution {q : ℕ} (S : Interaction q) (p : Fin q → ℝ)
    (hp : MarkovMixing.IsDist p) (hAp : ∀ c, 0 < (S.A *ᵥ p) c) :
    Psi S.A p =
      diagonal (fun c => (1 - (S.B *ᵥ p) c)⁻¹) * S.B * (diagonal p - vecMulVec p p) * S.B *
        diagonal (fun c => (1 - (S.B *ᵥ p) c)⁻¹) := by
  have ha : ∀ c, ∑ x, S.A c x * p x = (S.A *ᵥ p) c := fun c => rfl
  have hBp : ∀ c, (S.B *ᵥ p) c = 1 - (S.A *ᵥ p) c := by
    intro c
    rw [← ha c]
    show ∑ x, (1 - S.A c x) * p x = 1 - ∑ x, S.A c x * p x
    have e : ∑ x, (1 - S.A c x) * p x = ∑ x, p x - ∑ x, S.A c x * p x := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [e, hp.2]
  have hX : ∀ x k, (diagonal p - vecMulVec p p) x k = (if x = k then p x else 0) - p x * p k := by
    intro x k
    rw [Matrix.sub_apply, Matrix.diagonal_apply, Matrix.vecMulVec_apply]
  ext c e
  have hrow : ∀ k, (S.B * (diagonal p - vecMulVec p p)) c k
      = S.B c k * p k - (1 - (S.A *ᵥ p) c) * p k := by
    intro k
    rw [Matrix.mul_apply]
    have h1 : ∀ x, S.B c x * (diagonal p - vecMulVec p p) x k
        = (if x = k then S.B c x * p x else 0) - S.B c x * p x * p k := by
      intro x
      rw [hX x k]
      split_ifs <;> ring
    have hBp' : ∑ x, S.B c x * p x = 1 - (S.A *ᵥ p) c := hBp c
    rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_sub_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _), ← Finset.sum_mul, hBp']
  have hfull : (S.B * (diagonal p - vecMulVec p p) * S.B) c e
      = ∑ x, p x * S.A c x * S.A e x - (S.A *ᵥ p) c * (S.A *ᵥ p) e := by
    rw [Matrix.mul_apply, Finset.sum_congr rfl (fun k _ => by rw [hrow k])]
    simp only [Interaction.B]
    have h2 : ∀ k, ((1 - S.A c k) * p k - (1 - (S.A *ᵥ p) c) * p k) * (1 - S.A k e)
        = (S.A *ᵥ p) c * p k - (S.A *ᵥ p) c * (S.A e k * p k) - S.A c k * p k
          + p k * S.A c k * S.A e k := by
      intro k
      rw [S.symm k e]
      ring
    rw [Finset.sum_congr rfl (fun k _ => h2 k), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp.2, ha, ha]
    ring
  have hmat : diagonal (fun c => (1 - (S.B *ᵥ p) c)⁻¹) * S.B * (diagonal p - vecMulVec p p) *
      S.B * diagonal (fun c => (1 - (S.B *ᵥ p) c)⁻¹)
      = diagonal (fun c => (1 - (S.B *ᵥ p) c)⁻¹) * (S.B * (diagonal p - vecMulVec p p) * S.B) *
        diagonal (fun c => (1 - (S.B *ᵥ p) c)⁻¹) := by
    simp only [Matrix.mul_assoc]
  rw [hmat, Matrix.mul_diagonal, Matrix.diagonal_mul, hfull, hBp c, hBp e, sub_sub_cancel,
    sub_sub_cancel]
  have hc := (hAp c).ne'
  have he := (hAp e).ne'
  have h1c : ∑ x, p x * (S.A c x / (S.A *ᵥ p) c) = 1 := by
    rw [Finset.sum_congr rfl (fun x _ => show p x * (S.A c x / (S.A *ᵥ p) c)
      = S.A c x * p x / (S.A *ᵥ p) c by ring), ← Finset.sum_div, ha, div_self hc]
  have h1e : ∑ x, p x * (S.A e x / (S.A *ᵥ p) e) = 1 := by
    rw [Finset.sum_congr rfl (fun x _ => show p x * (S.A e x / (S.A *ᵥ p) e)
      = S.A e x * p x / (S.A *ᵥ p) e by ring), ← Finset.sum_div, ha, div_self he]
  show (∑ x, p x * (S.A c x / (S.A *ᵥ p) c) * (S.A e x / (S.A *ᵥ p) e))
      - (∑ x, p x * (S.A c x / (S.A *ᵥ p) c)) * (∑ x, p x * (S.A e x / (S.A *ᵥ p) e)) = _
  rw [h1c, h1e]
  rw [Finset.sum_congr rfl (fun x _ => show p x * (S.A c x / (S.A *ᵥ p) c) * (S.A e x / (S.A *ᵥ p) e)
      = p x * S.A c x * S.A e x / ((S.A *ᵥ p) c * (S.A *ᵥ p) e) by ring), ← Finset.sum_div]
  field_simp <;> ring
