-- Prove2me | solution 1 for WangSun.unbounded_hinge_sum
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T12:52:19.344034+00:00
-- url     : https://prove2.me/submissions/66e25fd8-e5b0-4ed9-b419-020a51d6a4e8

import Definitions.Def_WangSunCPWL

open Finset

variable {n : ℕ}

namespace WSUnb

/-- A finite pointwise maximum of affine functionals on `ℝⁿ`, with the index set
presented as `Fin (m + 1)` so that it is automatically nonempty. -/
private def IsAffMax (P : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (m : ℕ) (L : Fin (m + 1) → ((Fin n → ℝ) →ᵃ[ℝ] ℝ)),
    ∀ x, P x = (univ : Finset (Fin (m + 1))).sup' univ_nonempty fun i => L i x

private theorem isAffMax_affine (T : (Fin n → ℝ) →ᵃ[ℝ] ℝ) : IsAffMax (fun x => T x) := by
  refine ⟨0, fun _ => T, ?_⟩
  intro x
  simp

private theorem isAffMax_zero : IsAffMax (fun _ : Fin n → ℝ => (0 : ℝ)) := by
  simpa using isAffMax_affine (0 : (Fin n → ℝ) →ᵃ[ℝ] ℝ)

/-- Pointwise maxima are closed under addition:
`maxᵢ aᵢ + maxⱼ bⱼ = max_{(i,j)} (aᵢ + bⱼ)`. -/
private theorem isAffMax_add {P Q : (Fin n → ℝ) → ℝ} (hP : IsAffMax P) (hQ : IsAffMax Q) :
    IsAffMax (fun x => P x + Q x) := by
  obtain ⟨m, L, hL⟩ := hP
  obtain ⟨k, M, hM⟩ := hQ
  have hcard : m * k + m + k + 1 = (m + 1) * (k + 1) := by ring
  let e : Fin (m * k + m + k + 1) ≃ Fin (m + 1) × Fin (k + 1) :=
    (finCongr hcard).trans finProdFinEquiv.symm
  refine ⟨m * k + m + k, fun j => L (e j).1 + M (e j).2, ?_⟩
  intro x
  show P x + Q x = _
  rw [hL x, hM x]
  simp only [AffineMap.coe_add, Pi.add_apply]
  apply le_antisymm
  · obtain ⟨i₀, -, hi₀⟩ :=
      Finset.exists_mem_eq_sup' (univ_nonempty (α := Fin (m + 1))) (fun i => L i x)
    obtain ⟨j₀, -, hj₀⟩ :=
      Finset.exists_mem_eq_sup' (univ_nonempty (α := Fin (k + 1))) (fun j => M j x)
    rw [hi₀, hj₀]
    refine le_trans (le_of_eq ?_)
      (Finset.le_sup' (fun i => L (e i).1 x + M (e i).2 x) (mem_univ (e.symm (i₀, j₀))))
    simp
  · refine Finset.sup'_le _ _ fun j _ => ?_
    exact add_le_add (Finset.le_sup' (fun i => L i x) (mem_univ (e j).1))
      (Finset.le_sup' (fun i => M i x) (mem_univ (e j).2))

/-- Pointwise maxima are closed under binary maximum: concatenate the two families. -/
private theorem isAffMax_max {P Q : (Fin n → ℝ) → ℝ} (hP : IsAffMax P) (hQ : IsAffMax Q) :
    IsAffMax (fun x => max (P x) (Q x)) := by
  obtain ⟨m, L, hL⟩ := hP
  obtain ⟨k, M, hM⟩ := hQ
  have hcard : m + k + 1 + 1 = (m + 1) + (k + 1) := by ring
  let e : Fin (m + k + 1 + 1) ≃ Fin (m + 1) ⊕ Fin (k + 1) :=
    (finCongr hcard).trans finSumFinEquiv.symm
  refine ⟨m + k + 1, fun j => Sum.elim L M (e j), ?_⟩
  intro x
  show max (P x) (Q x) = _
  rw [hL x, hM x]
  apply le_antisymm
  · refine max_le ?_ ?_
    · refine Finset.sup'_le _ _ fun i _ => ?_
      have h3 := Finset.le_sup' (fun j => (Sum.elim L M (e j)) x) (mem_univ (e.symm (Sum.inl i)))
      simpa only [Equiv.apply_symm_apply, Sum.elim_inl] using h3
    · refine Finset.sup'_le _ _ fun i _ => ?_
      have h3 := Finset.le_sup' (fun j => (Sum.elim L M (e j)) x) (mem_univ (e.symm (Sum.inr i)))
      simpa only [Equiv.apply_symm_apply, Sum.elim_inr] using h3
  · refine Finset.sup'_le _ _ fun j _ => ?_
    rcases hj : e j with i | i
    · simp only [hj, Sum.elim_inl]
      exact le_max_of_le_left (Finset.le_sup' (fun i => L i x) (mem_univ i))
    · simp only [hj, Sum.elim_inr]
      exact le_max_of_le_right (Finset.le_sup' (fun i => M i x) (mem_univ i))

private theorem max_sub_sub (a b c d : ℝ) :
    max (a - b) (c - d) = max (a + d) (c + b) - (b + d) := by
  rcases le_total (a - b) (c - d) with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]; ring
  · rw [max_eq_left h, max_eq_left (by linarith)]; ring

private theorem min_sub_sub (a b c d : ℝ) :
    min (a - b) (c - d) = (a + c) - max (a + d) (c + b) := by
  rcases le_total (a - b) (c - d) with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith)]; ring

/-- Every lattice expression in affine functionals is a difference of two finite affine
maxima. -/
private theorem cpwl_sub {f : (Fin n → ℝ) → ℝ} (hf : CPWL f) :
    ∃ P Q, IsAffMax P ∧ IsAffMax Q ∧ ∀ x, f x = P x - Q x := by
  induction hf with
  | affine T =>
      exact ⟨fun x => T x, fun _ => 0, isAffMax_affine T, isAffMax_zero, by intro x; simp⟩
  | sup f' g' ih1 ih2 =>
      obtain ⟨P, Q, hP, hQ, hPQ⟩ := ih1
      obtain ⟨R, S, hR, hS, hRS⟩ := ih2
      refine ⟨fun x => max (P x + S x) (R x + Q x), fun x => Q x + S x,
        isAffMax_max (isAffMax_add hP hS) (isAffMax_add hR hQ), isAffMax_add hQ hS, ?_⟩
      intro x
      rw [Pi.sup_apply, hPQ x, hRS x]
      exact max_sub_sub (P x) (Q x) (R x) (S x)
  | inf f' g' ih1 ih2 =>
      obtain ⟨P, Q, hP, hQ, hPQ⟩ := ih1
      obtain ⟨R, S, hR, hS, hRS⟩ := ih2
      refine ⟨fun x => P x + R x, fun x => max (P x + S x) (R x + Q x),
        isAffMax_add hP hR, isAffMax_max (isAffMax_add hP hS) (isAffMax_add hR hQ), ?_⟩
      intro x
      rw [Pi.inf_apply, hPQ x, hRS x]
      exact min_sub_sub (P x) (Q x) (R x) (S x)

end WSUnb

theorem solution {f : (Fin n → ℝ) → ℝ} (hf : CPWL f) :
    ∃ (K : ℕ) (h : Fin K → ((Fin n → ℝ) → ℝ)),
      (∀ k, ∃ (σ : ℝ) (m : ℕ) (L : Fin (m + 1) → ((Fin n → ℝ) →ᵃ[ℝ] ℝ)),
          (σ = 1 ∨ σ = -1) ∧
            h k = fun x => σ * ((univ : Finset (Fin (m + 1))).sup' univ_nonempty fun i => L i x)) ∧
      f = ∑ k, h k := by
  obtain ⟨P, Q, ⟨m, L, hL⟩, ⟨k, M, hM⟩, hPQ⟩ := WSUnb.cpwl_sub hf
  refine ⟨2, ![fun x => (1 : ℝ) * ((univ : Finset (Fin (m + 1))).sup' univ_nonempty fun i => L i x),
    fun x => (-1 : ℝ) * ((univ : Finset (Fin (k + 1))).sup' univ_nonempty fun i => M i x)], ?_, ?_⟩
  · intro j
    fin_cases j
    · exact ⟨1, m, L, Or.inl rfl, rfl⟩
    · exact ⟨-1, k, M, Or.inr rfl, rfl⟩
  · funext x
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply]
    rw [hPQ x, hL x, hM x]
    ring
