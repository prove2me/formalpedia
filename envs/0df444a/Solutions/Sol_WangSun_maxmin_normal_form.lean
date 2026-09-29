-- Prove2me | solution 1 for WangSun.maxmin_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T12:57:07.257262+00:00
-- url     : https://prove2.me/submissions/7f6657fd-6f7a-48ae-a761-f24b971b553e

import Definitions.Def_WangSunCPWL

open Finset

variable {n : ℕ}

namespace WSMM

section Lattice

variable {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]

private theorem sup'_equiv (e : α ≃ β) (g : β → ℝ) :
    (univ : Finset α).sup' univ_nonempty (fun a => g (e a))
      = (univ : Finset β).sup' univ_nonempty g := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun a _ => Finset.le_sup' g (mem_univ (e a))
  · refine Finset.sup'_le _ _ fun b _ => ?_
    have h := Finset.le_sup' (fun a => g (e a)) (mem_univ (e.symm b))
    simpa only [Equiv.apply_symm_apply] using h

private theorem inf'_equiv (e : α ≃ β) (g : β → ℝ) :
    (univ : Finset α).inf' univ_nonempty (fun a => g (e a))
      = (univ : Finset β).inf' univ_nonempty g := by
  apply le_antisymm
  · refine Finset.le_inf' _ _ fun b _ => ?_
    have h := Finset.inf'_le (fun a => g (e a)) (mem_univ (e.symm b))
    simpa only [Equiv.apply_symm_apply] using h
  · exact Finset.le_inf' _ _ fun a _ => Finset.inf'_le g (mem_univ (e a))

private theorem sup'_sum (g : α ⊕ β → ℝ) :
    (univ : Finset (α ⊕ β)).sup' univ_nonempty g
      = max ((univ : Finset α).sup' univ_nonempty fun a => g (Sum.inl a))
          ((univ : Finset β).sup' univ_nonempty fun b => g (Sum.inr b)) := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun s _ => ?_
    rcases s with a | b
    · exact le_max_of_le_left (Finset.le_sup' (fun a => g (Sum.inl a)) (mem_univ a))
    · exact le_max_of_le_right (Finset.le_sup' (fun b => g (Sum.inr b)) (mem_univ b))
  · refine max_le ?_ ?_
    · exact Finset.sup'_le _ _ fun a _ => Finset.le_sup' g (mem_univ (Sum.inl a))
    · exact Finset.sup'_le _ _ fun b _ => Finset.le_sup' g (mem_univ (Sum.inr b))

private theorem inf'_sum (g : α ⊕ β → ℝ) :
    (univ : Finset (α ⊕ β)).inf' univ_nonempty g
      = min ((univ : Finset α).inf' univ_nonempty fun a => g (Sum.inl a))
          ((univ : Finset β).inf' univ_nonempty fun b => g (Sum.inr b)) := by
  apply le_antisymm
  · refine le_min ?_ ?_
    · exact Finset.le_inf' _ _ fun a _ => Finset.inf'_le g (mem_univ (Sum.inl a))
    · exact Finset.le_inf' _ _ fun b _ => Finset.inf'_le g (mem_univ (Sum.inr b))
  · refine Finset.le_inf' _ _ fun s _ => ?_
    rcases s with a | b
    · exact le_trans (min_le_left _ _) (Finset.inf'_le (fun a => g (Sum.inl a)) (mem_univ a))
    · exact le_trans (min_le_right _ _) (Finset.inf'_le (fun b => g (Sum.inr b)) (mem_univ b))

private theorem inf'_prod_fst (g : α → ℝ) :
    (univ : Finset (α × β)).inf' univ_nonempty (fun p => g p.1)
      = (univ : Finset α).inf' univ_nonempty g := by
  apply le_antisymm
  · exact Finset.le_inf' _ _ fun a _ =>
      Finset.inf'_le (fun p : α × β => g p.1) (mem_univ (a, Classical.arbitrary β))
  · exact Finset.le_inf' _ _ fun p _ => Finset.inf'_le g (mem_univ p.1)

private theorem inf'_prod_snd (g : β → ℝ) :
    (univ : Finset (α × β)).inf' univ_nonempty (fun p => g p.2)
      = (univ : Finset β).inf' univ_nonempty g := by
  apply le_antisymm
  · exact Finset.le_inf' _ _ fun b _ =>
      Finset.inf'_le (fun p : α × β => g p.2) (mem_univ (Classical.arbitrary α, b))
  · exact Finset.le_inf' _ _ fun p _ => Finset.inf'_le g (mem_univ p.2)

/-- Distributivity of the linear order: the maximum of pairwise minima over a product
is the minimum of the two maxima. -/
private theorem sup'_prod_min (A : α → ℝ) (B : β → ℝ) :
    (univ : Finset (α × β)).sup' univ_nonempty (fun p => min (A p.1) (B p.2))
      = min ((univ : Finset α).sup' univ_nonempty A) ((univ : Finset β).sup' univ_nonempty B) := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun p _ => ?_
    exact le_min (le_trans (min_le_left _ _) (Finset.le_sup' A (mem_univ p.1)))
      (le_trans (min_le_right _ _) (Finset.le_sup' B (mem_univ p.2)))
  · obtain ⟨a₀, -, ha₀⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := α)) A
    obtain ⟨b₀, -, hb₀⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := β)) B
    rw [ha₀, hb₀]
    exact Finset.le_sup' (fun p : α × β => min (A p.1) (B p.2)) (mem_univ (a₀, b₀))

end Lattice

/-- `f` has a max-min normal form over affine functionals. -/
private def IsMaxMin (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (I J : ℕ) (L : Fin (I + 1) → Fin (J + 1) → ((Fin n → ℝ) →ᵃ[ℝ] ℝ)),
    ∀ x, f x = (univ : Finset (Fin (I + 1))).sup' univ_nonempty
      (fun i => (univ : Finset (Fin (J + 1))).inf' univ_nonempty (fun j => L i j x))

private theorem isMaxMin_affine (T : (Fin n → ℝ) →ᵃ[ℝ] ℝ) : IsMaxMin (fun x => T x) := by
  refine ⟨0, 0, fun _ _ => T, ?_⟩
  intro x
  simp

private theorem isMaxMin_sup {f g : (Fin n → ℝ) → ℝ} (hf : IsMaxMin f) (hg : IsMaxMin g) :
    IsMaxMin (fun x => max (f x) (g x)) := by
  obtain ⟨I, J, L, hL⟩ := hf
  obtain ⟨I', J', M, hM⟩ := hg
  have hI : I + I' + 1 + 1 = (I + 1) + (I' + 1) := by ring
  have hJ : J * J' + J + J' + 1 = (J + 1) * (J' + 1) := by ring
  let eI : Fin (I + I' + 1 + 1) ≃ Fin (I + 1) ⊕ Fin (I' + 1) :=
    (finCongr hI).trans finSumFinEquiv.symm
  let eJ : Fin (J * J' + J + J' + 1) ≃ Fin (J + 1) × Fin (J' + 1) :=
    (finCongr hJ).trans finProdFinEquiv.symm
  refine ⟨I + I' + 1, J * J' + J + J',
    fun i j => Sum.elim (fun a => L a (eJ j).1) (fun b => M b (eJ j).2) (eI i), ?_⟩
  intro x
  set G : Fin (I + 1) ⊕ Fin (I' + 1) → ℝ := fun s =>
    Sum.elim
      (fun a => (univ : Finset (Fin (J + 1))).inf' univ_nonempty fun j => L a j x)
      (fun b => (univ : Finset (Fin (J' + 1))).inf' univ_nonempty fun j => M b j x) s with hG
  have key : ∀ i : Fin (I + I' + 1 + 1),
      (univ : Finset (Fin (J * J' + J + J' + 1))).inf' univ_nonempty
        (fun j => (Sum.elim (fun a => L a (eJ j).1) (fun b => M b (eJ j).2) (eI i)) x)
        = G (eI i) := by
    intro i
    rcases hi : eI i with a | b
    · simp only [hi, Sum.elim_inl, hG]
      rw [inf'_equiv eJ (fun p => L a p.1 x)]
      exact inf'_prod_fst (β := Fin (J' + 1)) (fun c => (L a c) x)
    · simp only [hi, Sum.elim_inr, hG]
      rw [inf'_equiv eJ (fun p => M b p.2 x)]
      exact inf'_prod_snd (α := Fin (J + 1)) (fun c => (M b c) x)
  show max (f x) (g x) = _
  rw [hL x, hM x]
  calc max ((univ : Finset (Fin (I + 1))).sup' univ_nonempty
              (fun i => (univ : Finset (Fin (J + 1))).inf' univ_nonempty fun j => L i j x))
          ((univ : Finset (Fin (I' + 1))).sup' univ_nonempty
              (fun i => (univ : Finset (Fin (J' + 1))).inf' univ_nonempty fun j => M i j x))
      = (univ : Finset (Fin (I + 1) ⊕ Fin (I' + 1))).sup' univ_nonempty G := (sup'_sum G).symm
    _ = (univ : Finset (Fin (I + I' + 1 + 1))).sup' univ_nonempty (fun i => G (eI i)) :=
        (sup'_equiv eI G).symm
    _ = _ := by exact Finset.sup'_congr _ rfl fun i _ => (key i).symm

private theorem isMaxMin_inf {f g : (Fin n → ℝ) → ℝ} (hf : IsMaxMin f) (hg : IsMaxMin g) :
    IsMaxMin (fun x => min (f x) (g x)) := by
  obtain ⟨I, J, L, hL⟩ := hf
  obtain ⟨I', J', M, hM⟩ := hg
  have hI : I * I' + I + I' + 1 = (I + 1) * (I' + 1) := by ring
  have hJ : J + J' + 1 + 1 = (J + 1) + (J' + 1) := by ring
  let eI : Fin (I * I' + I + I' + 1) ≃ Fin (I + 1) × Fin (I' + 1) :=
    (finCongr hI).trans finProdFinEquiv.symm
  let eJ : Fin (J + J' + 1 + 1) ≃ Fin (J + 1) ⊕ Fin (J' + 1) :=
    (finCongr hJ).trans finSumFinEquiv.symm
  refine ⟨I * I' + I + I', J + J' + 1,
    fun i j => Sum.elim (fun c => L (eI i).1 c) (fun d => M (eI i).2 d) (eJ j), ?_⟩
  intro x
  set A : Fin (I + 1) → ℝ := fun a =>
    (univ : Finset (Fin (J + 1))).inf' univ_nonempty fun j => L a j x with hA
  set B : Fin (I' + 1) → ℝ := fun b =>
    (univ : Finset (Fin (J' + 1))).inf' univ_nonempty fun j => M b j x with hB
  have key : ∀ i : Fin (I * I' + I + I' + 1),
      (univ : Finset (Fin (J + J' + 1 + 1))).inf' univ_nonempty
        (fun j => (Sum.elim (fun c => L (eI i).1 c) (fun d => M (eI i).2 d) (eJ j)) x)
        = min (A (eI i).1) (B (eI i).2) := by
    intro i
    rw [inf'_equiv eJ (fun s => (Sum.elim (fun c => L (eI i).1 c) (fun d => M (eI i).2 d) s) x)]
    rw [inf'_sum]
    simp [hA, hB]
  show min (f x) (g x) = _
  rw [hL x, hM x, ← hA, ← hB]
  calc min ((univ : Finset (Fin (I + 1))).sup' univ_nonempty A)
          ((univ : Finset (Fin (I' + 1))).sup' univ_nonempty B)
      = (univ : Finset (Fin (I + 1) × Fin (I' + 1))).sup' univ_nonempty
          (fun p => min (A p.1) (B p.2)) := (sup'_prod_min A B).symm
    _ = (univ : Finset (Fin (I * I' + I + I' + 1))).sup' univ_nonempty
          (fun i => min (A (eI i).1) (B (eI i).2)) :=
        (sup'_equiv eI (fun p => min (A p.1) (B p.2))).symm
    _ = _ := by exact Finset.sup'_congr _ rfl fun i _ => (key i).symm

private theorem cpwl_isMaxMin {f : (Fin n → ℝ) → ℝ} (hf : CPWL f) : IsMaxMin f := by
  induction hf with
  | affine T => exact isMaxMin_affine T
  | sup _ _ ih1 ih2 =>
      obtain ⟨I, J, L, hL⟩ := isMaxMin_sup ih1 ih2
      exact ⟨I, J, L, fun x => by rw [Pi.sup_apply]; exact hL x⟩
  | inf _ _ ih1 ih2 =>
      obtain ⟨I, J, L, hL⟩ := isMaxMin_inf ih1 ih2
      exact ⟨I, J, L, fun x => by rw [Pi.inf_apply]; exact hL x⟩

end WSMM

theorem solution {f : (Fin n → ℝ) → ℝ} (hf : CPWL f) :
    ∃ (I J : ℕ) (L : Fin (I + 1) → Fin (J + 1) → ((Fin n → ℝ) →ᵃ[ℝ] ℝ)),
      f = fun x => (univ : Finset (Fin (I + 1))).sup' univ_nonempty
        (fun i => (univ : Finset (Fin (J + 1))).inf' univ_nonempty (fun j => L i j x)) := by
  obtain ⟨I, J, L, hL⟩ := WSMM.cpwl_isMaxMin hf
  exact ⟨I, J, L, funext hL⟩
