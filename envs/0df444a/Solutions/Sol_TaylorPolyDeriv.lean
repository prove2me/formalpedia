-- Prove2me | solution 1 for TaylorPolyDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:10:27.71965+00:00
-- url     : https://prove2.me/submissions/f8f2fed3-83f0-4e13-b5c3-9495737f13ff

import Definitions.Def_PHigherOrder_TaylorPoly
import Definitions.Def_PHigherOrder_TaylorPolyDeriv

set_option autoImplicit false

theorem _root_.solution (k : ℕ) (u : Plane → ℝ) (x₀ : Plane) :
    ContDiff ℝ (⊤ : ℕ∞) (TaylorPoly k u x₀)
      ∧ (∀ z : Plane, iteratedFDeriv ℝ (k + 1) (TaylorPoly k u x₀) z = 0)
      ∧ (∀ z w : Plane, iteratedFDeriv ℝ k (TaylorPoly k u x₀) z (fun _ => w)
            = iteratedFDeriv ℝ k u x₀ (fun _ => w))
      ∧ (∀ j : ℕ, j ≤ k → ∀ w : Plane,
            iteratedFDeriv ℝ j (TaylorPoly k u x₀) x₀ (fun _ => w)
              = iteratedFDeriv ℝ j u x₀ (fun _ => w))
      ∧ TaylorPoly k u x₀ x₀ = u x₀ := by
  -- Step 0.  Four facts about a single shifted diagonal `z ↦ T (z - y₀, …, z - y₀)`.
  have hSD : ∀ (j : ℕ) (T : Plane [×j]→L[ℝ] ℝ) (y₀ : Plane),
      ContDiff ℝ (⊤ : ℕ∞) (fun z : Plane => T (fun _ => z - y₀)) := fun j T y₀ =>
    (T.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id.sub contDiff_const)).of_le le_top
  -- the `j`-th derivative on the diagonal: the permutation sum collapses to `j!`.
  have hDiag : ∀ (j : ℕ) (T : Plane [×j]→L[ℝ] ℝ) (y₀ x w : Plane),
      iteratedFDeriv ℝ j (fun z : Plane => T (fun _ => z - y₀)) x (fun _ => w)
        = (Nat.factorial j : ℝ) * T (fun _ => w) := by
    intro j T y₀ x w
    rw [iteratedFDeriv_comp_sub (f := fun z : Plane => T (fun _ => z)) j y₀ x,
      T.iteratedFDeriv_comp_diagonal]
    simp [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  -- above the arity the derivative vanishes at every point.
  have hTop : ∀ (j m : ℕ), j < m → ∀ (T : Plane [×j]→L[ℝ] ℝ) (y₀ x : Plane),
      iteratedFDeriv ℝ m (fun z : Plane => T (fun _ => z - y₀)) x = 0 := by
    intro j m hjm T y₀ x
    have hCMM : ∀ y : Fin j → Plane, iteratedFDeriv ℝ m (T : (Fin j → Plane) → ℝ) y = 0 := by
      intro y
      have h := T.norm_iteratedFDeriv_le m y
      rw [Nat.descFactorial_eq_zero_iff_lt.2 (by simpa using hjm)] at h
      simpa using h
    rw [iteratedFDeriv_comp_sub (f := fun z : Plane => T (fun _ => z)) m y₀ x]
    set g : Plane →L[ℝ] (Fin j → Plane) :=
      ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ Plane) with hg
    have hcomp : (fun z : Plane => T (fun _ => z)) = (T : (Fin j → Plane) → ℝ) ∘ g := rfl
    rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ T.contDiff _ le_rfl, hCMM]
    rfl
  -- below the arity the derivative vanishes AT THE CENTRE.
  have hLow : ∀ (i m : ℕ), m < i → ∀ (T : Plane [×i]→L[ℝ] ℝ) (y₀ : Plane),
      iteratedFDeriv ℝ m (fun z : Plane => T (fun _ => z - y₀)) y₀ = 0 := by
    intro i m hmi T y₀
    rw [iteratedFDeriv_comp_sub (f := fun z : Plane => T (fun _ => z)) m y₀ y₀]
    set g : Plane →L[ℝ] (Fin i → Plane) :=
      ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ Plane) with hg
    have hcomp : (fun z : Plane => T (fun _ => z)) = (T : (Fin i → Plane) → ℝ) ∘ g := rfl
    have hz : y₀ - y₀ = (0 : Plane) := sub_self y₀
    rw [hz, hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ T.contDiff _ le_rfl]
    have h0 : g 0 = (0 : Fin i → Plane) := by rw [hg]; rfl
    have h := T.norm_iteratedFDeriv_le m (g 0)
    rw [h0, Fintype.card_fin] at h
    have hzero : iteratedFDeriv ℝ m (T : (Fin i → Plane) → ℝ) (g 0) = 0 := by
      rw [h0]
      have hpow : ‖(0 : Fin i → Plane)‖ ^ (i - m) = 0 := by
        have hij : i - m ≠ 0 := by omega
        simp [hij]
      rw [hpow] at h
      simpa using h
    rw [hzero]
    rfl
  -- Step 1.  The individual summands of the Taylor sum.
  set f : ℕ → Plane → ℝ := fun j z =>
    (1 / (Nat.factorial j : ℝ)) * iteratedFDeriv ℝ j u x₀ (fun _ => z - x₀) with hf
  have hT : TaylorPoly k u x₀ = fun z => ∑ j ∈ Finset.range (k + 1), f j z := rfl
  have hfsmul : ∀ j : ℕ, f j = fun z : Plane =>
      (1 / (Nat.factorial j : ℝ)) • (iteratedFDeriv ℝ j u x₀ (fun _ => z - x₀) : ℝ) :=
    fun _ => rfl
  have hCD : ∀ j : ℕ, ContDiff ℝ (⊤ : ℕ∞) (f j) := fun j =>
    contDiff_const.mul (hSD j (iteratedFDeriv ℝ j u x₀) x₀)
  have hCDAt : ∀ (m : ℕ) (x : Plane), ∀ j ∈ Finset.range (k + 1), ContDiffAt ℝ m (f j) x :=
    fun m x j _ => (hCD j).contDiffAt.of_le (by exact_mod_cast le_top)
  -- Step 2.  Derivatives of the Taylor sum split termwise.
  have hsplit : ∀ (m : ℕ) (x : Plane),
      iteratedFDeriv ℝ m (TaylorPoly k u x₀) x
        = ∑ j ∈ Finset.range (k + 1), iteratedFDeriv ℝ m (f j) x := by
    intro m x
    rw [hT]
    exact iteratedFDeriv_fun_sum_apply (hCDAt m x)
  have hhigh : ∀ (m j : ℕ), j < m → ∀ x w : Plane,
      iteratedFDeriv ℝ m (f j) x (fun _ => w) = 0 := by
    intro m j hjm x w
    rw [hfsmul j, iteratedFDeriv_const_smul_apply'
        ((hSD j (iteratedFDeriv ℝ j u x₀) x₀).contDiffAt.of_le (by exact_mod_cast le_top)),
      hTop j m hjm (iteratedFDeriv ℝ j u x₀) x₀ x]
    simp
  have hlow : ∀ (m j : ℕ), m < j → ∀ w : Plane,
      iteratedFDeriv ℝ m (f j) x₀ (fun _ => w) = 0 := by
    intro m j hmj w
    rw [hfsmul j, iteratedFDeriv_const_smul_apply'
        ((hSD j (iteratedFDeriv ℝ j u x₀) x₀).contDiffAt.of_le (by exact_mod_cast le_top)),
      hLow j m hmj (iteratedFDeriv ℝ j u x₀) x₀]
    simp
  have hexact : ∀ (j : ℕ) (x w : Plane),
      iteratedFDeriv ℝ j (f j) x (fun _ => w) = iteratedFDeriv ℝ j u x₀ (fun _ => w) := by
    intro j x w
    rw [hfsmul j, iteratedFDeriv_const_smul_apply'
        ((hSD j (iteratedFDeriv ℝ j u x₀) x₀).contDiffAt.of_le (by exact_mod_cast le_top)),
      smul_apply, hDiag j (iteratedFDeriv ℝ j u x₀) x₀ x w, smul_eq_mul]
    have hfac : (Nat.factorial j : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j)
    field_simp
  -- Step 3.  Conclusions 3 and 4: only the degree-`j` term survives.
  have h3 : ∀ z w : Plane, iteratedFDeriv ℝ k (TaylorPoly k u x₀) z (fun _ => w)
      = iteratedFDeriv ℝ k u x₀ (fun _ => w) := by
    intro z w
    rw [hsplit k z, sum_apply]
    rw [Finset.sum_eq_single_of_mem k (Finset.self_mem_range_succ k)
      (fun b hb hbk => hhigh k b (by have := Finset.mem_range.1 hb; omega) z w)]
    exact hexact k z w
  have h4 : ∀ j : ℕ, j ≤ k → ∀ w : Plane,
      iteratedFDeriv ℝ j (TaylorPoly k u x₀) x₀ (fun _ => w)
        = iteratedFDeriv ℝ j u x₀ (fun _ => w) := by
    intro m hm w
    rw [hsplit m x₀, sum_apply]
    rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.2 (by omega))
      (fun b _ hbm => by
        rcases lt_or_gt_of_ne hbm with h | h
        · exact hhigh m b h x₀ w
        · exact hlow m b h w)]
    exact hexact m x₀ w
  refine ⟨?_, ?_, h3, h4, ?_⟩
  · rw [hT]; exact ContDiff.sum fun j _ => hCD j
  · intro z
    rw [hsplit (k + 1) z]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [hfsmul j, iteratedFDeriv_const_smul_apply'
        ((hSD j (iteratedFDeriv ℝ j u x₀) x₀).contDiffAt.of_le (by exact_mod_cast le_top)),
      hTop j (k + 1) (by simpa using Finset.mem_range.1 hj) (iteratedFDeriv ℝ j u x₀) x₀ z,
      smul_zero]
  · simpa [iteratedFDeriv_zero_apply] using h4 0 (Nat.zero_le k) 0
