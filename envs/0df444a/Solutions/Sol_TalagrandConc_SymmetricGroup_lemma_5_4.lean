-- Prove2me | solution 1 for TalagrandConc.SymmetricGroup.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:09:00.04612+00:00
-- url     : https://prove2.me/submissions/0910f351-7a06-4fb8-a5d9-91292a602c3f

import Mathlib
import Definitions.Def_TalagrandConc_SymmetricGroup_Basic



namespace TalagrandConc.SymmetricGroup

open scoped ENNReal Classical
open Equiv

lemma V_convex' {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) : Convex ℝ (V A σ) :=
  convex_convexHull ℝ _

/-- Extension-by-zero / coordinate-reindexing linear map. -/
def extMap {N M : ℕ} (e : Fin M → Option (Fin N)) : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ) where
  toFun s m := (e m).elim 0 s
  map_add' x y := by funext m; cases h : e m <;> simp [h]
  map_smul' c x := by funext m; cases h : e m <;> simp [h]

@[simp] lemma extMap_apply {N M : ℕ} (e : Fin M → Option (Fin N)) (s : Fin N → ℝ) (m : Fin M) :
    extMap e s m = (e m).elim 0 s := rfl

/-- A linear map sending `U` into a convex set sends `V` into it. -/
lemma V_map {N M : ℕ} (B : Set (Perm (Fin N))) (τ : Perm (Fin N))
    (φ : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ)) (W : Set (Fin M → ℝ)) (hW : Convex ℝ W)
    (hU : ∀ s ∈ U B τ, φ s ∈ W) : ∀ s ∈ V B τ, φ s ∈ W :=
  fun s hs => convexHull_min (fun u hu => hU u hu) (hW.linear_preimage φ) hs

lemma convex_T {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) (m : Fin N) :
    Convex ℝ {s ∈ V A σ | s m = 0} := by
  intro x hx y hy a b ha hb hab
  refine ⟨(convex_convexHull ℝ _) hx.1 hy.1 ha hb hab, ?_⟩
  show (a • x + b • y) m = 0
  simp [hx.2, hy.2]

/-- `e'` : drop the last coordinate. -/
def eLast (N : ℕ) : Fin (N + 1) → Option (Fin N) :=
  fun m => if h : m = Fin.last N then none else some (m.castPred h)

@[simp] lemma eLast_castSucc {N : ℕ} (ℓ : Fin N) : eLast N ℓ.castSucc = some ℓ := by
  simp [eLast, Fin.castSucc_ne_last]

@[simp] lemma eLast_last {N : ℕ} : eLast N (Fin.last N) = none := by simp [eLast]

lemma t_t {N : ℕ} (i m : Fin (N + 1)) : t N i (t N i m) = m := swap_apply_self _ _ _

lemma sum_eLast {N : ℕ} (s : Fin N → ℝ) :
    ∑ m, ((eLast N m).elim 0 s) ^ 2 = ∑ ℓ, s ℓ ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  simp

/-- Transfer for Lemma 5.4: for `σ ∈ G_i`, `fpm A σ (t_i(x)) i ≤ fp (R(A_i)) (Rσ) x`. -/
theorem transfer_54 {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i : Fin (N + 1))
    (σ : Perm (Fin (N + 1))) (hσ : σ ∈ G N i)
    (Rσ : Perm (Fin N)) (hRσ : Restricts (σ * t N i) Rσ) (x : Fin N) :
    fpm A σ (t N i x.castSucc) i ≤ fp (RImage A i) Rσ x := by
  have hσi : σ i = Fin.last N := by simpa [G] using hσ
  set φ := extMap (fun m => eLast N (t N i m)) with hφ
  have hval : ∀ s : Fin N → ℝ,
      (φ s) (t N i x.castSucc) ^ 2 + ∑ m, (φ s m) ^ 2 = s x ^ 2 + ∑ ℓ, s ℓ ^ 2 := by
    intro s
    have h1 : (φ s) (t N i x.castSucc) = s x := by
      simp [hφ, t, swap_apply_self]
    have h2 : ∑ m, (φ s m) ^ 2 = ∑ ℓ, s ℓ ^ 2 := by
      rw [← sum_eLast s]
      simp only [hφ, extMap_apply]
      exact Equiv.sum_comp (t N i) (fun n => ((eLast N n).elim 0 s) ^ 2)
    rw [h1, h2]
  have hmap : ∀ s ∈ V (RImage A i) Rσ, φ s ∈ {s ∈ V A σ | s i = 0} := by
    apply V_map _ _ φ _ (convex_T A σ i)
    intro s hs
    obtain ⟨h01, τ, ⟨ρ, hρA, hρi, hρτ⟩, hτ⟩ := hs
    refine ⟨subset_convexHull ℝ _ ⟨fun m => ?_, ρ, hρA, fun m hm => ?_⟩, ?_⟩
    · simp only [hφ, extMap_apply, eLast]
      split_ifs with h
      · simp
      · simpa using h01 _
    · simp only [hφ, extMap_apply, eLast] at hm
      split_ifs at hm with h
      · have : m = i := by
          simpa [t, swap_apply_eq_iff] using h
        rw [this, hσi, hρi]
      · simp only [Option.elim] at hm
        have hτm := hτ _ hm
        have e1 := hρτ ((t N i m).castPred h)
        have e2 := hRσ ((t N i m).castPred h)
        rw [Fin.castSucc_castPred] at e1 e2
        simp only [Perm.mul_apply, t_t] at e1 e2
        rw [e1, e2, hτm]
    · simp [hφ, extMap_apply, eLast, t]
  unfold fpm fp
  refine le_iInf₂ fun s hs => ?_
  refine (iInf₂_le (φ s) (hmap s hs)).trans ?_
  rw [hval]

/-- Lemma 5.4. -/
theorem lemma_5_4_core {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i j : Fin (N + 1))
    (hij : i ≠ j) (σ : Perm (Fin (N + 1))) (hσ : σ ∈ G N i)
    (Rσ : Perm (Fin N)) (hRσ : Restricts (σ * t N i) Rσ)
    (q : Fin N) (hq : q.castSucc = t N i j) :
    fpm A σ j i ≤ fp (RImage A i) Rσ q := by
  have := transfer_54 A i σ hσ Rσ hRσ q
  rwa [hq, show t N i (t N i j) = j from swap_apply_self _ _ _] at this

/-- Transfer for Lemma 5.8: for `σ ∈ G'_i`, `fpm A σ (castSucc x) last ≤ fp (R'(A'_i)) (R'σ) x`. -/
theorem transfer_58 {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i : Fin (N + 1))
    (σ : Perm (Fin (N + 1))) (hσ : σ ∈ G' N i)
    (R'σ : Perm (Fin N)) (hR'σ : Restricts (t N i * σ) R'σ) (x : Fin N) :
    fpm A σ x.castSucc (Fin.last N) ≤ fp (R'Image A i) R'σ x := by
  have hσi : σ (Fin.last N) = i := by simpa [G'] using hσ
  set φ := extMap (eLast N) with hφ
  have hval : ∀ s : Fin N → ℝ,
      (φ s) x.castSucc ^ 2 + ∑ m, (φ s m) ^ 2 = s x ^ 2 + ∑ ℓ, s ℓ ^ 2 := by
    intro s
    have h1 : (φ s) x.castSucc = s x := by simp [hφ]
    have h2 : ∑ m, (φ s m) ^ 2 = ∑ ℓ, s ℓ ^ 2 := by
      rw [← sum_eLast s]
      simp only [hφ, extMap_apply]
    rw [h1, h2]
  have hmap : ∀ s ∈ V (R'Image A i) R'σ, φ s ∈ {s ∈ V A σ | s (Fin.last N) = 0} := by
    apply V_map _ _ φ _ (convex_T A σ (Fin.last N))
    intro s hs
    obtain ⟨h01, τ, ⟨ρ, hρA, hρi, hρτ⟩, hτ⟩ := hs
    refine ⟨subset_convexHull ℝ _ ⟨fun m => ?_, ρ, hρA, fun m hm => ?_⟩, ?_⟩
    · simp only [hφ, extMap_apply, eLast]
      split_ifs with h
      · simp
      · simpa using h01 _
    · simp only [hφ, extMap_apply, eLast] at hm
      split_ifs at hm with h
      · rw [h, hσi, hρi]
      · simp only [Option.elim] at hm
        have hτm := hτ _ hm
        have e1 := hρτ (m.castPred h)
        have e2 := hR'σ (m.castPred h)
        rw [Fin.castSucc_castPred] at e1 e2
        simp only [Perm.mul_apply] at e1 e2
        rw [hτm, ← e2] at e1
        exact (t N i).injective e1
    · simp [hφ, extMap_apply, eLast]
  unfold fpm fp
  refine le_iInf₂ fun s hs => ?_
  refine (iInf₂_le (φ s) (hmap s hs)).trans ?_
  rw [hval]

/-- Lemma 5.8. -/
theorem lemma_5_8_core {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i j : Fin (N + 1))
    (hij : i ≠ j) (σ : Perm (Fin (N + 1))) (hσ : σ ∈ G' N i)
    (R'σ : Perm (Fin N)) (hR'σ : Restricts (t N i * σ) R'σ)
    (q : Fin N) (hq : q.castSucc = t N i j) :
    fpm A σ (σ⁻¹ j) (Fin.last N) ≤ fp (R'Image A i) R'σ (R'σ⁻¹ q) := by
  have hσi : σ (Fin.last N) = i := by simpa [G'] using hσ
  have hy : σ⁻¹ j ≠ Fin.last N := by
    intro h
    apply hij
    rw [← hσi, ← h]; simp
  have hx : (σ⁻¹ j).castPred hy = R'σ⁻¹ q := by
    rw [Perm.eq_inv_iff_eq]
    apply Fin.castSucc_injective
    rw [← hR'σ, Fin.castSucc_castPred, Perm.mul_apply]
    simp [hq]
  have := transfer_58 A i σ hσ R'σ hR'σ ((σ⁻¹ j).castPred hy)
  rwa [Fin.castSucc_castPred, hx] at this

end TalagrandConc.SymmetricGroup

open TalagrandConc.SymmetricGroup
open Equiv

theorem solution {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i j : Fin (N + 1))
    (hij : i ≠ j) (σ : Perm (Fin (N + 1))) (hσ : σ ∈ G N i)
    (Rσ : Perm (Fin N)) (hRσ : Restricts (σ * t N i) Rσ)
    (q : Fin N) (hq : q.castSucc = t N i j) :
    fpm A σ j i ≤ fp (RImage A i) Rσ q := by
  exact lemma_5_4_core A i j hij σ hσ Rσ hRσ q hq
