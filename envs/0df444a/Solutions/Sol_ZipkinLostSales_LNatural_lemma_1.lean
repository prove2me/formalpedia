-- Prove2me | solution 1 for ZipkinLostSales.LNatural.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:07:11.705989+00:00
-- url     : https://prove2.me/submissions/26d1edcb-463e-41a7-9494-bdac2229678f

import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model
open MeasureTheory


namespace ZipkinLostSales.LNatural

theorem lnat_iff {n : ℕ} (D : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    LNatConvexOn D f ↔ ∀ x η x' η', η ≤ 0 → x ∈ D → (fun i => x i - η) ∈ D →
      η' ≤ 0 → x' ∈ D → (fun i => x' i - η') ∈ D →
      f (fun i => max (x i) (x' i) - max η η') + f (fun i => min (x i) (x' i) - min η η') ≤
        f (fun i => x i - η) + f (fun i => x' i - η') := by
  constructor
  · intro h x η x' η' h1 h2 h3 h4 h5 h6
    have := h (Fin.snoc x η) ⟨by simpa using h1, by simpa using h2, by simpa [Fin.init] using h3⟩
      (Fin.snoc x' η') ⟨by simpa using h4, by simpa using h5, by simpa [Fin.init] using h6⟩
    simpa [Fin.init, Fin.snoc_castSucc] using this
  · intro h w hw w' hw'
    exact h (Fin.init w) (w (Fin.last n)) (Fin.init w') (w' (Fin.last n)) hw.1 hw.2.1 hw.2.2
      hw'.1 hw'.2.1 hw'.2.2

theorem V_shift {L : ℕ} {x : Fin L → ℝ} {η s : ℝ} (hx : (fun i => x i - η) ∈ V L)
    (hs : ∀ i, s ≤ x i) : (fun i => x i - s) ∈ V L := by
  refine ⟨fun i j hij => ?_, fun i => by simp only; linarith [hs i]⟩
  have := hx.1 hij
  simp only at this ⊢
  linarith

theorem V_join {L : ℕ} {x x' : Fin L → ℝ} {η η' : ℝ} (hx : (fun i => x i - η) ∈ V L)
    (hx' : (fun i => x' i - η') ∈ V L) :
    (fun i => max (x i) (x' i) - max η η') ∈ V L := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have h1 := hx.1 hij
    have h2 := hx'.1 hij
    simp only at h1 h2 ⊢
    have := max_le_max (show x j ≤ x i by linarith) (show x' j ≤ x' i by linarith)
    linarith
  · have h1 := hx.2 i
    have h2 := hx'.2 i
    simp only at h1 h2 ⊢
    have := max_le_max (show η ≤ x i by linarith) (show η' ≤ x' i by linarith)
    linarith

theorem V_meet {L : ℕ} {x x' : Fin L → ℝ} {η η' : ℝ} (hx : (fun i => x i - η) ∈ V L)
    (hx' : (fun i => x' i - η') ∈ V L) :
    (fun i => min (x i) (x' i) - min η η') ∈ V L := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have h1 := hx.1 hij
    have h2 := hx'.1 hij
    simp only at h1 h2 ⊢
    have := min_le_min (show x j ≤ x i by linarith) (show x' j ≤ x' i by linarith)
    linarith
  · have h1 := hx.2 i
    have h2 := hx'.2 i
    simp only at h1 h2 ⊢
    have := min_le_min (show η ≤ x i by linarith) (show η' ≤ x' i by linarith)
    linarith

theorem ext_step {L : ℕ} {F : (Fin L → ℝ) → ℝ} (hF : LNatConvexOn (V L) F)
    (x x' : Fin L → ℝ) (η η' s : ℝ) (hx : (fun i => x i - η) ∈ V L)
    (hx' : (fun i => x' i - η') ∈ V L)
    (hη : η ≤ s) (hη' : η' ≤ s) (hs : (fun i => x i - s) ∈ V L)
    (hs' : (fun i => x' i - s) ∈ V L) :
    F (fun i => max (x i) (x' i) - max η η') + F (fun i => min (x i) (x' i) - min η η') ≤
        F (fun i => x i - η) + F (fun i => x' i - η') := by
  have e3 : (fun i => (x i - s) - (η - s)) = fun i => x i - η := by funext i; ring
  have e4 : (fun i => (x' i - s) - (η' - s)) = fun i => x' i - η' := by funext i; ring
  have h := (lnat_iff _ _).1 hF (fun i => x i - s) (η - s) (fun i => x' i - s) (η' - s)
    (by linarith) hs (by rw [e3]; exact hx) (by linarith) hs' (by rw [e4]; exact hx')
  have e1 : (fun i => max (x i - s) (x' i - s) - max (η - s) (η' - s)) =
      fun i => max (x i) (x' i) - max η η' := by
    funext i; rw [max_sub_sub_right, max_sub_sub_right]; ring
  have e2 : (fun i => min (x i - s) (x' i - s) - min (η - s) (η' - s)) =
      fun i => min (x i) (x' i) - min η η' := by
    funext i; rw [min_sub_sub_right, min_sub_sub_right]; ring
  rw [e1, e2, e3, e4] at h
  exact h

theorem ext_sub {L : ℕ} (hL : 0 < L) {F : (Fin L → ℝ) → ℝ} (hF : LNatConvexOn (V L) F)
    (x x' : Fin L → ℝ) (η η' : ℝ) (hx : (fun i => x i - η) ∈ V L)
    (hx' : (fun i => x' i - η') ∈ V L) :
    F (fun i => max (x i) (x' i) - max η η') + F (fun i => min (x i) (x' i) - min η η') ≤
        F (fun i => x i - η) + F (fun i => x' i - η') := by
  have core : ∀ (x x' : Fin L → ℝ) (η η' : ℝ), (fun i => x i - η) ∈ V L →
      (fun i => x' i - η') ∈ V L → η ≤ η' →
      F (fun i => max (x i) (x' i) - η') + F (fun i => min (x i) (x' i) - η) ≤
        F (fun i => x i - η) + F (fun i => x' i - η') := by
    intro x x' η η' hx hx' hle
    let ℓ : Fin L := ⟨L - 1, by omega⟩
    have hxa : Antitone x := fun i j hij => by have := hx.1 hij; simp only at this; linarith
    have hx'a : Antitone x' := fun i j hij => by have := hx'.1 hij; simp only at this; linarith
    have hxl : ∀ i, x ℓ ≤ x i := fun i => hxa (Fin.le_def.2 (by simp only [ℓ]; omega))
    have hηx : ∀ i, η ≤ x i := fun i => by have := hx.2 i; simp only at this; linarith
    have hηx' : ∀ i, η' ≤ x' i := fun i => by have := hx'.2 i; simp only at this; linarith
    have ht1 : η ≤ min η' (x ℓ) := le_min hle (hηx ℓ)
    have ht2 : min η' (x ℓ) ≤ η' := min_le_left _ _
    have ht3 : min η' (x ℓ) ≤ x ℓ := min_le_right _ _
    have hxt' : (fun i => x' i - min η' (x ℓ)) ∈ V L := V_shift hx' (fun i => ht2.trans (hηx' i))
    have h2 := ext_step hF x x' η (min η' (x ℓ)) (min η' (x ℓ)) hx hxt' ht1 le_rfl
      (V_shift hx (fun i => ht3.trans (hxl i))) hxt'
    have hJ : (fun i => max (x i) (x' i) - η') ∈ V L := by
      exact V_shift (V_join hx hx') (fun i => (hηx' i).trans (le_max_right _ _))
    have hJt : (fun i => max (x i) (x' i) - min η' (x ℓ)) ∈ V L :=
      V_shift hJ (fun i => ht2.trans ((hηx' i).trans (le_max_right _ _)))
    have h1 := ext_step hF (fun i => max (x i) (x' i)) x' (min η' (x ℓ)) η' η' hJt hx' ht2 le_rfl
      hJ hx'
    rw [max_eq_right ht1, min_eq_left ht1] at h2
    rw [max_eq_right ht2, min_eq_left ht2] at h1
    have e1 : (fun i => max (max (x i) (x' i)) (x' i) - η') = fun i => max (x i) (x' i) - η' := by
      funext i; rw [max_assoc, max_self]
    have e2 : (fun i => min (max (x i) (x' i)) (x' i) - min η' (x ℓ)) =
        fun i => x' i - min η' (x ℓ) := by
      funext i; rw [min_eq_right (le_max_right _ _)]
    rw [e1, e2] at h1
    linarith
  rcases le_total η η' with h | h
  · have := core x x' η η' hx hx' h
    rw [max_eq_right h, min_eq_left h]; exact this
  · have := core x' x η' η hx' hx h
    rw [max_eq_left h, min_eq_right h]
    have e1 : (fun i => max (x' i) (x i) - η) = fun i => max (x i) (x' i) - η := by
      funext i; rw [max_comm]
    have e2 : (fun i => min (x' i) (x i) - η') = fun i => min (x i) (x' i) - η' := by
      funext i; rw [min_comm]
    rw [e1, e2] at this
    linarith

theorem lemma_1_core (L : ℕ) (hL : 0 < L) (f : (Fin L → ℝ) → ℝ) (hf : LNatConvexOn (V L) f) :
    LNatConvexOn (VxNeg L) (liftG (fun v ζ => f (fun i => v i - ζ))) := by
  rw [lnat_iff]
  intro y η y' η' h1 h2 h3 h4 h5 h6
  have hv : (fun i => Fin.init y i - y (Fin.last L)) ∈ V L :=
    V_shift (η := 0) (by simpa using h2.1) (fun i => (h2.2).trans (h2.1.2 i))
  have hv' : (fun i => Fin.init y' i - y' (Fin.last L)) ∈ V L :=
    V_shift (η := 0) (by simpa using h5.1) (fun i => (h5.2).trans (h5.1.2 i))
  have := ext_sub hL hf (Fin.init y) (Fin.init y') (y (Fin.last L)) (y' (Fin.last L)) hv hv'
  simp only [liftG, Fin.init] at this ⊢
  simpa only [sub_sub_sub_cancel_right] using this

end ZipkinLostSales.LNatural

open ZipkinLostSales.LNatural


theorem solution (L : ℕ) (hL : 0 < L) (f : (Fin L → ℝ) → ℝ) (hf : LNatConvexOn (V L) f) :
    LNatConvexOn (VxNeg L) (liftG (fun v ζ => f (fun i => v i - ζ))) := by
  exact lemma_1_core L hL f hf
