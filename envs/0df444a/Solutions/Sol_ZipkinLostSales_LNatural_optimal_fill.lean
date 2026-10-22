-- Prove2me | solution 1 for ZipkinLostSales.LNatural.optimal_fill
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:18:45.914317+00:00
-- url     : https://prove2.me/submissions/c4293039-9e1b-4f9d-bbae-66d5e06181f2

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

theorem init_fun {n : ℕ} (q : Fin (n+1) → ℝ) : Fin.init q = fun i => q (Fin.castSucc i) := rfl

theorem lemma_2_core (L : ℕ) (hL : 0 < L) (g : (Fin L → ℝ) → ℝ → ℝ)
    (hg : LNatConvexOn (VxNeg L) (liftG g))
    (hbdd : ∀ v ∈ V L, BddBelow (g v '' Set.Iic 0)) :
    LNatConvexOn (V L) (fun v => ⨅ ζ : Set.Iic (0 : ℝ), g v ζ) := by
  have hb : ∀ v ∈ V L, BddBelow (Set.range fun ζ : Set.Iic (0:ℝ) => g v ζ) := by
    intro v hv; rw [← Set.image_eq_range]; exact hbdd v hv
  have : Nonempty (Set.Iic (0:ℝ)) := ⟨⟨0, Set.mem_Iic.2 le_rfl⟩⟩
  rw [lnat_iff]
  intro x ξ x' ξ' h1 h2 h3 h4 h5 h6
  have hJ := V_join h3 h6
  have hM := V_meet h3 h6
  have key : ∀ ζ1 ζ2 : Set.Iic (0:ℝ),
      (⨅ ζ : Set.Iic (0 : ℝ), g (fun i => max (x i) (x' i) - max ξ ξ') ζ) +
        (⨅ ζ : Set.Iic (0 : ℝ), g (fun i => min (x i) (x' i) - min ξ ξ') ζ) ≤
        g (fun i => x i - ξ) ζ1 + g (fun i => x' i - ξ') ζ2 := by
    intro ζ1 ζ2
    have z1 := ζ1.2
    have z2 := ζ2.2
    simp only [Set.mem_Iic] at z1 z2
    have hl := (lnat_iff _ _).1 hg (Fin.snoc x (ζ1 + ξ)) ξ (Fin.snoc x' (ζ2 + ξ')) ξ' h1
      ⟨by simpa using h2, by simp; linarith⟩ ⟨by simpa [init_fun] using h3, by simpa using z1⟩ h4
      ⟨by simpa using h5, by simp; linarith⟩ ⟨by simpa [init_fun] using h6, by simpa using z2⟩
    simp only [liftG, init_fun, Fin.snoc_castSucc, Fin.snoc_last, add_sub_cancel_right] at hl
    have a1 : (⨅ ζ : Set.Iic (0 : ℝ), g (fun i => max (x i) (x' i) - max ξ ξ') ζ) ≤
        g (fun i => max (x i) (x' i) - max ξ ξ') (max (ζ1 + ξ) (ζ2 + ξ') - max ξ ξ') := by
      refine ciInf_le (hb _ hJ) ⟨max (ζ1 + ξ) (ζ2 + ξ') - max ξ ξ', ?_⟩
      simp only [Set.mem_Iic, sub_nonpos]
      exact max_le_max (by linarith) (by linarith)
    have a2 : (⨅ ζ : Set.Iic (0 : ℝ), g (fun i => min (x i) (x' i) - min ξ ξ') ζ) ≤
        g (fun i => min (x i) (x' i) - min ξ ξ') (min (ζ1 + ξ) (ζ2 + ξ') - min ξ ξ') := by
      refine ciInf_le (hb _ hM) ⟨min (ζ1 + ξ) (ζ2 + ξ') - min ξ ξ', ?_⟩
      simp only [Set.mem_Iic, sub_nonpos]
      exact min_le_min (by linarith) (by linarith)
    linarith
  show (⨅ ζ : Set.Iic (0 : ℝ), g (fun i => max (x i) (x' i) - max ξ ξ') ζ) +
        (⨅ ζ : Set.Iic (0 : ℝ), g (fun i => min (x i) (x' i) - min ξ ξ') ζ) ≤
      (⨅ ζ : Set.Iic (0 : ℝ), g (fun i => x i - ξ) ζ) + (⨅ ζ : Set.Iic (0 : ℝ), g (fun i => x' i - ξ') ζ)
  have k2 : ∀ ζ2 : Set.Iic (0:ℝ),
      (⨅ ζ : Set.Iic (0 : ℝ), g (fun i => max (x i) (x' i) - max ξ ξ') ζ) +
        (⨅ ζ : Set.Iic (0 : ℝ), g (fun i => min (x i) (x' i) - min ξ ξ') ζ) -
        (⨅ ζ : Set.Iic (0 : ℝ), g (fun i => x i - ξ) ζ) ≤ g (fun i => x' i - ξ') ζ2 := by
    intro ζ2
    have : (⨅ ζ : Set.Iic (0 : ℝ), g (fun i => max (x i) (x' i) - max ξ ξ') ζ) +
        (⨅ ζ : Set.Iic (0 : ℝ), g (fun i => min (x i) (x' i) - min ξ ξ') ζ) -
        g (fun i => x' i - ξ') ζ2 ≤ (⨅ ζ : Set.Iic (0 : ℝ), g (fun i => x i - ξ) ζ) :=
      le_ciInf fun ζ1 => by linarith [key ζ1 ζ2]
    linarith
  have := le_ciInf k2
  linarith

/-- `vext` with value `η` beyond `L`. -/
def ve {L : ℕ} (v : Fin L → ℝ) (η : ℝ) (k : ℕ) : ℝ := if h : k < L then v ⟨k, h⟩ else η

theorem vext_sub_eq {L : ℕ} (v : Fin L → ℝ) (η : ℝ) (k : ℕ) :
    vext (fun i => v i - η) k = ve v η k - η := by
  unfold vext ve; split_ifs <;> simp

theorem ve_max {L : ℕ} (v v' : Fin L → ℝ) (η η' : ℝ) (k : ℕ) :
    ve (fun i => max (v i) (v' i)) (max η η') k = max (ve v η k) (ve v' η' k) := by
  unfold ve; split_ifs <;> rfl

theorem ve_min {L : ℕ} (v v' : Fin L → ℝ) (η η' : ℝ) (k : ℕ) :
    ve (fun i => min (v i) (v' i)) (min η η') k = min (ve v η k) (ve v' η' k) := by
  unfold ve; split_ifs <;> rfl

theorem ve_ge {L : ℕ} {v : Fin L → ℝ} {η : ℝ} (hη : ∀ i, η ≤ v i) (k : ℕ) : η ≤ ve v η k := by
  unfold ve; split_ifs
  · exact hη _
  · exact le_rfl

theorem ve_anti {L : ℕ} {v : Fin L → ℝ} {η : ℝ} (hv : Antitone v) (hη : ∀ i, η ≤ v i)
    {a b : ℕ} (hab : a ≤ b) : ve v η b ≤ ve v η a := by
  unfold ve; split_ifs with h1 h2 h2
  · exact hv (Fin.le_def.2 (by simpa using hab))
  · omega
  · exact hη _
  · exact le_rfl

/-- First-coordinate replacement of `ve`. -/
def Nf {L : ℕ} (u : ℝ) (v : Fin L → ℝ) (η : ℝ) : Fin L → ℝ :=
  fun l => if (l : ℕ) = 0 then u else ve v η ((l : ℕ) + 1)

theorem Nf_max {L : ℕ} (u u' : ℝ) (v v' : Fin L → ℝ) (η η' : ℝ) :
    Nf (max u u') (fun i => max (v i) (v' i)) (max η η') =
      fun l => max (Nf u v η l) (Nf u' v' η' l) := by
  funext l; unfold Nf; split_ifs <;> simp [ve_max]

theorem Nf_min {L : ℕ} (u u' : ℝ) (v v' : Fin L → ℝ) (η η' : ℝ) :
    Nf (min u u') (fun i => min (v i) (v' i)) (min η η') =
      fun l => min (Nf u v η l) (Nf u' v' η' l) := by
  funext l; unfold Nf; split_ifs <;> simp [ve_min]

theorem Nf_mem {L : ℕ} {u : ℝ} {v : Fin L → ℝ} {η ζ : ℝ} (hv : Antitone v)
    (hη : ∀ i, η ≤ v i) (hζ : ζ ≤ η) (hu : ve v η 1 ≤ u) :
    (fun l => Nf u v η l - ζ) ∈ V L := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp only [Nf]
    have hij' : (i : ℕ) ≤ j := hij
    by_cases h1 : (i : ℕ) = 0
    · by_cases h2 : (j : ℕ) = 0
      · simp [h1, h2]
      · rw [if_pos h1, if_neg h2]
        have := ve_anti hv hη (show 1 ≤ (j : ℕ) + 1 by omega); linarith
    · have h2 : ¬ (j : ℕ) = 0 := by omega
      rw [if_neg h1, if_neg h2]
      have := ve_anti hv hη (show (i : ℕ) + 1 ≤ (j : ℕ) + 1 by omega); linarith
  · simp only [Nf]
    split_ifs
    · linarith [ve_ge hη 1]
    · linarith [ve_ge hη ((i : ℕ) + 1)]

/-- The objective `ψ` after the change of variables `u = v₊ + η`. -/
def Psi {L : ℕ} (hh p γ : ℝ) (F : (Fin L → ℝ) → ℝ) (d u : ℝ) (v : Fin L → ℝ) (η ζ : ℝ) : ℝ :=
  hh * (u - ve v η 1) + p * (u - ve v η 0 + d) + γ * F (fun l => Nf u v η l - ζ)

theorem psi_shift {L : ℕ} (hh p γ : ℝ) (F : (Fin L → ℝ) → ℝ) (d u : ℝ) (v : Fin L → ℝ)
    (η ζ : ℝ) :
    psi hh p γ F d (u - η) (fun i => v i - η) (ζ - η) = Psi hh p γ F d u v η ζ := by
  have e : next' (u - η) (fun i => v i - η) (ζ - η) = fun l => Nf u v η l - ζ := by
    funext l; unfold next' Nf; split_ifs
    · ring
    · rw [vext_sub_eq]; ring
  unfold psi Psi; rw [e, vext_sub_eq, vext_sub_eq]; ring

theorem Psi_sub {L : ℕ} (hL : 0 < L) (hh p γ : ℝ) (hγ : 0 ≤ γ) (F : (Fin L → ℝ) → ℝ)
    (hF : LNatConvexOn (V L) F) (d : ℝ)
    (u u' : ℝ) (v v' : Fin L → ℝ) (η η' ζ ζ' : ℝ)
    (hv : Antitone v) (hη : ∀ i, η ≤ v i) (hζ : ζ ≤ η) (hu : ve v η 1 ≤ u)
    (hv' : Antitone v') (hη' : ∀ i, η' ≤ v' i) (hζ' : ζ' ≤ η') (hu' : ve v' η' 1 ≤ u') :
    Psi hh p γ F d (max u u') (fun i => max (v i) (v' i)) (max η η') (max ζ ζ') +
      Psi hh p γ F d (min u u') (fun i => min (v i) (v' i)) (min η η') (min ζ ζ') ≤
    Psi hh p γ F d u v η ζ + Psi hh p γ F d u' v' η' ζ' := by
  unfold Psi
  rw [ve_max, ve_max, ve_min, ve_min, Nf_max, Nf_min]
  have hF' := ext_sub hL hF (Nf u v η) (Nf u' v' η') ζ ζ' (Nf_mem hv hη hζ hu)
    (Nf_mem hv' hη' hζ' hu')
  have hγF := mul_le_mul_of_nonneg_left hF' hγ
  have lin := min_add_max u u'
  have lin1 := min_add_max (ve v η 1) (ve v' η' 1)
  have lin0 := min_add_max (ve v η 0) (ve v' η' 0)
  have : hh * (max u u' - max (ve v η 1) (ve v' η' 1)) +
      p * (max u u' - max (ve v η 0) (ve v' η' 0) + d) +
      (hh * (min u u' - min (ve v η 1) (ve v' η' 1)) +
      p * (min u u' - min (ve v η 0) (ve v' η' 0) + d)) =
      hh * (u - ve v η 1) + p * (u - ve v η 0 + d) +
      (hh * (u' - ve v' η' 1) + p * (u' - ve v' η' 0 + d)) := by
    linear_combination (hh + p) * lin - hh * lin1 - p * lin0
  nlinarith

theorem psi_core (L : ℕ) (hL : 0 < L) (hh p γ : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (F : (Fin L → ℝ) → ℝ) (hF : LNatConvexOn (V L) F)
    (d : ℝ) (hd : 0 ≤ d) :
    LNatConvexOn (Dpsi L d) (liftPsi hh p γ F d) := by
  have key : ∀ (x : Fin (L + 2) → ℝ) (η : ℝ), liftPsi hh p γ F d (fun i => x i - η) =
      Psi hh p γ F d (x 0) (psiV x) η (x (Fin.last (L + 1))) := by
    intro x η
    exact psi_shift hh p γ F d (x 0) (psiV x) η (x (Fin.last (L + 1)))
  rw [lnat_iff]
  intro x η x' η' h1 h2 h3 h4 h5 h6
  rw [key, key, key, key]
  have c1 : ∀ (x : Fin (L + 2) → ℝ) (η : ℝ), x ∈ Dpsi L d → (fun i => x i - η) ∈ Dpsi L d →
      Antitone (psiV x) ∧ (∀ i, η ≤ psiV x i) ∧ x (Fin.last (L + 1)) ≤ η ∧
        ve (psiV x) η 1 ≤ x 0 := by
    intro x η h2 h3
    refine ⟨h2.1.1, fun i => ?_, ?_, ?_⟩
    · have := h3.1.2 i; simp only [psiV] at this ⊢; linarith
    · have := h3.2.1; simp only at this; linarith
    · have := h3.2.2.2.2
      have e : psiV (fun i => x i - η) = fun i => psiV x i - η := rfl
      rw [e, vext_sub_eq] at this
      simp only at this; linarith
  obtain ⟨a1, a2, a3, a4⟩ := c1 x η h2 h3
  obtain ⟨b1, b2, b3, b4⟩ := c1 x' η' h5 h6
  exact Psi_sub hL hh p γ hγ0.le F hF d (x 0) (x' 0) (psiV x) (psiV x') η η'
    (x (Fin.last (L + 1))) (x' (Fin.last (L + 1))) a1 a2 a3 a4 b1 b2 b3 b4

def Cond {L : ℕ} (v : Fin L → ℝ) (η ζ : ℝ) : Prop := Antitone v ∧ (∀ i, η ≤ v i) ∧ ζ ≤ η

theorem Cond_max {L : ℕ} {v v' : Fin L → ℝ} {η η' ζ ζ' : ℝ} (h : Cond v η ζ)
    (h' : Cond v' η' ζ') : Cond (fun i => max (v i) (v' i)) (max η η') (max ζ ζ') :=
  ⟨fun _ _ hij => max_le_max (h.1 hij) (h'.1 hij), fun i => max_le_max (h.2.1 i) (h'.2.1 i),
    max_le_max h.2.2 h'.2.2⟩

theorem Cond_min {L : ℕ} {v v' : Fin L → ℝ} {η η' ζ ζ' : ℝ} (h : Cond v η ζ)
    (h' : Cond v' η' ζ') : Cond (fun i => min (v i) (v' i)) (min η η') (min ζ ζ') :=
  ⟨fun _ _ hij => min_le_min (h.1 hij) (h'.1 hij), fun i => min_le_min (h.2.1 i) (h'.2.1 i),
    min_le_min h.2.2 h'.2.2⟩

theorem Psi_nonneg {L : ℕ} (hh p γ : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ : 0 ≤ γ)
    (F : (Fin L → ℝ) → ℝ) (hF0 : ∀ v ∈ V L, 0 ≤ F v) (d u : ℝ) (v : Fin L → ℝ) (η ζ : ℝ)
    (hc : Cond v η ζ) (hu : u ∈ Set.Icc (max (ve v η 0 - d) (ve v η 1)) (ve v η 0)) :
    0 ≤ Psi hh p γ F d u v η ζ := by
  have h1 : ve v η 1 ≤ u := (le_max_right _ _).trans hu.1
  have h0 : ve v η 0 - d ≤ u := (le_max_left _ _).trans hu.1
  have := hF0 _ (Nf_mem hc.1 hc.2.1 hc.2.2 h1)
  unfold Psi
  have a := mul_nonneg hhh (show 0 ≤ u - ve v η 1 by linarith)
  have b := mul_nonneg hp (show 0 ≤ u - ve v η 0 + d by linarith)
  have c := mul_nonneg hγ this
  linarith

theorem psi_eq_Psi {L : ℕ} (hh p γ : ℝ) (F : (Fin L → ℝ) → ℝ) (d vp : ℝ) (v : Fin L → ℝ)
    (η ζ : ℝ) : psi hh p γ F d vp (fun i => v i - η) (ζ - η) = Psi hh p γ F d (vp + η) v η ζ := by
  rw [← psi_shift, add_sub_cancel_right]

theorem mem_shift {L : ℕ} {v : Fin L → ℝ} {η d vp : ℝ}
    (h : vp ∈ Set.Icc (max (vext (fun i => v i - η) 0 - d) (vext (fun i => v i - η) 1))
      (vext (fun i => v i - η) 0)) :
    vp + η ∈ Set.Icc (max (ve v η 0 - d) (ve v η 1)) (ve v η 0) := by
  rw [vext_sub_eq, vext_sub_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨max_le ?_ ?_, by linarith⟩
  · linarith [(le_max_left (ve v η 0 - η - d) (ve v η 1 - η)).trans h1]
  · linarith [(le_max_right (ve v η 0 - η - d) (ve v η 1 - η)).trans h1]

theorem kappa_le_Psi {L : ℕ} (hh p γ : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ : 0 ≤ γ)
    (F : (Fin L → ℝ) → ℝ) (hF0 : ∀ v ∈ V L, 0 ≤ F v) (d u : ℝ) (v : Fin L → ℝ) (η ζ : ℝ)
    (hc : Cond v η ζ) (hu : u ∈ Set.Icc (max (ve v η 0 - d) (ve v η 1)) (ve v η 0)) :
    kappa hh p γ F d (fun i => v i - η) (ζ - η) ≤ Psi hh p γ F d u v η ζ := by
  unfold kappa
  have hm : u - η ∈ Set.Icc (max (vext (fun i => v i - η) 0 - d) (vext (fun i => v i - η) 1))
      (vext (fun i => v i - η) 0) := by
    rw [vext_sub_eq, vext_sub_eq]
    obtain ⟨h1, h2⟩ := hu
    refine ⟨max_le ?_ ?_, by linarith⟩
    · linarith [(le_max_left (ve v η 0 - d) (ve v η 1)).trans h1]
    · linarith [(le_max_right (ve v η 0 - d) (ve v η 1)).trans h1]
  have hb : BddBelow (Set.range fun vp : Set.Icc (max (vext (fun i => v i - η) 0 - d)
      (vext (fun i => v i - η) 1)) (vext (fun i => v i - η) 0) =>
        psi hh p γ F d vp (fun i => v i - η) (ζ - η)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨vp, rfl⟩
    simp only
    rw [psi_eq_Psi]
    exact Psi_nonneg hh p γ hhh hp hγ F hF0 d _ v η ζ hc (mem_shift vp.2)
  have := ciInf_le hb ⟨u - η, hm⟩
  simp only at this
  rw [psi_eq_Psi, sub_add_cancel] at this
  exact this

theorem le_kappa {L : ℕ} (hh p γ : ℝ) (F : (Fin L → ℝ) → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (v : Fin L → ℝ) (η ζ : ℝ) (hc : Cond v η ζ) (c : ℝ)
    (h : ∀ u ∈ Set.Icc (max (ve v η 0 - d) (ve v η 1)) (ve v η 0), c ≤ Psi hh p γ F d u v η ζ) :
    c ≤ kappa hh p γ F d (fun i => v i - η) (ζ - η) := by
  unfold kappa
  have hne : Nonempty (Set.Icc (max (vext (fun i => v i - η) 0 - d) (vext (fun i => v i - η) 1))
      (vext (fun i => v i - η) 0)) := by
    refine ⟨⟨vext (fun i => v i - η) 0, max_le (by linarith) ?_, le_rfl⟩⟩
    rw [vext_sub_eq, vext_sub_eq]
    linarith [ve_anti hc.1 hc.2.1 (show 0 ≤ 1 by omega)]
  refine le_ciInf fun vp => ?_
  rw [psi_eq_Psi]
  exact h _ (mem_shift vp.2)

theorem kappa_sub {L : ℕ} (hL : 0 < L) (hh p γ : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ : 0 ≤ γ)
    (F : (Fin L → ℝ) → ℝ) (hF : LNatConvexOn (V L) F) (hF0 : ∀ v ∈ V L, 0 ≤ F v)
    (d : ℝ) (hd : 0 ≤ d) (v v' : Fin L → ℝ) (η η' ζ ζ' : ℝ)
    (hc : Cond v η ζ) (hc' : Cond v' η' ζ') :
    kappa hh p γ F d (fun i => max (v i) (v' i) - max η η') (max ζ ζ' - max η η') +
      kappa hh p γ F d (fun i => min (v i) (v' i) - min η η') (min ζ ζ' - min η η') ≤
    kappa hh p γ F d (fun i => v i - η) (ζ - η) + kappa hh p γ F d (fun i => v' i - η') (ζ' - η') := by
  have key : ∀ u ∈ Set.Icc (max (ve v η 0 - d) (ve v η 1)) (ve v η 0),
      ∀ u' ∈ Set.Icc (max (ve v' η' 0 - d) (ve v' η' 1)) (ve v' η' 0),
      kappa hh p γ F d (fun i => max (v i) (v' i) - max η η') (max ζ ζ' - max η η') +
        kappa hh p γ F d (fun i => min (v i) (v' i) - min η η') (min ζ ζ' - min η η') ≤
      Psi hh p γ F d u v η ζ + Psi hh p γ F d u' v' η' ζ' := by
    intro u hu u' hu'
    have mJ : max u u' ∈ Set.Icc (max (ve (fun i => max (v i) (v' i)) (max η η') 0 - d)
        (ve (fun i => max (v i) (v' i)) (max η η') 1)) (ve (fun i => max (v i) (v' i)) (max η η') 0) := by
      rw [ve_max, ve_max]
      refine ⟨max_le ?_ (max_le_max ((le_max_right _ _).trans hu.1) ((le_max_right _ _).trans hu'.1)),
        max_le_max hu.2 hu'.2⟩
      rw [← max_sub_sub_right]
      exact max_le_max ((le_max_left _ _).trans hu.1) ((le_max_left _ _).trans hu'.1)
    have mM : min u u' ∈ Set.Icc (max (ve (fun i => min (v i) (v' i)) (min η η') 0 - d)
        (ve (fun i => min (v i) (v' i)) (min η η') 1)) (ve (fun i => min (v i) (v' i)) (min η η') 0) := by
      rw [ve_min, ve_min]
      refine ⟨max_le ?_ (min_le_min ((le_max_right _ _).trans hu.1) ((le_max_right _ _).trans hu'.1)),
        min_le_min hu.2 hu'.2⟩
      rw [← min_sub_sub_right]
      exact min_le_min ((le_max_left _ _).trans hu.1) ((le_max_left _ _).trans hu'.1)
    have k1 := kappa_le_Psi hh p γ hhh hp hγ F hF0 d _ _ _ _ (Cond_max hc hc') mJ
    have k2 := kappa_le_Psi hh p γ hhh hp hγ F hF0 d _ _ _ _ (Cond_min hc hc') mM
    have k3 := Psi_sub hL hh p γ hγ F hF d u u' v v' η η' ζ ζ' hc.1 hc.2.1 hc.2.2
      ((le_max_right _ _).trans hu.1) hc'.1 hc'.2.1 hc'.2.2 ((le_max_right _ _).trans hu'.1)
    linarith
  have k2 : ∀ u' ∈ Set.Icc (max (ve v' η' 0 - d) (ve v' η' 1)) (ve v' η' 0),
      kappa hh p γ F d (fun i => max (v i) (v' i) - max η η') (max ζ ζ' - max η η') +
        kappa hh p γ F d (fun i => min (v i) (v' i) - min η η') (min ζ ζ' - min η η') -
        kappa hh p γ F d (fun i => v i - η) (ζ - η) ≤ Psi hh p γ F d u' v' η' ζ' := by
    intro u' hu'
    have := le_kappa hh p γ F d hd v η ζ hc
      (kappa hh p γ F d (fun i => max (v i) (v' i) - max η η') (max ζ ζ' - max η η') +
        kappa hh p γ F d (fun i => min (v i) (v' i) - min η η') (min ζ ζ' - min η η') -
        Psi hh p γ F d u' v' η' ζ') (fun u hu => by linarith [key u hu u' hu'])
    linarith
  have := le_kappa hh p γ F d hd v' η' ζ' hc' _ k2
  linarith

theorem kappa_core (L : ℕ) (hL : 0 < L) (hh p γ : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (F : (Fin L → ℝ) → ℝ) (hF : LNatConvexOn (V L) F)
    (hF0 : ∀ v ∈ V L, 0 ≤ F v) (d : ℝ) (hd : 0 ≤ d) :
    LNatConvexOn (VxNeg L) (liftG (kappa hh p γ F d)) := by
  rw [lnat_iff]
  intro y η y' η' h1 h2 h3 h4 h5 h6
  have cnd : ∀ (y : Fin (L + 1) → ℝ) (η : ℝ), η ≤ 0 → y ∈ VxNeg L → (fun i => y i - η) ∈ VxNeg L →
      Cond (Fin.init y) η (y (Fin.last L)) := by
    intro y η h1 h2 h3
    refine ⟨h2.1.1, fun i => h1.trans (h2.1.2 i), ?_⟩
    have := h3.2; simp only at this; linarith
  have := kappa_sub hL hh p γ hhh hp hγ0.le F hF hF0 d hd (Fin.init y) (Fin.init y') η η'
    (y (Fin.last L)) (y' (Fin.last L)) (cnd y η h1 h2 h3) (cnd y' η' h4 h5 h6)
  simpa only [liftG, init_fun] using this

/-! ## Analytic infrastructure -/

theorem qhat_nonneg (hh p u : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p) : 0 ≤ qhat hh p u := by
  unfold qhat
  exact add_nonneg (mul_nonneg hhh (le_max_right _ _)) (mul_nonneg hp (le_max_right _ _))

theorem qhat_eq (hh p u : ℝ) : qhat hh p u = (hh + p) * max u 0 - p * u := by
  unfold qhat
  rcases le_total u 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

theorem qhat_cont (hh p : ℝ) : Continuous (qhat hh p) := by
  unfold qhat
  exact (continuous_const.mul (continuous_id.max continuous_const)).add
    (continuous_const.mul (continuous_neg.max continuous_const))

theorem qhat_abs (hh p u : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p) : |qhat hh p u| ≤ (hh + p) * |u| := by
  rw [abs_of_nonneg (qhat_nonneg hh p u hhh hp)]
  unfold qhat
  have h1 : max u 0 ≤ |u| := max_le (le_abs_self u) (abs_nonneg u)
  have h2 : max (-u) 0 ≤ |u| := max_le (neg_le_abs u) (abs_nonneg u)
  nlinarith [mul_le_mul_of_nonneg_left h1 hhh, mul_le_mul_of_nonneg_left h2 hp]

theorem qhat_int (hh p : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμint : Integrable id μ) (Y : ℝ) : Integrable (fun d => qhat hh p (Y - d)) μ := by
  refine Integrable.mono' (g := fun d => (hh + p) * (|Y| + |d|)) ?_ ?_ ?_
  · exact ((integrable_const |Y|).add hμint.abs).const_mul _
  · exact ((qhat_cont hh p).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun d => ?_
    rw [Real.norm_eq_abs]
    calc |qhat hh p (Y - d)| ≤ (hh + p) * |Y - d| := qhat_abs hh p _ hhh hp
      _ ≤ (hh + p) * (|Y| + |d|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (by linarith)

def bump {L : ℕ} (y : Fin L → ℝ) (δ : ℝ) : Fin L → ℝ := fun l => y l + (if (l : ℕ) = 0 then δ else 0)

theorem bump_mem {L : ℕ} {y : Fin L → ℝ} (hy : y ∈ V L) {δ : ℝ} (hδ : 0 ≤ δ) : bump y δ ∈ V L := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : (i : ℕ) ≤ j := hij
    have := hy.1 hij
    simp only [bump]
    split_ifs with h1 h2 <;> first | linarith | omega
  · have := hy.2 i
    simp only [bump]
    split_ifs <;> linarith

theorem vext_bump {L : ℕ} (hL : 0 < L) (y : Fin L → ℝ) (δ : ℝ) (k : ℕ) :
    vext (bump y δ) k = vext y k + (if k = 0 then δ else 0) := by
  unfold vext bump
  by_cases h1 : k < L
  · simp [h1]
  · have : k ≠ 0 := by omega
    simp [h1, this]

theorem vext_anti {L : ℕ} {v : Fin L → ℝ} (hv : v ∈ V L) {a b : ℕ} (hab : a ≤ b) :
    vext v b ≤ vext v a := ve_anti (η := 0) hv.1 hv.2 hab

theorem vext_nonneg {L : ℕ} {v : Fin L → ℝ} (hv : v ∈ V L) (k : ℕ) : 0 ≤ vext v k :=
  ve_ge (η := 0) hv.2 k

def Eat {L : ℕ} (v : Fin L → ℝ) (ζ t : ℝ) : Fin L → ℝ :=
  fun l => (if (l : ℕ) = 0 then t else 0) + vext v ((l : ℕ) + 1) - ζ

theorem Eat_bump {L : ℕ} (v : Fin L → ℝ) (ζ t δ : ℝ) : Eat v ζ (t + δ) = bump (Eat v ζ t) δ := by
  funext l; by_cases h : (l : ℕ) = 0 <;> simp [Eat, bump, h] <;> ring

theorem Eat_mem {L : ℕ} {v : Fin L → ℝ} (hv : v ∈ V L) {ζ t : ℝ} (hζ : ζ ≤ 0) (ht : 0 ≤ t) :
    Eat v ζ t ∈ V L := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : (i : ℕ) ≤ j := hij
    have := vext_anti hv (show (i : ℕ) + 1 ≤ (j : ℕ) + 1 by omega)
    simp only [Eat]
    split_ifs with h1 h2 <;> first | linarith | omega
  · have := vext_nonneg hv ((i : ℕ) + 1)
    simp only [Eat]
    split_ifs <;> linarith

theorem next_eq_Eat {L : ℕ} (v : Fin L → ℝ) (d ζ : ℝ) :
    next v d ζ = Eat v ζ (max (vext v 0 - vext v 1 - d) 0) := rfl

theorem next_mem {L : ℕ} {v : Fin L → ℝ} (hv : v ∈ V L) {ζ : ℝ} (hζ : ζ ≤ 0) (d : ℝ) :
    next v d ζ ∈ V L := Eat_mem hv hζ (le_max_right _ _)

theorem next_bump {L : ℕ} (hL : 0 < L) (y : Fin L → ℝ) (δ d ζ : ℝ) :
    next (bump y δ) d ζ = bump (next y d ζ)
      (max (vext y 0 - vext y 1 - d + δ) 0 - max (vext y 0 - vext y 1 - d) 0) := by
  rw [next_eq_Eat, next_eq_Eat, ← Eat_bump]
  have e : ∀ k, vext (bump y δ) (k + 1) = vext y (k + 1) := by
    intro k; rw [vext_bump hL]; simp
  have e0 : vext (bump y δ) 0 - vext (bump y δ) 1 - d = vext y 0 - vext y 1 - d + δ := by
    rw [vext_bump hL, vext_bump hL]; simp; ring
  rw [e0, add_sub_cancel]
  funext l; unfold Eat; rw [e]

def LipB {L : ℕ} (F : (Fin L → ℝ) → ℝ) (a C : ℝ) : Prop :=
  ∀ y ∈ V L, ∀ δ : ℝ, 0 ≤ δ → F y - a * δ ≤ F (bump y δ) ∧ F (bump y δ) ≤ F y + C * δ

theorem int_next {L : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμint : Integrable id μ)
    (F : (Fin L → ℝ) → ℝ) (a C : ℝ) (ha : 0 ≤ a) (hC : 0 ≤ C) (hLip : LipB F a C)
    {v : Fin L → ℝ} (hv : v ∈ V L) {ζ : ℝ} (hζ : ζ ≤ 0) :
    Integrable (fun d => F (next v d ζ)) μ := by
  set h : ℝ → ℝ := fun t => F (Eat v ζ (max t 0)) with hh_def
  have hl : ∀ t t', t ≤ t' → |h t' - h t| ≤ (a + C) * (t' - t) := by
    intro t t' htt
    have hδ0 : 0 ≤ max t' 0 - max t 0 := sub_nonneg.2 (max_le_max htt le_rfl)
    have hδ1 : max t' 0 - max t 0 ≤ t' - t := by
      rcases le_total t 0 with h1 | h1 <;> rcases le_total t' 0 with h2 | h2 <;>
        simp [max_eq_left, max_eq_right, *] <;> linarith
    have e : max t' 0 = max t 0 + (max t' 0 - max t 0) := by ring
    have := hLip _ (Eat_mem hv hζ (le_max_right t 0)) _ hδ0
    simp only [hh_def]
    rw [e, Eat_bump]
    rw [abs_le]
    constructor <;> nlinarith
  have hlip : ∀ t t', |h t - h t'| ≤ (a + C) * |t - t'| := by
    intro t t'
    rcases le_total t t' with h1 | h1
    · rw [abs_sub_comm (h t), abs_sub_comm t, abs_of_nonneg (by linarith : 0 ≤ t' - t)]
      exact hl t t' h1
    · rw [abs_of_nonneg (by linarith : 0 ≤ t - t')]
      exact hl t' t h1
  have hcont : Continuous h := by
    have : LipschitzWith (Real.toNNReal (a + C)) h := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by linarith)]
      exact hlip x y
    exact this.continuous
  have hfun : (fun d => F (next v d ζ)) = fun d => h (vext v 0 - vext v 1 - d) := rfl
  rw [hfun]
  refine Integrable.mono' (g := fun d => |h 0| + (a + C) * (|vext v 0 - vext v 1| + |d|)) ?_ ?_ ?_
  · exact (integrable_const _).add (((integrable_const _).add hμint.abs).const_mul _)
  · exact (hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun d => ?_
    rw [Real.norm_eq_abs]
    have h1 := hlip (vext v 0 - vext v 1 - d) 0
    have h2 : |vext v 0 - vext v 1 - d - 0| ≤ |vext v 0 - vext v 1| + |d| := by
      rw [sub_zero]; exact abs_sub _ _
    have h3 := abs_sub_abs_le_abs_sub (h (vext v 0 - vext v 1 - d)) (h 0)
    nlinarith [mul_le_mul_of_nonneg_left h2 (show 0 ≤ a + C by linarith)]

theorem gstep_nonneg {L : ℕ} (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ : 0 ≤ γ)
    (μ : Measure ℝ) (F : (Fin L → ℝ) → ℝ) (hF : ∀ v, 0 ≤ F v) (v : Fin L → ℝ) {ζ : ℝ}
    (hζ : ζ ≤ 0) : 0 ≤ gstep c hh p γ μ F v ζ := by
  unfold gstep qhat0
  have h1 : γ ^ L * c * ζ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hζ
  have h2 : 0 ≤ ∫ d, qhat hh p (vext v 0 - vext v 1 - d) ∂μ :=
    integral_nonneg fun d => qhat_nonneg hh p _ hhh hp
  have h3 : 0 ≤ ∫ d, F (next v d ζ) ∂μ := integral_nonneg fun d => hF _
  have := mul_nonneg hγ h3
  linarith

theorem nonempty_Iic0 : Nonempty (Set.Iic (0:ℝ)) := ⟨⟨0, Set.mem_Iic.2 le_rfl⟩⟩

theorem fbar_nonneg {L : ℕ} (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ : 0 ≤ γ)
    (μ : Measure ℝ) : ∀ k (v : Fin L → ℝ), 0 ≤ fbar c hh p γ μ k v := by
  intro k
  induction k with
  | zero => intro v; simp [fbar_zero]
  | succ k ih =>
    intro v
    rw [fbar_succ]
    have := nonempty_Iic0
    exact le_ciInf fun ζ => gstep_nonneg c hh p γ hc hhh hp hγ μ _ ih v ζ.2

theorem gstep_eq {L : ℕ} (c hh p γ : ℝ) (μ : Measure ℝ) (F : (Fin L → ℝ) → ℝ) (v : Fin L → ℝ)
    (ζ : ℝ) (h1 : Integrable (fun d => qhat hh p (vext v 0 - vext v 1 - d)) μ)
    (h2 : Integrable (fun d => F (next v d ζ)) μ) :
    gstep c hh p γ μ F v ζ = -(γ ^ L * c * ζ) +
      ∫ d, (qhat hh p (vext v 0 - vext v 1 - d) + γ * F (next v d ζ)) ∂μ := by
  unfold gstep qhat0
  rw [integral_add h1 (h2.const_mul γ), integral_const_mul]
  ring

theorem bdd_gstep {L : ℕ} (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ : 0 ≤ γ)
    (μ : Measure ℝ) (F : (Fin L → ℝ) → ℝ) (hF : ∀ v, 0 ≤ F v) (v : Fin L → ℝ) :
    BddBelow (Set.range fun ζ : Set.Iic (0:ℝ) => gstep c hh p γ μ F v ζ) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨ζ, rfl⟩
  exact gstep_nonneg c hh p γ hc hhh hp hγ μ F hF v ζ.2

theorem fbar_lip {L : ℕ} (hL : 0 < L) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμint : Integrable id μ) (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    ∀ k : ℕ, LipB (fbar (L := L) c hh p γ μ k) p (k * hh) := by
  intro k
  induction k with
  | zero =>
    intro y hy δ hδ
    simp only [fbar_zero, Nat.cast_zero, zero_mul, add_zero]
    constructor <;> nlinarith [mul_nonneg hp hδ]
  | succ k ih =>
    intro y hy δ hδ
    have hF0 := fbar_nonneg (L := L) c hh p γ hc hhh hp hγ0.le μ k
    have hbm := bump_mem hy hδ
    -- pointwise comparison of gstep
    have cmp : ∀ ζ : ℝ, ζ ≤ 0 →
        gstep c hh p γ μ (fbar c hh p γ μ k) y ζ - p * δ ≤
          gstep c hh p γ μ (fbar c hh p γ μ k) (bump y δ) ζ ∧
        gstep c hh p γ μ (fbar c hh p γ μ k) (bump y δ) ζ ≤
          gstep c hh p γ μ (fbar c hh p γ μ k) y ζ + ((k + 1 : ℕ) * hh) * δ := by
      intro ζ hζ
      have I1 := int_next μ hμint _ p (k * hh) hp (by positivity) ih hy hζ
      have I2 := int_next μ hμint _ p (k * hh) hp (by positivity) ih hbm hζ
      have Q1 := qhat_int hh p hhh hp μ hμint (vext y 0 - vext y 1)
      have Q2 := qhat_int hh p hhh hp μ hμint (vext (bump y δ) 0 - vext (bump y δ) 1)
      rw [gstep_eq c hh p γ μ _ y ζ Q1 I1, gstep_eq c hh p γ μ _ (bump y δ) ζ Q2 I2]
      have G1 : Integrable (fun d => qhat hh p (vext y 0 - vext y 1 - d) +
          γ * fbar c hh p γ μ k (next y d ζ)) μ := Q1.add (I1.const_mul γ)
      have G2 : Integrable (fun d => qhat hh p (vext (bump y δ) 0 - vext (bump y δ) 1 - d) +
          γ * fbar c hh p γ μ k (next (bump y δ) d ζ)) μ := Q2.add (I2.const_mul γ)
      have e0 : vext (bump y δ) 0 - vext (bump y δ) 1 = vext y 0 - vext y 1 + δ := by
        rw [vext_bump hL, vext_bump hL]; simp; ring
      have pw : ∀ d,
          qhat hh p (vext y 0 - vext y 1 - d) + γ * fbar c hh p γ μ k (next y d ζ) - p * δ ≤
            qhat hh p (vext (bump y δ) 0 - vext (bump y δ) 1 - d) +
              γ * fbar c hh p γ μ k (next (bump y δ) d ζ) ∧
          qhat hh p (vext (bump y δ) 0 - vext (bump y δ) 1 - d) +
              γ * fbar c hh p γ μ k (next (bump y δ) d ζ) ≤
            qhat hh p (vext y 0 - vext y 1 - d) + γ * fbar c hh p γ μ k (next y d ζ) +
              ((k + 1 : ℕ) * hh) * δ := by
        intro d
        rw [next_bump hL, e0]
        set u := vext y 0 - vext y 1 - d with hu
        have eu : vext y 0 - vext y 1 + δ - d = u + δ := by rw [hu]; ring
        rw [eu]
        set δ' := max (u + δ) 0 - max u 0 with hδ'
        have hδ'0 : 0 ≤ δ' := sub_nonneg.2 (max_le_max (by linarith) le_rfl)
        have hδ'1 : δ' ≤ δ := by
          have : max (u + δ) 0 ≤ max u 0 + δ :=
            max_le (by linarith [le_max_left u 0]) (by linarith [le_max_right u 0])
          linarith
        have q : qhat hh p (u + δ) = qhat hh p u + (hh + p) * δ' - p * δ := by
          rw [qhat_eq, qhat_eq, hδ']; ring
        rw [q]
        obtain ⟨l1, l2⟩ := ih _ (next_mem hy hζ d) δ' hδ'0
        push_cast
        constructor
        · nlinarith [mul_nonneg hhh hδ'0, mul_nonneg (mul_nonneg hp hδ'0) (sub_nonneg.2 hγ1),
            mul_le_mul_of_nonneg_left l1 hγ0.le]
        · have hk : (0:ℝ) ≤ k * hh := by positivity
          nlinarith [mul_le_mul_of_nonneg_left l2 hγ0.le, mul_nonneg hp (sub_nonneg.2 hδ'1),
            mul_nonneg hhh (sub_nonneg.2 hδ'1), mul_nonneg hk (sub_nonneg.2 hδ'1),
            mul_nonneg (mul_nonneg hk hδ'0) (sub_nonneg.2 hγ1)]
      have i1 : ∫ d, (qhat hh p (vext y 0 - vext y 1 - d) +
          γ * fbar c hh p γ μ k (next y d ζ) - p * δ) ∂μ ≤
          ∫ d, (qhat hh p (vext (bump y δ) 0 - vext (bump y δ) 1 - d) +
          γ * fbar c hh p γ μ k (next (bump y δ) d ζ)) ∂μ :=
        integral_mono (G1.sub (integrable_const (p * δ))) G2 (fun d => (pw d).1)
      have i2 : ∫ d, (qhat hh p (vext (bump y δ) 0 - vext (bump y δ) 1 - d) +
          γ * fbar c hh p γ μ k (next (bump y δ) d ζ)) ∂μ ≤
          ∫ d, (qhat hh p (vext y 0 - vext y 1 - d) +
          γ * fbar c hh p γ μ k (next y d ζ) + ((k + 1 : ℕ) * hh) * δ) ∂μ :=
        integral_mono G2 (G1.add (integrable_const (((k + 1 : ℕ) * hh) * δ))) (fun d => (pw d).2)
      rw [integral_sub G1 (integrable_const _), integral_const] at i1
      rw [integral_add G1 (integrable_const _), integral_const] at i2
      simp only [probReal_univ, one_smul] at i1 i2
      constructor <;> linarith
    have := nonempty_Iic0
    have b1 := bdd_gstep c hh p γ hc hhh hp hγ0.le μ _ hF0 y
    have b2 := bdd_gstep c hh p γ hc hhh hp hγ0.le μ _ hF0 (bump y δ)
    rw [fbar_succ, fbar_succ]
    simp only [gbar]
    constructor
    · refine le_ciInf fun ζ => ?_
      have := ciInf_le b1 ζ
      linarith [(cmp ζ ζ.2).1]
    · have : (⨅ ζ : Set.Iic (0:ℝ), gstep c hh p γ μ (fbar c hh p γ μ k) (bump y δ) ζ) -
          ((k + 1 : ℕ) * hh) * δ ≤ ⨅ ζ : Set.Iic (0:ℝ), gstep c hh p γ μ (fbar c hh p γ μ k) y ζ := by
        refine le_ciInf fun ζ => ?_
        have := ciInf_le b2 ζ
        linarith [(cmp ζ ζ.2).2]
      linarith

theorem opt_fill_core {L : ℕ} (hh p γ : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (F : (Fin L → ℝ) → ℝ) (hlow : ∀ y ∈ V L, ∀ δ : ℝ, 0 ≤ δ → F y - p * δ ≤ F (bump y δ))
    {v : Fin L → ℝ} (hv : v ∈ V L) {ζ : ℝ} (hζ : ζ ≤ 0) {d : ℝ} (hd : 0 ≤ d) :
    kappa hh p γ F d v ζ = qhat hh p (vext v 0 - vext v 1 - d) + γ * F (next v d ζ) := by
  set m := max (vext v 0 - d) (vext v 1) with hm
  have h01 : vext v 1 ≤ vext v 0 := vext_anti hv (by omega)
  have hmem : m ∈ Set.Icc (max (vext v 0 - d) (vext v 1)) (vext v 0) :=
    ⟨le_rfl, max_le (by linarith) h01⟩
  have enext : next' m v ζ = next v d ζ := by
    funext l; unfold next' next
    split_ifs with hl
    · rw [hl, hm]
      rcases le_total (vext v 0 - d) (vext v 1) with h | h
      · rw [max_eq_right h, max_eq_right (by linarith)]; simp
      · rw [max_eq_left h, max_eq_left (by linarith)]; ring
    · simp
  have ebump : ∀ t, next' t v ζ = bump (next' m v ζ) (t - m) := by
    intro t; funext l; by_cases hl : (l : ℕ) = 0 <;> simp [next', bump, hl]
  have hge : ∀ t ∈ Set.Icc (max (vext v 0 - d) (vext v 1)) (vext v 0),
      psi hh p γ F d m v ζ ≤ psi hh p γ F d t v ζ := by
    intro t ht
    have htm : 0 ≤ t - m := by linarith [ht.1]
    have := hlow (next' m v ζ) (by rw [enext]; exact next_mem hv hζ d) (t - m) htm
    rw [← ebump] at this
    unfold psi
    nlinarith [mul_le_mul_of_nonneg_left this hγ0.le, mul_nonneg hhh htm,
      mul_nonneg (mul_nonneg hp htm) (sub_nonneg.2 hγ1)]
  have hne : Nonempty (Set.Icc (max (vext v 0 - d) (vext v 1)) (vext v 0)) := ⟨⟨m, hmem⟩⟩
  have hk : kappa hh p γ F d v ζ = psi hh p γ F d m v ζ := by
    unfold kappa
    apply le_antisymm
    · have hb : BddBelow (Set.range fun t : Set.Icc (max (vext v 0 - d) (vext v 1)) (vext v 0) =>
          psi hh p γ F d t v ζ) := ⟨psi hh p γ F d m v ζ, by rintro _ ⟨t, rfl⟩; exact hge t t.2⟩
      exact ciInf_le hb ⟨m, hmem⟩
    · exact le_ciInf fun t => hge t t.2
  rw [hk]
  unfold psi qhat
  rw [enext]
  have e1 : m - vext v 1 = max (vext v 0 - vext v 1 - d) 0 := by
    rw [hm]
    rcases le_total (vext v 0 - d) (vext v 1) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]; ring
    · rw [max_eq_left h, max_eq_left (by linarith)]; ring
  have e2 : m - vext v 0 + d = max (-(vext v 0 - vext v 1 - d)) 0 := by
    rw [hm]
    rcases le_total (vext v 0 - d) (vext v 1) with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  rw [e1, e2]

theorem optimal_fill_core (L : ℕ) (hL : 0 < L) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hμint : Integrable id μ)
    (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (k : ℕ) (v : Fin L → ℝ) (hv : v ∈ V L) (ζ : ℝ) (hζ : ζ ≤ 0) (d : ℝ) (hd : 0 ≤ d) :
    kappa hh p γ (fbar c hh p γ μ k) d v ζ =
      qhat hh p (vext v 0 - vext v 1 - d) + γ * fbar c hh p γ μ k (next v d ζ) :=
  opt_fill_core hh p γ hhh hp hγ0 hγ1 _
    (fun y hy δ hδ => (fbar_lip hL μ hμint c hh p γ hc hhh hp hγ0 hγ1 k y hy δ hδ).1) hv hζ hd

end ZipkinLostSales.LNatural

open ZipkinLostSales.LNatural


theorem solution (L : ℕ) (hL : 0 < L) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hμint : Integrable id μ)
    (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (k : ℕ) (v : Fin L → ℝ) (hv : v ∈ V L) (ζ : ℝ) (hζ : ζ ≤ 0) (d : ℝ) (hd : 0 ≤ d) :
    kappa hh p γ (fbar c hh p γ μ k) d v ζ =
      qhat hh p (vext v 0 - vext v 1 - d) + γ * fbar c hh p γ μ k (next v d ζ) := by
  exact optimal_fill_core L hL μ hμ hμint c hh p γ hc hhh hp hγ0 hγ1 k v hv ζ hζ d hd
