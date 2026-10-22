-- Prove2me | solution 1 for ZipkinLostSales.LNatural.psi_lnatconvex
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:10:51.99837+00:00
-- url     : https://prove2.me/submissions/de9ee5dc-fdee-49b2-9719-2485780443ef

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

end ZipkinLostSales.LNatural

open ZipkinLostSales.LNatural


theorem solution (L : ℕ) (hL : 0 < L) (hh p γ : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (F : (Fin L → ℝ) → ℝ) (hF : LNatConvexOn (V L) F)
    (d : ℝ) (hd : 0 ≤ d) :
    LNatConvexOn (Dpsi L d) (liftPsi hh p γ F d) := by
  exact psi_core L hL hh p γ hhh hp hγ0 hγ1 F hF d hd
