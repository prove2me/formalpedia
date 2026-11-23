-- Prove2me | solution 1 for TermCycDich.all_red_grid
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:49:52.86455+00:00
-- url     : https://prove2.me/submissions/8cc0a77c-5919-4d24-a034-8c66b15c0f2e

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
import Definitions.Def_RobertsonSeymour1986_GM5_grid
import Definitions.Def_TermCycDich_bidim

namespace AuxAllRedGrid

open RobertsonSeymour1986.GM5 TermCycDich

def pt {θ : ℕ} (v : Fin θ × Fin θ) : ℝ × ℝ :=
  ((v.1 : ℕ), (v.2 : ℕ))

lemma pt_injective (θ : ℕ) : Function.Injective (@pt θ) := by
  intro v w h
  rcases Prod.mk.inj h with ⟨h1, h2⟩
  exact Prod.ext (Fin.ext (Nat.cast_inj.mp h1)) (Fin.ext (Nat.cast_inj.mp h2))

def aff (a b t : ℝ) : ℝ :=
  (1 - t) * a + t * b

def segPath (p q : ℝ × ℝ) : Path p q where
  toFun t := (aff p.1 q.1 (t : ℝ), aff p.2 q.2 (t : ℝ))
  continuous_toFun := by
    unfold aff
    fun_prop
  source' := by
    ext <;> simp [aff]
  target' := by
    ext <;> simp [aff]

lemma adj_cases {θ : ℕ} {v w : Fin θ × Fin θ} (h : (grid θ).Adj v w) :
    (((w.1 : ℕ) : ℤ) = ((v.1 : ℕ) : ℤ) + 1 ∧ v.2 = w.2) ∨
    (((v.1 : ℕ) : ℤ) = ((w.1 : ℕ) : ℤ) + 1 ∧ v.2 = w.2) ∨
    (v.1 = w.1 ∧ ((w.2 : ℕ) : ℤ) = ((v.2 : ℕ) : ℤ) + 1) ∨
    (v.1 = w.1 ∧ ((v.2 : ℕ) : ℤ) = ((w.2 : ℕ) : ℤ) + 1) := by
  change |((v.1 : ℕ) : ℤ) - ((w.1 : ℕ) : ℤ)| + |((v.2 : ℕ) : ℤ) - ((w.2 : ℕ) : ℤ)| = 1 at h
  rcases abs_cases (((v.1 : ℕ) : ℤ) - ((w.1 : ℕ) : ℤ)) with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩ <;>
    rcases abs_cases (((v.2 : ℕ) : ℤ) - ((w.2 : ℕ) : ℤ)) with ⟨ha2, hb2⟩ | ⟨ha2, hb2⟩
  · by_cases h1 : ((v.1 : ℕ) : ℤ) = ((w.1 : ℕ) : ℤ)
    · exact Or.inr (Or.inr (Or.inr ⟨Fin.ext (Int.ofNat.inj h1), by omega⟩))
    · have h2 : ((v.2 : ℕ) : ℤ) = ((w.2 : ℕ) : ℤ) := by omega
      exact Or.inr (Or.inl ⟨by omega, Fin.ext (Int.ofNat.inj h2)⟩)
  · by_cases h1 : ((v.1 : ℕ) : ℤ) = ((w.1 : ℕ) : ℤ)
    · exact Or.inr (Or.inr (Or.inl ⟨Fin.ext (Int.ofNat.inj h1), by omega⟩))
    · have h2 : ((v.2 : ℕ) : ℤ) = ((w.2 : ℕ) : ℤ) := by omega
      exact Or.inr (Or.inl ⟨by omega, Fin.ext (Int.ofNat.inj h2)⟩)
  · by_cases h1 : ((v.1 : ℕ) : ℤ) = ((w.1 : ℕ) : ℤ)
    · exact Or.inr (Or.inr (Or.inr ⟨Fin.ext (Int.ofNat.inj h1), by omega⟩))
    · have h2 : ((v.2 : ℕ) : ℤ) = ((w.2 : ℕ) : ℤ) := by omega
      exact Or.inl ⟨by omega, Fin.ext (Int.ofNat.inj h2)⟩
  · by_cases h1 : ((v.1 : ℕ) : ℤ) = ((w.1 : ℕ) : ℤ)
    · exact Or.inr (Or.inr (Or.inl ⟨Fin.ext (Int.ofNat.inj h1), by omega⟩))
    · have h2 : ((v.2 : ℕ) : ℤ) = ((w.2 : ℕ) : ℤ) := by omega
      exact Or.inl ⟨by omega, Fin.ext (Int.ofNat.inj h2)⟩

lemma aff_int_step {a b x : ℤ} {t : unitInterval}
    (hstep : b = a + 1 ∨ a = b + 1)
    (heq : aff (a : ℝ) (b : ℝ) (t : ℝ) = (x : ℝ)) :
    (t = 0 ∧ x = a) ∨ (t = 1 ∧ x = b) := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  rcases hstep with rfl | rfl
  · push_cast at heq
    have hlo_r : (a : ℝ) ≤ (x : ℝ) := by unfold aff at heq; linarith
    have hhi_r : (x : ℝ) ≤ ((a + 1 : ℤ) : ℝ) := by unfold aff at heq; push_cast; linarith
    have hlo : a ≤ x := by exact_mod_cast hlo_r
    have hhi : x ≤ a + 1 := by exact_mod_cast hhi_r
    have hxa : x = a ∨ x = a + 1 := by omega
    rcases hxa with rfl | rfl
    · left
      refine ⟨Subtype.ext ?_, rfl⟩
      change (t : ℝ) = 0
      unfold aff at heq
      linarith
    · right
      refine ⟨Subtype.ext ?_, rfl⟩
      change (t : ℝ) = 1
      unfold aff at heq
      push_cast at heq
      linarith
  · push_cast at heq
    have hlo_r : (b : ℝ) ≤ (x : ℝ) := by unfold aff at heq; linarith
    have hhi_r : (x : ℝ) ≤ ((b + 1 : ℤ) : ℝ) := by unfold aff at heq; push_cast; linarith
    have hlo : b ≤ x := by exact_mod_cast hlo_r
    have hhi : x ≤ b + 1 := by exact_mod_cast hhi_r
    have hxb : x = b + 1 ∨ x = b := by omega
    rcases hxb with rfl | rfl
    · left
      refine ⟨Subtype.ext ?_, rfl⟩
      change (t : ℝ) = 0
      unfold aff at heq
      push_cast at heq
      linarith
    · right
      refine ⟨Subtype.ext ?_, rfl⟩
      change (t : ℝ) = 1
      unfold aff at heq
      linarith

lemma aff_bounds {a b m : ℤ} (hm : (a = m ∧ b = m + 1) ∨ (a = m + 1 ∧ b = m))
    (t : unitInterval) :
    (m : ℝ) ≤ aff (a : ℝ) (b : ℝ) (t : ℝ) ∧
      aff (a : ℝ) (b : ℝ) (t : ℝ) ≤ ((m + 1 : ℤ) : ℝ) := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (unfold aff; push_cast; constructor <;> linarith)

lemma unit_intervals_meet {a b c d : ℤ} {s t : unitInterval}
    (hab : b = a + 1 ∨ a = b + 1) (hcd : d = c + 1 ∨ c = d + 1)
    (heq : aff (a : ℝ) (b : ℝ) (s : ℝ) = aff (c : ℝ) (d : ℝ) (t : ℝ)) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨ ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) := by
  let m₁ : ℤ := min a b
  let m₂ : ℤ := min c d
  have hm₁ : (a = m₁ ∧ b = m₁ + 1) ∨ (a = m₁ + 1 ∧ b = m₁) := by
    rcases hab with rfl | rfl
    · left; exact ⟨by simp [m₁], by simp [m₁]⟩
    · right; exact ⟨by simp [m₁], by simp [m₁]⟩
  have hm₂ : (c = m₂ ∧ d = m₂ + 1) ∨ (c = m₂ + 1 ∧ d = m₂) := by
    rcases hcd with rfl | rfl
    · left; exact ⟨by simp [m₂], by simp [m₂]⟩
    · right; exact ⟨by simp [m₂], by simp [m₂]⟩
  obtain ⟨hlo₁, hhi₁⟩ := aff_bounds hm₁ s
  obtain ⟨hlo₂, hhi₂⟩ := aff_bounds hm₂ t
  have hle₁_r : (m₁ : ℝ) ≤ ((m₂ + 1 : ℤ) : ℝ) := by linarith
  have hle₂_r : (m₂ : ℝ) ≤ ((m₁ + 1 : ℤ) : ℝ) := by linarith
  have hle₁ : m₁ ≤ m₂ + 1 := by exact_mod_cast hle₁_r
  have hle₂ : m₂ ≤ m₁ + 1 := by exact_mod_cast hle₂_r
  have hcases : m₁ = m₂ ∨ m₂ = m₁ + 1 ∨ m₁ = m₂ + 1 := by omega
  rcases hcases with hm_eq | hm_eq | hm_eq
  · rcases hm₁ with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rcases hm₂ with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · left; omega
    · right; left; omega
    · right; left; omega
    · left; omega
  · right; right
    have hval₁ : aff (a : ℝ) (b : ℝ) (s : ℝ) = ((m₁ + 1 : ℤ) : ℝ) := by
      have : ((m₂ : ℤ) : ℝ) = ((m₁ + 1 : ℤ) : ℝ) := by exact_mod_cast hm_eq
      linarith
    have hval₂ : aff (c : ℝ) (d : ℝ) (t : ℝ) = (m₂ : ℝ) := by
      have : ((m₂ : ℤ) : ℝ) = ((m₁ + 1 : ℤ) : ℝ) := by exact_mod_cast hm_eq
      linarith
    have hs := aff_int_step hab hval₁
    have ht := aff_int_step hcd hval₂
    exact ⟨by rcases hs with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact Or.inl h; exact Or.inr h],
           by rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact Or.inl h; exact Or.inr h]⟩
  · right; right
    have hval₁ : aff (a : ℝ) (b : ℝ) (s : ℝ) = (m₁ : ℝ) := by
      have : ((m₁ : ℤ) : ℝ) = ((m₂ + 1 : ℤ) : ℝ) := by exact_mod_cast hm_eq
      linarith
    have hval₂ : aff (c : ℝ) (d : ℝ) (t : ℝ) = ((m₂ + 1 : ℤ) : ℝ) := by
      have : ((m₁ : ℤ) : ℝ) = ((m₂ + 1 : ℤ) : ℝ) := by exact_mod_cast hm_eq
      linarith
    have hs := aff_int_step hab hval₁
    have ht := aff_int_step hcd hval₂
    exact ⟨by rcases hs with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact Or.inl h; exact Or.inr h],
           by rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact Or.inl h; exact Or.inr h]⟩

def gridDrawing (θ : ℕ) : PlaneDrawing (grid θ) where
  vertex := pt
  vertex_injective := pt_injective θ
  arc {_ _} _ := segPath (pt _) (pt _)
  arc_injective {v w} h s t hst := by
    have hvw : pt v ≠ pt w := fun hp => (grid θ).ne_of_adj h (pt_injective θ hp)
    rcases Prod.mk.inj hst with ⟨h1, h2⟩
    change aff (pt v).1 (pt w).1 (s : ℝ) = aff (pt v).1 (pt w).1 (t : ℝ) at h1
    change aff (pt v).2 (pt w).2 (s : ℝ) = aff (pt v).2 (pt w).2 (t : ℝ) at h2
    unfold aff at h1 h2
    by_contra hne
    have hsr : (s : ℝ) ≠ (t : ℝ) := fun hr => hne (Subtype.ext hr)
    have hp1 : ((s : ℝ) - (t : ℝ)) * ((pt w).1 - (pt v).1) = 0 := by linarith
    have hp2 : ((s : ℝ) - (t : ℝ)) * ((pt w).2 - (pt v).2) = 0 := by linarith
    have e1 : (pt v).1 = (pt w).1 := by
      rcases mul_eq_zero.mp hp1 with hc | hc
      · exact False.elim (hsr (sub_eq_zero.mp hc))
      · linarith
    have e2 : (pt v).2 = (pt w).2 := by
      rcases mul_eq_zero.mp hp2 with hc | hc
      · exact False.elim (hsr (sub_eq_zero.mp hc))
      · linarith
    exact hvw (Prod.ext e1 e2)
  arc_reverse {v w} _ := by
    ext t <;> simp [segPath, aff] <;> ring
  arc_avoids_vertices {v w} h t x htx := by
    rcases Prod.mk.inj htx with ⟨hx1, hx2⟩
    change aff ((v.1 : ℕ) : ℝ) ((w.1 : ℕ) : ℝ) (t : ℝ) = ((x.1 : ℕ) : ℝ) at hx1
    change aff ((v.2 : ℕ) : ℝ) ((w.2 : ℕ) : ℝ) (t : ℝ) = ((x.2 : ℕ) : ℝ) at hx2
    rcases adj_cases h with ⟨hstep, hv2⟩ | ⟨hstep, hv2⟩ | ⟨hv1, hstep⟩ | ⟨hv1, hstep⟩
    · have hx2' : x.2 = v.2 := by
        rw [← hv2] at hx2; unfold aff at hx2
        have : ((v.2 : ℕ) : ℝ) = ((x.2 : ℕ) : ℝ) := by linear_combination hx2
        exact (Fin.ext (Nat.cast_inj.mp this)).symm
      have hs := aff_int_step (a := (v.1 : ℕ)) (b := (w.1 : ℕ)) (x := (x.1 : ℕ)) (Or.inl hstep)
        (by exact_mod_cast hx1)
      rcases hs with ⟨_, hx1'⟩ | ⟨_, hx1'⟩
      · left; exact Prod.ext (Fin.ext (Int.ofNat.inj hx1')) hx2'
      · right; exact Prod.ext (Fin.ext (Int.ofNat.inj hx1')) (hx2'.trans hv2)
    · have hx2' : x.2 = v.2 := by
        rw [← hv2] at hx2; unfold aff at hx2
        have : ((v.2 : ℕ) : ℝ) = ((x.2 : ℕ) : ℝ) := by linear_combination hx2
        exact (Fin.ext (Nat.cast_inj.mp this)).symm
      have hs := aff_int_step (a := (v.1 : ℕ)) (b := (w.1 : ℕ)) (x := (x.1 : ℕ)) (Or.inr hstep)
        (by exact_mod_cast hx1)
      rcases hs with ⟨_, hx1'⟩ | ⟨_, hx1'⟩
      · left; exact Prod.ext (Fin.ext (Int.ofNat.inj hx1')) hx2'
      · right; exact Prod.ext (Fin.ext (Int.ofNat.inj hx1')) (hx2'.trans hv2)
    · have hx1' : x.1 = v.1 := by
        rw [← hv1] at hx1; unfold aff at hx1
        have : ((v.1 : ℕ) : ℝ) = ((x.1 : ℕ) : ℝ) := by linear_combination hx1
        exact (Fin.ext (Nat.cast_inj.mp this)).symm
      have hs := aff_int_step (a := (v.2 : ℕ)) (b := (w.2 : ℕ)) (x := (x.2 : ℕ)) (Or.inl hstep)
        (by exact_mod_cast hx2)
      rcases hs with ⟨_, hx2'⟩ | ⟨_, hx2'⟩
      · left; exact Prod.ext hx1' (Fin.ext (Int.ofNat.inj hx2'))
      · right; exact Prod.ext (hx1'.trans hv1) (Fin.ext (Int.ofNat.inj hx2'))
    · have hx1' : x.1 = v.1 := by
        rw [← hv1] at hx1; unfold aff at hx1
        have : ((v.1 : ℕ) : ℝ) = ((x.1 : ℕ) : ℝ) := by linear_combination hx1
        exact (Fin.ext (Nat.cast_inj.mp this)).symm
      have hs := aff_int_step (a := (v.2 : ℕ)) (b := (w.2 : ℕ)) (x := (x.2 : ℕ)) (Or.inr hstep)
        (by exact_mod_cast hx2)
      rcases hs with ⟨_, hx2'⟩ | ⟨_, hx2'⟩
      · left; exact Prod.ext hx1' (Fin.ext (Int.ofNat.inj hx2'))
      · right; exact Prod.ext (hx1'.trans hv1) (Fin.ext (Int.ofNat.inj hx2'))
  arcs_meet_only_at_endpoints {v w x y} h k s t hst := by
    rcases Prod.mk.inj hst with ⟨he1, he2⟩
    change aff ((v.1 : ℕ) : ℝ) ((w.1 : ℕ) : ℝ) (s : ℝ) =
      aff ((x.1 : ℕ) : ℝ) ((y.1 : ℕ) : ℝ) (t : ℝ) at he1
    change aff ((v.2 : ℕ) : ℝ) ((w.2 : ℕ) : ℝ) (s : ℝ) =
      aff ((x.2 : ℕ) : ℝ) ((y.2 : ℕ) : ℝ) (t : ℝ) at he2
    have hv_dir : ((((w.1 : ℕ) : ℤ) = ((v.1 : ℕ) : ℤ) + 1 ∨
        ((v.1 : ℕ) : ℤ) = ((w.1 : ℕ) : ℤ) + 1) ∧ v.2 = w.2) ∨
        (v.1 = w.1 ∧ (((w.2 : ℕ) : ℤ) = ((v.2 : ℕ) : ℤ) + 1 ∨
        ((v.2 : ℕ) : ℤ) = ((w.2 : ℕ) : ℤ) + 1)) := by
      rcases adj_cases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
      · exact Or.inl ⟨Or.inl a, b⟩
      · exact Or.inl ⟨Or.inr a, b⟩
      · exact Or.inr ⟨a, Or.inl b⟩
      · exact Or.inr ⟨a, Or.inr b⟩
    have hx_dir : ((((y.1 : ℕ) : ℤ) = ((x.1 : ℕ) : ℤ) + 1 ∨
        ((x.1 : ℕ) : ℤ) = ((y.1 : ℕ) : ℤ) + 1) ∧ x.2 = y.2) ∨
        (x.1 = y.1 ∧ (((y.2 : ℕ) : ℤ) = ((x.2 : ℕ) : ℤ) + 1 ∨
        ((x.2 : ℕ) : ℤ) = ((y.2 : ℕ) : ℤ) + 1)) := by
      rcases adj_cases k with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
      · exact Or.inl ⟨Or.inl a, b⟩
      · exact Or.inl ⟨Or.inr a, b⟩
      · exact Or.inr ⟨a, Or.inl b⟩
      · exact Or.inr ⟨a, Or.inr b⟩
    rcases hv_dir with ⟨hvw1, hvw2⟩ | ⟨hvw1, hvw2⟩ <;>
      rcases hx_dir with ⟨hxy1, hxy2⟩ | ⟨hxy1, hxy2⟩
    · -- both horizontal in 1st coord
      have hc2 : v.2 = x.2 := by
        rw [← hvw2, ← hxy2] at he2; unfold aff at he2
        exact Fin.ext (Nat.cast_inj.mp (by linear_combination he2))
      rcases unit_intervals_meet hvw1 hxy1 (by exact_mod_cast he1) with
        ⟨e1, e2⟩ | ⟨e1, e2⟩ | hends
      · left
        exact ⟨Prod.ext (Fin.ext (Int.ofNat.inj e1)) hc2,
               Prod.ext (Fin.ext (Int.ofNat.inj e2)) (hvw2.symm.trans (hc2.trans hxy2))⟩
      · right; left
        exact ⟨Prod.ext (Fin.ext (Int.ofNat.inj e1)) (hc2.trans hxy2),
               Prod.ext (Fin.ext (Int.ofNat.inj e2)) (hvw2.symm.trans hc2)⟩
      · exact Or.inr (Or.inr hends)
    · -- vw step in 1st, xy step in 2nd
      right; right
      have h1 : aff ((v.1 : ℕ) : ℝ) ((w.1 : ℕ) : ℝ) (s : ℝ) = ((x.1 : ℕ) : ℝ) := by
        rw [← hxy1] at he1; unfold aff at he1 ⊢; linear_combination he1
      have h2 : aff ((x.2 : ℕ) : ℝ) ((y.2 : ℕ) : ℝ) (t : ℝ) = ((v.2 : ℕ) : ℝ) := by
        rw [← hvw2] at he2; unfold aff at he2 ⊢; linear_combination -he2
      have hs := aff_int_step hvw1 (x := (x.1 : ℕ)) (by exact_mod_cast h1)
      have ht := aff_int_step hxy2 (x := (v.2 : ℕ)) (by exact_mod_cast h2)
      exact ⟨by rcases hs with ⟨a, _⟩ | ⟨a, _⟩ <;> [exact Or.inl a; exact Or.inr a],
             by rcases ht with ⟨a, _⟩ | ⟨a, _⟩ <;> [exact Or.inl a; exact Or.inr a]⟩
    · -- vw step in 2nd, xy step in 1st
      right; right
      have h1 : aff ((x.1 : ℕ) : ℝ) ((y.1 : ℕ) : ℝ) (t : ℝ) = ((v.1 : ℕ) : ℝ) := by
        rw [← hvw1] at he1; unfold aff at he1 ⊢; linear_combination -he1
      have h2 : aff ((v.2 : ℕ) : ℝ) ((w.2 : ℕ) : ℝ) (s : ℝ) = ((x.2 : ℕ) : ℝ) := by
        rw [← hxy2] at he2; unfold aff at he2 ⊢; linear_combination he2
      have hs := aff_int_step hvw2 (x := (x.2 : ℕ)) (by exact_mod_cast h2)
      have ht := aff_int_step hxy1 (x := (v.1 : ℕ)) (by exact_mod_cast h1)
      exact ⟨by rcases hs with ⟨a, _⟩ | ⟨a, _⟩ <;> [exact Or.inl a; exact Or.inr a],
             by rcases ht with ⟨a, _⟩ | ⟨a, _⟩ <;> [exact Or.inl a; exact Or.inr a]⟩
    · -- both step in 2nd coord
      have hc1 : v.1 = x.1 := by
        rw [← hvw1, ← hxy1] at he1; unfold aff at he1
        exact Fin.ext (Nat.cast_inj.mp (by linear_combination he1))
      rcases unit_intervals_meet hvw2 hxy2 (by exact_mod_cast he2) with
        ⟨e1, e2⟩ | ⟨e1, e2⟩ | hends
      · left
        exact ⟨Prod.ext hc1 (Fin.ext (Int.ofNat.inj e1)),
               Prod.ext (hvw1.symm.trans (hc1.trans hxy1)) (Fin.ext (Int.ofNat.inj e2))⟩
      · right; left
        exact ⟨Prod.ext (hc1.trans hxy1) (Fin.ext (Int.ofNat.inj e1)),
               Prod.ext (hvw1.symm.trans hc1) (Fin.ext (Int.ofNat.inj e2))⟩
      · exact Or.inr (Or.inr hends)

lemma hasRedGrid_refl (θ : ℕ) : HasRedGrid (grid θ) Set.univ θ := by
  refine ⟨fun w => {w}, ?_, ?_, ?_, ?_⟩
  · intro w
    have : Nonempty ({w} : Set (Fin θ × Fin θ)) := ⟨⟨w, rfl⟩⟩
    refine ⟨⟨w, rfl⟩, SimpleGraph.Connected.mk ?_⟩
    intro ⟨a, ha⟩ ⟨b, hb⟩
    subst ha; subst hb
    exact SimpleGraph.Reachable.refl _
  · intro a b hab
    exact Set.disjoint_singleton.mpr hab
  · intro a b hadj
    exact ⟨a, rfl, b, rfl, hadj⟩
  · intro w _
    exact ⟨w, rfl, trivial⟩

lemma not_hasRedGrid_of_gt {θ k : ℕ} (hk : θ < k) : ¬ HasRedGrid (grid θ) Set.univ k := by
  rintro ⟨β, hconn, hdisj, _, _⟩
  choose f hf using fun w => (hconn w).1
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) (hf a) (hab ▸ hf b)
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  nlinarith

end AuxAllRedGrid

theorem solution (c : ℕ) :
    RobertsonSeymour1986.GM5.IsPlanar (RobertsonSeymour1986.GM5.grid (c + 1)) ∧
      TermCycDich.bidim (RobertsonSeymour1986.GM5.grid (c + 1)) Set.univ = c + 1 := by
  classical
  refine ⟨⟨AuxAllRedGrid.gridDrawing (c + 1)⟩, ?_⟩
  unfold TermCycDich.bidim
  convert (Nat.findGreatest_eq_iff (P := fun k =>
    TermCycDich.HasRedGrid (RobertsonSeymour1986.GM5.grid (c + 1)) Set.univ k)).mpr ?_
  refine ⟨?_, fun _ => AuxAllRedGrid.hasRedGrid_refl (c + 1), ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_fin]
    nlinarith
  · intro k hck _
    exact AuxAllRedGrid.not_hasRedGrid_of_gt hck
