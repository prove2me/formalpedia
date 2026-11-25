-- Prove2me | solution 1 for SteerableE2CNN.vector_field_nonlinearity_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:36:26.121436+00:00
-- url     : https://prove2.me/submissions/6ecc46c4-aa6e-40e7-88d4-b15a0a139bef

import Mathlib
import Definitions.Def_SteerableE2CNN_Basic

set_option autoImplicit false

open Matrix MeasureTheory
namespace SteerableE2CNN

lemma vf_reg_apply (N : ℕ) [NeZero N] (p : ZMod N) (v : ZMod N → ℝ) (q : ZMod N) :
    (regRepCN N p *ᵥ v) q = v (q - p) := by
  simp only [Matrix.mulVec, dotProduct, regRepCN, Matrix.of_apply]
  have : ∀ b : ZMod N, (if q = p + b then (1:ℝ) else 0) * v b
      = if q - p = b then v b else 0 := by
    intro b
    have e : (q = p + b) ↔ (q - p = b) := by
      constructor
      · rintro rfl; ring
      · rintro rfl; ring
    by_cases h : q = p + b
    · rw [if_pos h, if_pos (e.1 h)]; ring
    · rw [if_neg h, if_neg (fun h' => h (e.2 h'))]; ring
  rw [Finset.sum_congr rfl (fun b _ => this b)]
  simp

lemma vf_argmax_spec (N : ℕ) [NeZero N] (v : ZMod N → ℝ) :
    ∀ b, v b ≤ v (vfArgmax N v) := by
  intro b
  have := (Classical.choose_spec (Finset.exists_max_image Finset.univ v Finset.univ_nonempty)).2
  exact this b (Finset.mem_univ b)

lemma vf_sup_eq (N : ℕ) [NeZero N] (v : ZMod N → ℝ) (m : ZMod N) (hm : ∀ b, v b ≤ v m) :
    Finset.univ.sup' Finset.univ_nonempty v = v m :=
  le_antisymm (Finset.sup'_le _ _ (fun b _ => hm b)) (Finset.le_sup' v (Finset.mem_univ m))

lemma vf_angle (N : ℕ) [NeZero N] (a p : ZMod N) :
    Real.cos (2 * Real.pi * ((a + p).val : ℝ) / N) =
      Real.cos (2 * Real.pi * (p.val : ℝ) / N + 2 * Real.pi * (a.val : ℝ) / N) ∧
    Real.sin (2 * Real.pi * ((a + p).val : ℝ) / N) =
      Real.sin (2 * Real.pi * (p.val : ℝ) / N + 2 * Real.pi * (a.val : ℝ) / N) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  rw [ZMod.val_add]
  set x := a.val + p.val
  have hx : ((x % N : ℕ) : ℝ) = (x : ℝ) - N * ((x / N : ℕ) : ℝ) := by
    have := Nat.mod_add_div x N
    have h' : ((x % N : ℕ) : ℝ) + N * ((x / N : ℕ) : ℝ) = x := by exact_mod_cast this
    linarith
  have e : 2 * Real.pi * ((x % N : ℕ) : ℝ) / N =
      (2 * Real.pi * (p.val : ℝ) / N + 2 * Real.pi * (a.val : ℝ) / N) - ((x / N : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [hx]; simp only [x, Nat.cast_add]; field_simp; ring
  rw [e]
  exact ⟨Real.cos_sub_nat_mul_two_pi _ _, Real.sin_sub_nat_mul_two_pi _ _⟩

theorem vector_field_nonlinearity_equivariant (N : ℕ) [NeZero N] (v : ZMod N → ℝ)
    (hv : ∃! a : ZMod N, ∀ b, v b ≤ v a) (p : ZMod N) :
    vecFieldNL N (regRepCN N p *ᵥ v) = rotMat (2 * Real.pi * (p.val : ℝ) / N) *ᵥ vecFieldNL N v := by
  obtain ⟨a, ha, huniq⟩ := hv
  set w := regRepCN N p *ᵥ v with hw
  have hwq : ∀ q, w q = v (q - p) := fun q => vf_reg_apply N p v q
  have h1 : vfArgmax N v = a := huniq _ (vf_argmax_spec N v)
  have h2 : vfArgmax N w = a + p := by
    have hs := vf_argmax_spec N w
    have : ∀ b, v b ≤ v (vfArgmax N w - p) := by
      intro b
      have := hs (b + p)
      rw [hwq, hwq] at this
      simpa using this
    have := huniq _ this
    rw [← this]; ring
  have s1 : Finset.univ.sup' Finset.univ_nonempty v = v a := vf_sup_eq N v a ha
  have s2 : Finset.univ.sup' Finset.univ_nonempty w = v a := by
    rw [vf_sup_eq N w (a + p)]
    · rw [hwq]; simp
    · intro b; rw [hwq, hwq]; simpa using ha (b - p)
  unfold vecFieldNL
  rw [h1, h2, s1, s2, Matrix.mulVec_smul]
  obtain ⟨hc, hs⟩ := vf_angle N a p
  rw [hc, hs]
  congr 1
  ext i
  fin_cases i
  all_goals simp [rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Real.cos_add, Real.sin_add]
  all_goals ring

end SteerableE2CNN

open SteerableE2CNN in
theorem solution (N : ℕ) [NeZero N] (v : ZMod N → ℝ)
    (hv : ∃! a : ZMod N, ∀ b, v b ≤ v a) (p : ZMod N) :
    vecFieldNL N (regRepCN N p *ᵥ v) = rotMat (2 * Real.pi * (p.val : ℝ) / N) *ᵥ vecFieldNL N v :=
  SteerableE2CNN.vector_field_nonlinearity_equivariant N v hv p
