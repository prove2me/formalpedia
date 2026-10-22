-- Prove2me | solution 1 for ProConChoice.Rational.rs_cs_matrix_tu
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:33:19.379844+00:00
-- url     : https://prove2.me/submissions/1df835d0-c2e3-48d2-ade1-15ebd8bd17dd

import Mathlib
set_option autoImplicit false

theorem solution {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] :
    (Matrix.of (fun (r : I ⊕ J) (c : I × J) =>
      Sum.elim (fun i => if c.1 = i then (1 : ℝ) else 0)
        (fun j => if c.2 = j then (1 : ℝ) else 0) r)).IsTotallyUnimodular := by
  set M : Matrix (I ⊕ J) (I × J) ℝ := Matrix.of (fun (r : I ⊕ J) (c : I × J) =>
      Sum.elim (fun i => if c.1 = i then (1 : ℝ) else 0)
        (fun j => if c.2 = j then (1 : ℝ) else 0) r) with hM
  have P0 : (0 : ℝ) ∈ Set.range (SignType.cast : SignType → ℝ) := ⟨0, by simp⟩
  have P1 : (1 : ℝ) ∈ Set.range (SignType.cast : SignType → ℝ) := ⟨1, by simp⟩
  have Pm1 : (-1 : ℝ) ∈ Set.range (SignType.cast : SignType → ℝ) := ⟨-1, by simp⟩
  have Pmul : ∀ a b : ℝ, a ∈ Set.range (SignType.cast : SignType → ℝ) →
      b ∈ Set.range (SignType.cast : SignType → ℝ) →
      a * b ∈ Set.range (SignType.cast : SignType → ℝ) := by
    rintro a b ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s * t, by simp⟩
  have Ppow : ∀ n : ℕ, ((-1 : ℝ) ^ n) ∈ Set.range (SignType.cast : SignType → ℝ) := by
    intro n
    rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] <;> assumption
  have main : ∀ (k : ℕ) (f : Fin k → I ⊕ J) (g : Fin k → I × J), Function.Injective f →
      (M.submatrix f g).det ∈ Set.range (SignType.cast : SignType → ℝ) := by
    intro k
    induction k with
    | zero => intro f g hf; simpa using P1
    | succ k ih =>
      intro f g hf
      set B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ := M.submatrix f g with hBdef
      have hB : ∀ r c, B r c = Sum.elim (fun i => if (g c).1 = i then (1 : ℝ) else 0)
          (fun j => if (g c).2 = j then (1 : ℝ) else 0) (f r) := by
        intro r c; simp [hBdef, hM]
      have hnz : ∀ r c, B r c ≠ 0 → f r = Sum.inl (g c).1 ∨ f r = Sum.inr (g c).2 := by
        intro r c hne
        rw [hB] at hne
        rcases hfr : f r with i | j
        · rw [hfr] at hne
          simp only [Sum.elim_inl] at hne
          left
          by_cases h : (g c).1 = i
          · rw [h]
          · simp [h] at hne
        · rw [hfr] at hne
          simp only [Sum.elim_inr] at hne
          right
          by_cases h : (g c).2 = j
          · rw [h]
          · simp [h] at hne
      have hentry : ∀ r c, B r c ∈ Set.range (SignType.cast : SignType → ℝ) := by
        intro r c
        rw [hB]
        rcases f r with i | j
        · simp only [Sum.elim_inl]; split_ifs <;> assumption
        · simp only [Sum.elim_inr]; split_ifs <;> assumption
      by_cases h : ∃ c r0, ∀ r, r ≠ r0 → B r c = 0
      · obtain ⟨c, r0, h0⟩ := h
        rw [Matrix.det_succ_column B c, Finset.sum_eq_single r0]
        · have hsub : B.submatrix r0.succAbove c.succAbove
              = M.submatrix (f ∘ r0.succAbove) (g ∘ c.succAbove) := by
            rw [hBdef, Matrix.submatrix_submatrix]
          rw [hsub]
          exact Pmul _ _ (Pmul _ _ (Ppow _) (hentry r0 c))
            (ih _ _ (hf.comp (Fin.succAbove_right_injective)))
        · intro r _ hr
          rw [h0 r hr]; simp
        · intro h'; exact absurd (Finset.mem_univ _) h'
      · push_neg at h
        have hI : ∀ c, ∃ rI, f rI = Sum.inl (g c).1 := by
          intro c
          by_contra hno
          push_neg at hno
          by_cases hex : ∃ r1, f r1 = Sum.inr (g c).2
          · obtain ⟨r1, hr1⟩ := hex
            obtain ⟨r, hrne, hrnz⟩ := h c r1
            rcases hnz r c hrnz with h1 | h1
            · exact hno r h1
            · exact hrne (hf (h1.trans hr1.symm))
          · obtain ⟨r, _, hrnz⟩ := h c 0
            rcases hnz r c hrnz with h1 | h1
            · exact hno r h1
            · exact hex ⟨r, h1⟩
        have hJ : ∀ c, ∃ rJ, f rJ = Sum.inr (g c).2 := by
          intro c
          by_contra hno
          push_neg at hno
          by_cases hex : ∃ r1, f r1 = Sum.inl (g c).1
          · obtain ⟨r1, hr1⟩ := hex
            obtain ⟨r, hrne, hrnz⟩ := h c r1
            rcases hnz r c hrnz with h1 | h1
            · exact hrne (hf (h1.trans hr1.symm))
            · exact hno r h1
          · obtain ⟨r, _, hrnz⟩ := h c 0
            rcases hnz r c hrnz with h1 | h1
            · exact hex ⟨r, h1⟩
            · exact hno r h1
        set v : Fin (k + 1) → ℝ := fun r => Sum.elim (fun _ => (1 : ℝ)) (fun _ => (-1 : ℝ)) (f r)
          with hv
        have hvB : Matrix.vecMul v B = 0 := by
          funext c
          obtain ⟨rI, hrI⟩ := hI c
          obtain ⟨rJ, hrJ⟩ := hJ c
          have hne : rI ≠ rJ := by
            intro heq
            rw [heq] at hrI
            rw [hrI] at hrJ
            exact Sum.inl_ne_inr hrJ
          simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
          rw [Finset.sum_eq_add rI rJ hne]
          · have e1 : B rI c = 1 := by rw [hB, hrI]; simp
            have e2 : B rJ c = 1 := by rw [hB, hrJ]; simp
            have v1 : v rI = 1 := by simp [hv, hrI]
            have v2 : v rJ = -1 := by simp [hv, hrJ]
            rw [e1, e2, v1, v2]; ring
          · intro r _ hr
            by_cases hz : B r c = 0
            · rw [hz]; simp
            · exfalso
              rcases hnz r c hz with h1 | h1
              · exact hr.1 (hf (h1.trans hrI.symm))
              · exact hr.2 (hf (h1.trans hrJ.symm))
          · intro h'; exact absurd (Finset.mem_univ _) h'
          · intro h'; exact absurd (Finset.mem_univ _) h'
        have hv0 : v ≠ 0 := by
          intro h0
          have := congrFun h0 0
          simp only [hv, Pi.zero_apply] at this
          generalize f 0 = x at this
          rcases x with i | j <;> simp at this
        have hdet : B.det = 0 := Matrix.exists_vecMul_eq_zero_iff.mp ⟨v, hv0, hvB⟩
        rw [hdet]; exact P0
  intro k f g hf _
  exact main k f g hf
