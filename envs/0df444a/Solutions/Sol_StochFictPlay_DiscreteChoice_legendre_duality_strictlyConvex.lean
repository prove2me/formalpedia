-- Prove2me | solution 1 for StochFictPlay.DiscreteChoice.legendre_duality_strictlyConvex
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T00:03:44.057616+00:00
-- url     : https://prove2.me/submissions/0d98ee9e-87b0-4d26-ac62-58fc2804add5

import Mathlib

set_option autoImplicit false

section HelpersE8638dfb

/-- The quadratic `q x = (x 0)^2 / 2` on `Fin 1 → ℝ` has derivative `v ↦ x 0 * v 0`. -/
theorem fderiv_halfsq_e8638dfb (x v : Fin 1 → ℝ) :
    fderiv ℝ (fun x : Fin 1 → ℝ => x 0 ^ 2 / 2) x v = x 0 * v 0 := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 1 => ℝ) (0 : Fin 1) x
  have h1 := (h0.mul h0).mul_const (1 / 2 : ℝ)
  have h3 : (fun x : Fin 1 → ℝ => x 0 ^ 2 / 2) =
      (fun y => ((fun f : Fin 1 → ℝ => f 0) * fun f : Fin 1 → ℝ => f 0) y * (1 / 2)) := by
    funext y
    simp only [Pi.mul_apply]
    ring
  rw [h3, h1.fderiv]
  simp
  ring

theorem halfsq_strictConvexOn_e8638dfb :
    StrictConvexOn ℝ {x : Fin 1 → ℝ | 0 < x 0} (fun x : Fin 1 → ℝ => x 0 ^ 2 / 2) := by
  refine ⟨convex_halfSpace_gt (f := fun x : Fin 1 → ℝ => x 0)
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩ 0, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  have hne : x 0 ≠ y 0 := by
    intro h
    apply hxy
    funext i
    rw [Subsingleton.elim i 0]
    exact h
  have hpos : 0 < a * b * (x 0 - y 0) ^ 2 :=
    mul_pos (mul_pos ha hb)
      (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hne))))
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [hpos]

end HelpersE8638dfb

theorem solution : ¬ (∀ {n : ℕ} (W : (Fin n → ℝ) → ℝ)
    (O : Set (Fin n → ℝ)) (hO : IsOpen O) (hW : StrictConvexOn ℝ O W)
    (C : (Fin n → ℝ) → (Fin n → ℝ))
    (hgrad : ∀ x ∈ O, ∀ i : Fin n,
      C x i = fderiv ℝ W x ((Pi.single i (1 : ℝ)) : Fin n → ℝ))
    (hinjC : Set.InjOn C O)
    (O' : Set (Fin n → ℝ)) (hO' : IsOpen O') (hrange : C '' O = O')
    (V : (Fin n → ℝ) → ℝ)
    (hV : ∀ y ∈ O', V y =
      Finset.sum Finset.univ (fun i => y i * Function.invFun C y i)
        - W (Function.invFun C y)),
    (ContDiffOn ℝ 2 V O')
      ∧ (∀ y ∈ O', ∀ i : Fin n,
          fderiv ℝ V y ((Pi.single i (1 : ℝ)) : Fin n → ℝ) = Function.invFun C y i)
      ∧ StrictConvexOn ℝ O' V
      ∧ (∀ y₀ ∈ frontier O', ∀ M : ℝ, ∀ᶠ y in nhdsWithin y₀ O',
          M < ‖((fun i : Fin n => fderiv ℝ V y ((Pi.single i (1 : ℝ)) : Fin n → ℝ)) :
            Fin n → ℝ)‖)
      ∧ ∀ π ∈ O,
          IsMaxOn (fun y => Finset.sum Finset.univ (fun i => y i * π i) - V y) O' (C π)
            ∧ ∀ y ∈ O',
              IsMaxOn (fun y => Finset.sum Finset.univ (fun i => y i * π i) - V y) O' y
                → y = C π) := by
  intro h
  set O : Set (Fin 1 → ℝ) := {x | 0 < x 0} with hOdef
  have hOopen : IsOpen O := isOpen_lt continuous_const (continuous_apply 0)
  have hinv : ∀ y : Fin 1 → ℝ, Function.invFun (id : (Fin 1 → ℝ) → (Fin 1 → ℝ)) y = y :=
    fun y => Function.invFun_eq (f := (id : (Fin 1 → ℝ) → (Fin 1 → ℝ))) ⟨y, rfl⟩
  have hgrad : ∀ x ∈ O, ∀ i : Fin 1,
      (id : (Fin 1 → ℝ) → (Fin 1 → ℝ)) x i =
        fderiv ℝ (fun x : Fin 1 → ℝ => x 0 ^ 2 / 2) x ((Pi.single i (1 : ℝ)) : Fin 1 → ℝ) := by
    intro x _ i
    rw [fderiv_halfsq_e8638dfb, Subsingleton.elim i 0]
    simp
  have hV : ∀ y ∈ O, (fun x : Fin 1 → ℝ => x 0 ^ 2 / 2) y =
      Finset.sum Finset.univ (fun i => y i * Function.invFun
        (id : (Fin 1 → ℝ) → (Fin 1 → ℝ)) y i)
        - (fun x : Fin 1 → ℝ => x 0 ^ 2 / 2) (Function.invFun
          (id : (Fin 1 → ℝ) → (Fin 1 → ℝ)) y) := by
    intro y _
    simp only [hinv, Fin.sum_univ_one]
    ring
  obtain ⟨-, -, -, h4, -⟩ := h (n := 1) (fun x : Fin 1 → ℝ => x 0 ^ 2 / 2) O hOopen
    halfsq_strictConvexOn_e8638dfb id hgrad (Function.injective_id.injOn) O hOopen
    (Set.image_id O) (fun x : Fin 1 → ℝ => x 0 ^ 2 / 2) hV
  -- 0 lies on the frontier of O
  have hcl : (0 : Fin 1 → ℝ) ∈ closure O := by
    have ht : Filter.Tendsto (fun t : ℝ => (fun _ : Fin 1 => t)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (0 : Fin 1 → ℝ)) := by
      have hc : Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) := continuous_pi (fun _ => continuous_id)
      have := hc.tendsto 0
      exact this.mono_left nhdsWithin_le_nhds
    apply mem_closure_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  have hfr : (0 : Fin 1 → ℝ) ∈ frontier O := by
    rw [hOopen.frontier_eq]
    refine ⟨hcl, ?_⟩
    simp [hOdef]
  have hev := h4 0 hfr 1
  have hne : Filter.NeBot (nhdsWithin (0 : Fin 1 → ℝ) O) := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hev2 : ∀ᶠ y in nhdsWithin (0 : Fin 1 → ℝ) O, y ∈ O := self_mem_nhdsWithin
  have hev3 : ∀ᶠ y in nhdsWithin (0 : Fin 1 → ℝ) O, y 0 < 1 := by
    apply nhdsWithin_le_nhds
    have : (fun y : Fin 1 → ℝ => y 0) ⁻¹' Set.Iio 1 ∈ nhds (0 : Fin 1 → ℝ) :=
      (continuous_apply 0).continuousAt.preimage_mem_nhds (Iio_mem_nhds (by simp))
    exact this
  obtain ⟨y, hy1, hy2, hy3⟩ := (hev.and (hev2.and hev3)).exists
  have hvec : (fun i : Fin 1 => fderiv ℝ (fun x : Fin 1 → ℝ => x 0 ^ 2 / 2) y
      ((Pi.single i (1 : ℝ)) : Fin 1 → ℝ)) = y := by
    funext i
    rw [fderiv_halfsq_e8638dfb, Subsingleton.elim i 0]
    simp
  rw [hvec] at hy1
  have hlt : ‖y‖ < 1 := by
    rw [pi_norm_lt_iff one_pos]
    intro i
    rw [Subsingleton.elim i 0, Real.norm_eq_abs, abs_lt]
    have : 0 < y 0 := hy2
    constructor <;> linarith
  linarith
