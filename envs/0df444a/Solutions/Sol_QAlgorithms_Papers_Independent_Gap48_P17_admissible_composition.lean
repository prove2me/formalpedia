-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P17.admissible_composition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:09:30.214008+00:00
-- url     : https://prove2.me/submissions/2e9cffac-11d5-47cc-b947-bfbcfb58d79c

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17
open QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

section
set_option linter.unusedSectionVars false
variable {K : Type*} [Field K] [CharZero K] {d : ℕ}
variable {g : Matrix (Fin d) (Fin d) K}
variable {S : Type*} [AddCommGroup S] [Module K S]

theorem g74c_sign_sq {t : K} (h : IsSign t) : t * t = 1 := by
  rcases h with rfl | rfl <;> norm_num

theorem g74c_cva (rho : SpinRepresentation g S) (v : Fin d → K) :
    cliffordVectorAction rho v = rho.action (CliffordAlgebra.ι (cliffordQ g) v) := rfl

theorem g74c_even_comm (rho : SpinRepresentation g S) (A : Module.End K S) (τ : K)
    (hτ : IsSign τ) (hA : ∀ v, cliffordVectorAction rho v * A = τ • (A * cliffordVectorAction rho v))
    (a : CliffordAlgebra.even (cliffordQ g)) : rho.action a.val * A = A * rho.action a.val := by
  obtain ⟨x, hx⟩ := a
  change rho.action x * A = A * rho.action x
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r A
  | add x y hx hy ihx ihy => rw [map_add, add_mul, mul_add, ihx, ihy]
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul, ← g74c_cva, ← g74c_cva]
    have h1 : cliffordVectorAction rho m₁ * (cliffordVectorAction rho m₂ * A) =
        A * (cliffordVectorAction rho m₁ * cliffordVectorAction rho m₂) := by
      rw [hA, mul_smul_comm, ← mul_assoc, hA, smul_mul_assoc, smul_smul, g74c_sign_sq hτ,
        one_smul, mul_assoc]
    rw [mul_assoc, mul_assoc, ih, ← mul_assoc (cliffordVectorAction rho m₂),
      ← mul_assoc (cliffordVectorAction rho m₁), h1]
    simp only [mul_assoc]

theorem g74c_form_gen (rho : SpinRepresentation g S) (b : LinearMap.BilinForm K S) (τ σ : K)
    (h : FormSigns rho b τ σ) (u v : Fin d → K) (s t : S) :
    b (spinGenerator rho u v s) t = - b s (spinGenerator rho u v t) := by
  obtain ⟨hτ, -, hc, -⟩ := h
  have key : ∀ x y : Fin d → K, ∀ s t, b ((cliffordVectorAction rho x * cliffordVectorAction rho y) s) t
      = b s ((cliffordVectorAction rho y * cliffordVectorAction rho x) t) := by
    intro x y s t
    simp only [Module.End.mul_apply]
    rw [hc, hc, ← mul_assoc, g74c_sign_sq hτ, one_mul]
  simp only [spinGenerator, LinearMap.smul_apply, LinearMap.sub_apply, map_smul, map_sub,
    LinearMap.smul_apply, LinearMap.sub_apply, key, smul_eq_mul]
  ring

theorem g74c_inv (rho : SpinRepresentation g S) (b : LinearMap.BilinForm K S) (τ σ : K)
    (h : FormSigns rho b τ σ) : b ∈ invariantForms rho := by
  intro u v s t
  rw [g74c_form_gen rho b τ σ h]; ring

theorem g74c_isSign_mul {a b : K} (ha : IsSign a) (hb : IsSign b) : IsSign (a * b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [IsSign]

end
section
set_option linter.unusedSectionVars false
variable {K : Type*} [Field K] [CharZero K] {d : ℕ}
variable {g : Matrix (Fin d) (Fin d) K}
variable {S : Type*} [AddCommGroup S] [Module K S]

theorem g74c_swap {X A : Module.End K S} {τ : K} (hτ : IsSign τ) (h : X * A = τ • (A * X))
    (s : S) : A (X s) = τ • X (A s) := by
  have := congrArg (fun F : Module.End K S => F s) h
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
  rw [this, smul_smul, g74c_sign_sq hτ, one_smul]

theorem g74c_gen_comm (rho : SpinRepresentation g S) (A : Module.End K S) (τ : K)
    (hτ : IsSign τ) (hA : ∀ v, cliffordVectorAction rho v * A = τ • (A * cliffordVectorAction rho v))
    (u v : Fin d → K) : spinGenerator rho u v * A = A * spinGenerator rho u v := by
  have h1 : ∀ x y : Fin d → K, cliffordVectorAction rho x * cliffordVectorAction rho y * A =
      A * (cliffordVectorAction rho x * cliffordVectorAction rho y) := by
    intro x y
    rw [mul_assoc, hA, mul_smul_comm, ← mul_assoc, hA, smul_mul_assoc, smul_smul, g74c_sign_sq hτ,
      one_smul, mul_assoc]
  simp only [spinGenerator, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, h1]

end

/-- Definition 2.2 consequence, PDF p. 18. Composition multiplies all defined signs;
this uses witnesses, and does not assign unique invariants to a zero composite. -/
theorem solution (p q : ℕ) (hd : 0 < p + q)
    (S : Type*) [AddCommGroup S] [Module ℝ S] [FiniteDimensional ℝ S]
    (rho : SpinRepresentation (signatureMatrix p q) S)
    (splitting : Option (SpinSplitting rho)) (hs : CompleteSplitting rho splitting)
    (b : LinearMap.BilinForm ℝ S) (hb : FormAdmissible rho splitting b)
    (A : Module.End ℝ S) (hA : EndAdmissible rho splitting b A) :
    A ∈ schurAlgebra rho ∧ formCompose b A ∈ invariantForms rho ∧
    FormAdmissible rho splitting (formCompose b A) ∧
    (∀ tau sigma tauA sigmaA : ℝ,
      FormSigns rho b tau sigma → EndSigns rho b A tauA sigmaA →
        FormSigns rho (formCompose b A) (tau * tauA) (sigma * sigmaA)) ∧
    (∀ h : SpinSplitting rho, splitting = some h →
      ∀ i iA : ℝ, FormIsotropy h.grading b i → EndIsotropy h.grading A iA →
        FormIsotropy h.grading (formCompose b A) (i * iA)) := by
  obtain ⟨tau, sigma, hbs, hbi⟩ := hb
  obtain ⟨tauA, sigmaA, hAs, hAi⟩ := hA
  have C4 : ∀ tau sigma tauA sigmaA : ℝ,
      FormSigns rho b tau sigma → EndSigns rho b A tauA sigmaA →
        FormSigns rho (formCompose b A) (tau * tauA) (sigma * sigmaA) := by
    intro tau sigma tauA sigmaA h1 h2
    obtain ⟨t1, s1, c1, y1⟩ := h1
    obtain ⟨t2, s2, c2, y2⟩ := h2
    refine ⟨g74c_isSign_mul t1 t2, g74c_isSign_mul s1 s2, ?_, ?_⟩
    · intro v s t
      simp only [formCompose, LinearMap.comp_apply]
      rw [g74c_swap t2 (c2 v), map_smul, LinearMap.smul_apply, c1, smul_eq_mul]; ring
    · intro s t
      simp only [formCompose, LinearMap.comp_apply]
      rw [y2 t s, y1 (A s) t]; ring
  have C5 : ∀ h : SpinSplitting rho, splitting = some h →
      ∀ i iA : ℝ, FormIsotropy h.grading b i → EndIsotropy h.grading A iA →
        FormIsotropy h.grading (formCompose b A) (i * iA) := by
    intro h _ i iA h1 h2
    obtain ⟨t1, c1⟩ := h1
    obtain ⟨t2, c2⟩ := h2
    refine ⟨g74c_isSign_mul t1 t2, ?_⟩
    intro s t
    simp only [formCompose, LinearMap.comp_apply]
    rw [g74c_swap t2 c2, map_smul, LinearMap.smul_apply, c1, smul_eq_mul]; ring
  refine ⟨?_, ?_, ?_, C4, C5⟩
  · rw [schurAlgebra, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    exact g74c_even_comm rho A tauA hAs.1 hAs.2.2.1 a
  · intro u v s t
    simp only [formCompose, LinearMap.comp_apply]
    have := congrArg (fun F : Module.End ℝ S => F s) (g74c_gen_comm rho A tauA hAs.1 hAs.2.2.1 u v)
    simp only [Module.End.mul_apply] at this
    rw [← this, g74c_form_gen rho b tau sigma hbs]; ring
  · refine ⟨tau * tauA, sigma * sigmaA, C4 _ _ _ _ hbs hAs, ?_⟩
    cases splitting with
    | none => trivial
    | some h =>
      obtain ⟨i, hi⟩ := hbi
      obtain ⟨iA, hiA⟩ := hAi
      exact ⟨i * iA, C5 h rfl i iA hi hiA⟩
