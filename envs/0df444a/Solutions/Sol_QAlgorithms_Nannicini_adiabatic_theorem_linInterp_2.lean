-- Prove2me | solution 2 for QAlgorithms.Nannicini.adiabatic_theorem_linInterp
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-30T14:24:02.136253+00:00
-- url     : https://prove2.me/submissions/c1b857be-7342-4b7a-b30b-e82430ca9a7e

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Theorems.Thm_QAlgorithms_Nannicini_adiabatic_linInterp_frame
import Theorems.Thm_QAlgorithms_Nannicini_norm_le_of_schrodinger_source
import Theorems.Thm_QAlgorithms_Nannicini_eigvec_eq_smul_of_hasGapAround

set_option autoImplicit false

open QAlgorithms




open QAlgorithms.Nannicini

theorem red_act_sub {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    act A (x - y) = act A x - act A y := by
  simp [act, Matrix.mulVec_sub]

theorem red_act_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (c : ℂ)
    (x : EuclideanSpace ℂ ι) : act A (c • x) = c • act A x := by
  simp [act, Matrix.mulVec_smul]

theorem red_act_zero {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    act A (0 : EuclideanSpace ℂ ι) = 0 := by
  simp [act]

theorem solution.{u} :
    ∃ c : ℝ, ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (HI HF : Matrix ι ι ℂ),
      HI.IsHermitian → HF.IsHermitian →
      ∀ (lam : ℝ → ℝ), ContinuousOn lam (Set.Icc 0 1) →
      ∀ (φ : ℝ → EuclideanSpace ℂ ι),
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        IsState (φ s) ∧ act (linInterp HI HF s) (φ s) = (lam s : ℂ) • φ s) →
      ∀ (γ : ℝ), 0 < γ →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (linInterp HI HF s) (lam s) γ) →
      ∀ (δ : ℝ), 0 < δ → ∀ (T : ℝ),
      c / δ * (specNorm (HF - HI) / γ ^ 2 + specNorm (HF - HI) ^ 2 / γ ^ 3) ≤ T →
      ∀ (ψ : ℝ → EuclideanSpace ℂ ι), SolvesAdiabaticPlus (linInterp HI HF) T ψ → ψ 0 = φ 0 →
      ∃ θ : ℝ, ‖Complex.exp ((θ : ℂ) * Complex.I) • ψ 1 - φ 1‖ ≤ δ := by
  obtain ⟨K, hK⟩ := adiabatic_linInterp_frame.{u}
  refine ⟨2 * max K 0 + 1, ?_⟩
  intro ι _ _ HI HF hI hF lam hlam φ hφ γ hγ hgap δ hδ T hT ψ hψ hψ0
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨u, u', v, v', hu0, hfr⟩ :=
    hK HI HF hI hF lam hlam (φ 0) (hφ 0 h0).1 (hφ 0 h0).2 γ hγ hgap
  set H := linInterp HI HF with hHdef
  set N := specNorm (HF - HI) with hN
  have hN0 : 0 ≤ N := by
    rw [hN]; unfold specNorm
    letI : NormedAddCommGroup (Matrix ι ι ℂ) := Matrix.instL2OpNormedAddCommGroup
    exact norm_nonneg _
  set K' := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hv : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖v s‖ ≤ K' * N / γ ^ 2 := fun s hs =>
    (hfr s hs).2.2.2.2.2.1.trans (by gcongr; exact le_max_left _ _)
  have hv' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖v' s‖ ≤ K' * N ^ 2 / γ ^ 3 := fun s hs =>
    (hfr s hs).2.2.2.2.2.2.trans (by gcongr; exact le_max_left _ _)
  have hHerm : ∀ s ∈ Set.Icc (0 : ℝ) 1, (H s).IsHermitian := fun s hs => (hgap s hs).1
  -- the dynamical phase `E s = exp(i T Λ(s))`, `Λ(s) = ∫₀ˢ λ`
  set lamE : ℝ → ℝ := fun t => lam (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) with hlamE
  have hlamEc : Continuous lamE :=
    hlam.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun t => (Set.projIcc (0 : ℝ) 1 zero_le_one t).2)
  have hlamE_eq : ∀ s ∈ Set.Icc (0 : ℝ) 1, lamE s = lam s := fun s hs => by
    simp [hlamE, Set.projIcc_of_mem _ hs]
  set Λ : ℝ → ℝ := fun s => ∫ t in (0 : ℝ)..s, lamE t with hΛ
  have hΛd : ∀ s, HasDerivAt Λ (lamE s) s := fun s =>
    (hlamEc.integral_hasStrictDerivAt 0 s).hasDerivAt
  set E : ℝ → ℂ := fun s => Complex.exp ((T : ℂ) * (Λ s : ℂ) * Complex.I) with hE
  have hEd : ∀ s, HasDerivAt E (E s * ((T : ℂ) * (lamE s : ℂ) * Complex.I)) s := fun s =>
    (((hΛd s).ofReal_comp.const_mul (T : ℂ)).mul_const Complex.I).cexp
  have hE0 : E 0 = 1 := by simp [hE, hΛ]
  have hEn : ∀ s, ‖E s‖ = 1 := fun s => by
    have : (T : ℂ) * (Λ s : ℂ) * Complex.I = ((T * Λ s : ℝ) : ℂ) * Complex.I := by push_cast; ring
    simp only [hE, this, Complex.norm_exp_ofReal_mul_I]
  -- the error `e = ψ - E u` obeys `e' = i T H e - E u'`
  set e : ℝ → EuclideanSpace ℂ ι := fun s => ψ s - E s • u s with he
  have hed : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt e
      (Complex.I • (T : ℂ) • act (H s) (e s) + -(E s • u' s)) (Set.Icc 0 1) s := by
    intro s hs
    have := (hψ s hs).sub (((hEd s).hasDerivWithinAt).smul (hfr s hs).1)
    refine this.congr_deriv ?_
    simp only [he, red_act_sub, red_act_smul, (hfr s hs).2.2.2.1, hlamE_eq s hs]
    module
  have he0 : e 0 = 0 := by simp [he, hE0, hu0, hψ0]
  have he1 : ‖e 1‖ ≤ δ := by
    rcases hN0.eq_or_lt with hN0' | hNpos
    · -- `H_F = H_I` in norm: no transitions at all
      have hu' : ∀ s ∈ Set.Icc (0 : ℝ) 1, u' s = 0 := by
        intro s hs
        have hv0 : v s = 0 := by
          have := hv s hs
          rw [← hN0'] at this
          simpa using this
        rw [← (hfr s hs).2.2.2.2.1, hv0, red_act_zero, smul_zero, sub_zero]
      have := norm_le_of_schrodinger_source H hHerm T e (fun s => -(E s • u' s)) hed 0
        (fun s hs => by simp [hu' s hs])
      rw [he0, norm_zero, add_zero] at this
      exact this.trans hδ.le
    · -- integrate by parts once more: `f = e - (iT)⁻¹ E v`
      have hS : 0 < N / γ ^ 2 + N ^ 2 / γ ^ 3 := by positivity
      have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
      have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
      set κ : ℂ := (Complex.I * (T : ℂ))⁻¹ with hκ
      have hκn : ‖κ‖ = 1 / T := by
        simp [hκ, abs_of_pos hT0]
      set f : ℝ → EuclideanSpace ℂ ι := fun s => e s - κ • (E s • v s) with hf
      have hfd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f
          (Complex.I • (T : ℂ) • act (H s) (f s) + -(κ • (E s • v' s))) (Set.Icc 0 1) s := by
        intro s hs
        have := (hed s hs).sub ((((hEd s).hasDerivWithinAt).smul (hfr s hs).2.1).const_smul κ)
        refine this.congr_deriv ?_
        have hHv : act (H s) (v s) = u' s + (lam s : ℂ) • v s := by
          rw [← (hfr s hs).2.2.2.2.1]; abel
        simp only [hf, red_act_sub, red_act_smul, hHv, hlamE_eq s hs]
        rw [hκ]
        match_scalars <;> field_simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring
      have hfb := norm_le_of_schrodinger_source H hHerm T f (fun s => -(κ • (E s • v' s))) hfd
        (K' * N ^ 2 / γ ^ 3 / T) (fun s hs => by
          rw [norm_neg, norm_smul, norm_smul, hEn, hκn, one_mul, one_div, inv_mul_eq_div]
          gcongr
          exact hv' s hs)
      have hf0 : ‖f 0‖ = ‖v 0‖ / T := by
        simp [hf, he0, hE0, norm_smul, hκn, div_eq_inv_mul]
      have he1' : e 1 = f 1 + κ • (E 1 • v 1) := by simp [hf]
      have hb : ‖e 1‖ ≤ (2 * K' * N / γ ^ 2 + K' * N ^ 2 / γ ^ 3) / T := by
        rw [he1']
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, hEn, hκn, one_mul]
        have := hv 0 h0
        have := hv 1 h1
        rw [hf0] at hfb
        calc ‖f 1‖ + 1 / T * ‖v 1‖ ≤ ‖v 0‖ / T + K' * N ^ 2 / γ ^ 3 / T + ‖v 1‖ / T := by
              rw [one_div_mul_eq_div]; linarith
          _ = (‖v 0‖ + ‖v 1‖ + K' * N ^ 2 / γ ^ 3) / T := by ring
          _ ≤ (2 * K' * N / γ ^ 2 + K' * N ^ 2 / γ ^ 3) / T := by
              gcongr
              have : 2 * K' * N / γ ^ 2 = K' * N / γ ^ 2 + K' * N / γ ^ 2 := by ring
              linarith
      refine hb.trans ?_
      rw [div_le_iff₀ hT0]
      have hcS : (2 * K' + 1) * (N / γ ^ 2 + N ^ 2 / γ ^ 3) ≤ δ * T := by
        have := mul_le_mul_of_nonneg_left hT hδ.le
        rwa [← mul_assoc, mul_div_cancel₀ _ hδ.ne'] at this
      have ha : 0 ≤ N / γ ^ 2 := by positivity
      have hb' : 0 ≤ N ^ 2 / γ ^ 3 := by positivity
      have : 2 * K' * N / γ ^ 2 + K' * N ^ 2 / γ ^ 3 = 2 * K' * (N / γ ^ 2) + K' * (N ^ 2 / γ ^ 3) := by
        ring
      rw [this]
      nlinarith [hcS, mul_nonneg hK'0 hb', ha, hb']
  -- fix the phase using simplicity of `λ(1)`
  obtain ⟨ω, hω, hφ1⟩ := eigvec_eq_smul_of_hasGapAround (H 1) (lam 1) γ (hgap 1 h1) (u 1) (φ 1)
    (hfr 1 h1).2.2.1 (hφ 1 h1).1 (hfr 1 h1).2.2.2.1 (hφ 1 h1).2
  refine ⟨Complex.arg ω - T * Λ 1, ?_⟩
  have hωe : Complex.exp ((Complex.arg ω : ℂ) * Complex.I) = ω := by
    have := Complex.norm_mul_exp_arg_mul_I ω
    rwa [hω, Complex.ofReal_one, one_mul] at this
  have hψ1 : ψ 1 = e 1 + E 1 • u 1 := by simp [he]
  have hkey : Complex.exp (((Complex.arg ω - T * Λ 1 : ℝ) : ℂ) * Complex.I) • ψ 1 - φ 1 =
      (ω * Complex.exp (-((T : ℂ) * (Λ 1 : ℂ) * Complex.I))) • e 1 := by
    have hsplit : Complex.exp (((Complex.arg ω - T * Λ 1 : ℝ) : ℂ) * Complex.I) =
        ω * Complex.exp (-((T : ℂ) * (Λ 1 : ℂ) * Complex.I)) := by
      conv_rhs => rw [← hωe]
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hEE : Complex.exp (-((T : ℂ) * (Λ 1 : ℂ) * Complex.I)) * E 1 = 1 := by
      rw [hE, ← Complex.exp_add]; simp
    have hω1 : ω * Complex.exp (-((T : ℂ) * (Λ 1 : ℂ) * Complex.I)) * E 1 = ω := by
      rw [mul_assoc, hEE, mul_one]
    rw [hsplit, hψ1, hφ1, smul_add, smul_smul, hω1]
    abel
  rw [hkey, norm_smul, norm_mul, hω, one_mul]
  have : ‖Complex.exp (-((T : ℂ) * (Λ 1 : ℂ) * Complex.I))‖ = 1 := by
    have h' : -((T : ℂ) * (Λ 1 : ℂ) * Complex.I) = ((-(T * Λ 1) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h', Complex.norm_exp_ofReal_mul_I]
  rw [this, one_mul]
  exact he1
