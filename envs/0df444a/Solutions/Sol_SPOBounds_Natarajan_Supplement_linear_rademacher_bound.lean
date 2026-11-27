-- Prove2me | solution 1 for SPOBounds.Natarajan.Supplement.linear_rademacher_bound
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:06:45.147796+00:00
-- url     : https://prove2.me/submissions/f55c7b77-ae28-4d87-b3e2-98341a6f478d

import Mathlib
import Definitions.Def_SPOBounds_Margin_Model
import Definitions.Def_SPOBounds_Margin_Degeneracy
import Definitions.Def_SPOBounds_Margin_Rademacher
import Definitions.Def_SPOBounds_Natarajan_Supplement_LinearClass

open MeasureTheory SPOBounds.Margin

open SPOBounds
open SPOBounds.Natarajan
open SPOBounds.Natarajan.Supplement

/-- **Theorem 6** (arXiv:1905.11488v3, p. 21). Let `N` be a norm on `ℝ^{d×p}` and `N_*` its dual
norm under the trace pairing. Let `𝒮 ⊆ ℝ^{d×p}` be closed and convex, `F` `α`-strongly convex on
`𝒮` with respect to `N_*` (`α > 0`) with `inf_{B ∈ 𝒮} F(B) = 0`, `ℬ ⊆ {B ∈ 𝒮 : F(B) ≤ β²}`
(`β ≥ 0`), and `Ω` such that `N(σ xᵀ) ≤ Ω` for all `σ ∈ {±1}^d` and `x ∈ 𝒳 ⊆ ℝ^p`. For any
distribution `D` of (feature, cost) pairs whose feature lies in `𝒳` almost surely and any `n > 0`,
the expected multivariate Rademacher complexity of the linear class `𝓗_ℬ = {x ↦ Bx : B ∈ ℬ}`
satisfies `ℜⁿ(𝓗_ℬ) ≤ Ω β √(2 / (α n))`. -/
theorem solution {d p : ℕ}
    [MeasurableSpace (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))]
    [BorelSpace (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))]
    (N : Seminorm ℝ (Matrix (Fin d) (Fin p) ℝ)) (hN : IsMatrixNorm N)
    (𝒮 : Set (Matrix (Fin d) (Fin p) ℝ)) (h𝒮c : IsClosed 𝒮) (h𝒮v : Convex ℝ 𝒮)
    (F : Matrix (Fin d) (Fin p) ℝ → ℝ) (α : ℝ) (hα : 0 < α)
    (hF : StronglyConvexWrt (dualNorm N) 𝒮 α F) (hinf : IsGLB (F '' 𝒮) 0)
    (ℬ : Set (Matrix (Fin d) (Fin p) ℝ)) (β : ℝ) (hβ : 0 ≤ β)
    (hℬ : ℬ ⊆ {B | B ∈ 𝒮 ∧ F B ≤ β ^ 2})
    (𝒳 : Set (EuclideanSpace ℝ (Fin p))) (Ω : ℝ)
    (hΩ : ∀ σ : Fin d → Bool, ∀ x ∈ 𝒳, N (signOuter σ x) ≤ Ω)
    (D : Measure (EuclideanSpace ℝ (Fin p) × StrongDual ℝ (EuclideanSpace ℝ (Fin d))))
    [IsProbabilityMeasure D] (hD𝒳 : ∀ᵐ z ∂D, z.1 ∈ 𝒳)
    (n : ℕ) (hn : 0 < n) :
    expRademacherMulti D (linearClass ℬ) n ≤ Ω * β * Real.sqrt (2 / (α * n)) := by
      classical
      -- basic facts about the pairing
      have hlin : ∀ (B : Matrix (Fin d) (Fin p) ℝ) (x : EuclideanSpace ℝ (Fin p)) (b : Fin d → Bool),
          linPred B x (signVec b) = matInner B (signOuter b x) := by
        intro B x b
        simp [linPred, signVec, signOuter, matInner, PiLp.inner_apply, Matrix.mulVec, dotProduct,
          Finset.mul_sum]
      have hI_sum : ∀ (A : Matrix (Fin d) (Fin p) ℝ) (m : ℕ) (f : Fin m → Matrix (Fin d) (Fin p) ℝ),
          matInner A (∑ i, f i : Matrix (Fin d) (Fin p) ℝ) = ∑ i, matInner A (f i) := by
        intro A m f
        simp only [matInner, Matrix.sum_apply, Finset.mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Finset.sum_comm
      have hI_smul : ∀ (r : ℝ) (A B : Matrix (Fin d) (Fin p) ℝ),
          matInner A (r • B) = r * matInner A B := by
        intro r A B
        simp only [matInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      have hI_add : ∀ (A B C : Matrix (Fin d) (Fin p) ℝ),
          matInner A (B + C) = matInner A B + matInner A C := by
        intro A B C
        simp only [matInner, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
      have hI_subl : ∀ (A B C : Matrix (Fin d) (Fin p) ℝ),
          matInner (A - B) C = matInner A C - matInner B C := by
        intro A B C
        simp only [matInner, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
      have hI_symm : ∀ (A B : Matrix (Fin d) (Fin p) ℝ), matInner A B = matInner B A := by
        intro A B
        simp only [matInner, mul_comm]
      have hneg : ∀ (b : Fin d → Bool) (y : EuclideanSpace ℝ (Fin p)),
          signOuter (fun i => !b i) y = - signOuter b y := by
        intro b y
        ext i j; simp only [signOuter, Matrix.of_apply, Matrix.neg_apply]
        by_cases h : b i <;> simp [h]
      -- coercivity of N
      obtain ⟨c, hc, hcoer⟩ : ∃ c > 0, ∀ B : Fin d → Fin p → ℝ, ∀ i j, c * |B i j| ≤ N B := by
        have hfc : Continuous (fun B : Fin d → Fin p → ℝ => N B) := by
          have hcv : ConvexOn ℝ Set.univ (fun B : Fin d → Fin p → ℝ => N B) := N.convexOn
          have := hcv.continuousOn_interior
          rw [interior_univ] at this
          exact continuousOn_univ.mp this
        by_cases h : ∃ B : Fin d → Fin p → ℝ, B ≠ 0
        · obtain ⟨B1, hB1⟩ := h
          have : Nontrivial (Fin d → Fin p → ℝ) := nontrivial_of_ne B1 0 hB1
          have hne : (Metric.sphere (0 : Fin d → Fin p → ℝ) 1).Nonempty :=
            (NormedSpace.sphere_nonempty).mpr zero_le_one
          obtain ⟨B0, hB0S, hmin⟩ := (isCompact_sphere (0 : Fin d → Fin p → ℝ) 1).exists_isMinOn hne
            hfc.continuousOn
          have hB0n : ‖B0‖ = 1 := by simpa using hB0S
          have hc : 0 < N B0 := by
            rcases (apply_nonneg N B0).lt_or_eq with h1 | h1
            · exact h1
            · have := hN B0 h1.symm
              exfalso
              have : B0 = 0 := this
              rw [this, norm_zero] at hB0n
              exact zero_ne_one hB0n
          refine ⟨N B0, hc, fun B i j => ?_⟩
          by_cases hB : B = 0
          · subst hB; simp only [Pi.zero_apply, abs_zero, mul_zero]; exact apply_nonneg N _
          have hBpos : 0 < ‖B‖ := norm_pos_iff.mpr hB
          have hu : ‖B‖⁻¹ • B ∈ Metric.sphere (0 : Fin d → Fin p → ℝ) 1 := by
            simp [norm_smul, hBpos.ne']
          have h1 : N B0 ≤ N (‖B‖⁻¹ • B) := hmin hu
          have e : N (‖B‖⁻¹ • B) = ‖‖B‖⁻¹‖ * N B := map_smul_eq_mul N _ (B : Matrix (Fin d) (Fin p) ℝ)
          rw [e, Real.norm_eq_abs, abs_inv, abs_norm] at h1
          have h2 : |B i j| ≤ ‖B‖ := by
            have := (norm_le_pi_norm (B i) j).trans (norm_le_pi_norm B i)
            simpa [Real.norm_eq_abs] using this
          have h3 : N B0 * ‖B‖ ≤ N B := by
            rw [le_inv_mul_iff₀ hBpos] at h1; linarith
          nlinarith
        · push Not at h
          refine ⟨1, one_pos, fun B i j => ?_⟩
          rw [h B]; simp only [Pi.zero_apply, abs_zero, mul_zero]; exact apply_nonneg N _
      -- duality inequality
      have hbdd_dual : ∀ D : Matrix (Fin d) (Fin p) ℝ,
          BddAbove ((fun B => matInner B D) '' {B | N B ≤ 1}) := by
        intro D
        refine ⟨∑ i, ∑ j, |D i j| / c, ?_⟩
        rintro _ ⟨B, hB, rfl⟩
        have hB' : N B ≤ 1 := hB
        simp only [matInner]
        apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
        have h1 := hcoer B i j
        have h2 : |B i j| ≤ 1 / c := by rw [le_div_iff₀ hc]; linarith
        calc B i j * D i j ≤ |B i j| * |D i j| := by rw [← abs_mul]; exact le_abs_self _
          _ ≤ (1 / c) * |D i j| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
          _ = |D i j| / c := by ring
      have hdual : ∀ D θ : Matrix (Fin d) (Fin p) ℝ, matInner D θ ≤ dualNorm N D * N θ := by
        intro D θ
        by_cases hθ : N θ = 0
        · have h0 : θ = 0 := hN θ hθ
          subst h0
          simp [matInner]
        · have hpos : 0 < N θ := lt_of_le_of_ne (apply_nonneg N θ) (Ne.symm hθ)
          have hmem : (N θ)⁻¹ • θ ∈ {B | N B ≤ 1} := by
            show N ((N θ)⁻¹ • θ) ≤ 1
            rw [map_smul_eq_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hθ]
          have h1 : matInner ((N θ)⁻¹ • θ) D ≤ dualNorm N D := le_csSup (hbdd_dual D) ⟨_, hmem, rfl⟩
          rw [hI_symm, hI_smul, inv_mul_le_iff₀ hpos] at h1
          linarith [mul_comm (N θ) (dualNorm N D)]
      -- nonnegativity facts
      have hF0 : ∀ B ∈ 𝒮, 0 ≤ F B := fun B hB => hinf.1 ⟨B, hB, rfl⟩
      have hΩ0 : 0 ≤ Ω := by
        obtain ⟨z, hz⟩ := hD𝒳.exists
        exact (apply_nonneg N _).trans (hΩ (fun _ => true) z.1 hz)
      have hRHS0 : 0 ≤ Ω * β * Real.sqrt (2 / (α * n)) := by positivity
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      -- reduction of the integral to a pointwise bound
      have hae : ∀ᵐ s ∂(Measure.pi fun _ : Fin n => D), ∀ i, (s i).1 ∈ 𝒳 := by
        rw [ae_all_iff]; intro i
        exact (measurePreserving_eval (fun _ : Fin n => D) i).quasiMeasurePreserving.ae hD𝒳
      suffices hpt : ∀ x : Fin n → EuclideanSpace ℝ (Fin p), (∀ i, x i ∈ 𝒳) →
          empRademacherMulti (linearClass ℬ) x ≤ Ω * β * Real.sqrt (2 / (α * n)) by
        unfold expRademacherMulti
        by_cases hint : Integrable (fun s : Fin n → EuclideanSpace ℝ (Fin p) ×
            StrongDual ℝ (EuclideanSpace ℝ (Fin d)) => empRademacherMulti (linearClass ℬ)
              (fun i => (s i).1)) (Measure.pi fun _ : Fin n => D)
        · calc _ ≤ ∫ _s, Ω * β * Real.sqrt (2 / (α * n)) ∂(Measure.pi fun _ : Fin n => D) :=
                integral_mono_ae hint (integrable_const _) (hae.mono fun s hs => hpt _ hs)
            _ = _ := by simp
        · rw [integral_undef hint]; exact hRHS0
      intro x hx
      rcases ℬ.eq_empty_or_nonempty with hE | ⟨B0, hB0⟩
      · have hempty : IsEmpty (linearClass ℬ) := by
          constructor; rintro ⟨f, B, hB, -⟩; rw [hE] at hB; exact hB
        have : ∀ σ : Fin n → Fin d → Bool, multiSignedSup (linearClass ℬ) x σ = 0 := by
          intro σ; unfold multiSignedSup; exact Real.iSup_of_isEmpty _
        unfold empRademacherMulti
        simp only [this, Finset.sum_const_zero, mul_zero]
        exact hRHS0
      set ℬ' : Set (Matrix (Fin d) (Fin p) ℝ) := {B | B ∈ 𝒮 ∧ F B ≤ β ^ 2} with hℬ'def
      have hB0' : B0 ∈ ℬ' := hℬ hB0
      have hsc : ∀ B1 ∈ ℬ', ∀ B2 ∈ ℬ',
          F ((1 / 2 : ℝ) • B1 + (1 - 1 / 2 : ℝ) • B2) ≤ 1 / 2 * F B1 + (1 - 1 / 2) * F B2
            - α / 2 * (1 / 2) * (1 - 1 / 2) * dualNorm N (B1 - B2) ^ 2 :=
        fun B1 h1 B2 h2 => hF B1 h1.1 B2 h2.1 (1 / 2) (by norm_num) (by norm_num)
      have hmid𝒮 : ∀ B1 ∈ ℬ', ∀ B2 ∈ ℬ', (1 / 2 : ℝ) • B1 + (1 - 1 / 2 : ℝ) • B2 ∈ 𝒮 :=
        fun B1 h1 B2 h2 => h𝒮v h1.1 h2.1 (by norm_num) (by norm_num) (by norm_num)
      have hmid : ∀ B1 ∈ ℬ', ∀ B2 ∈ ℬ', (1 / 2 : ℝ) • B1 + (1 - 1 / 2 : ℝ) • B2 ∈ ℬ' := by
        intro B1 h1 B2 h2
        refine ⟨hmid𝒮 B1 h1 B2 h2, ?_⟩
        have := hsc B1 h1 B2 h2
        have := h1.2; have := h2.2
        nlinarith [sq_nonneg (dualNorm N (B1 - B2))]
      have hsq : ∀ B1 ∈ ℬ', ∀ B2 ∈ ℬ', dualNorm N (B1 - B2) ^ 2 ≤ 8 * β ^ 2 / α := by
        intro B1 h1 B2 h2
        have := hsc B1 h1 B2 h2
        have := hF0 _ (hmid𝒮 B1 h1 B2 h2)
        have := h1.2; have := h2.2
        rw [le_div_iff₀ hα]; nlinarith
      have hne' : Nonempty ℬ' := ⟨⟨B0, hB0'⟩⟩
      set Φ : Matrix (Fin d) (Fin p) ℝ → ℝ :=
        fun A => ⨆ B : ℬ', (matInner (B : Matrix (Fin d) (Fin p) ℝ) A - F B) with hΦdef
      have hΦbdd : ∀ A, BddAbove (Set.range fun B : ℬ' =>
          matInner (B : Matrix (Fin d) (Fin p) ℝ) A - F B) := by
        intro A
        refine ⟨matInner B0 A + (8 * β ^ 2 / α + N A ^ 2) / 2, ?_⟩
        rintro _ ⟨⟨B, hB⟩, rfl⟩
        have e : matInner B A = matInner B0 A + matInner (B - B0) A := by rw [hI_subl]; ring
        have h1 := hdual (B - B0) A
        have h2 := hsq B hB B0 hB0'
        have h3 := hF0 B hB.1
        show matInner B A - F B ≤ _
        nlinarith [sq_nonneg (dualNorm N (B - B0) - N A)]
      have hΦle : ∀ A, ∀ B ∈ ℬ', matInner B A - F B ≤ Φ A := fun A B hB =>
        le_ciSup (f := fun B : ℬ' => matInner (B : Matrix (Fin d) (Fin p) ℝ) A - F B) (hΦbdd A) ⟨B, hB⟩
      have hΦ0 : Φ 0 ≤ 0 := by
        apply ciSup_le; rintro ⟨B, hB⟩
        have := hF0 B hB.1
        simp only [matInner, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]; linarith
      have hpair : ∀ A θ : Matrix (Fin d) (Fin p) ℝ,
          Φ (A + θ) + Φ (A - θ) ≤ 2 * Φ A + N θ ^ 2 / α := by
        intro A θ
        apply ciSup_add_ciSup_le
        rintro ⟨B1, h1⟩ ⟨B2, h2⟩
        show matInner B1 (A + θ) - F B1 + (matInner B2 (A - θ) - F B2) ≤ _
        have hsc' := hsc B1 h1 B2 h2
        have hΦM := hΦle A _ (hmid B1 h1 B2 h2)
        have eM : matInner ((1 / 2 : ℝ) • B1 + (1 - 1 / 2 : ℝ) • B2) A
            = 1 / 2 * matInner B1 A + (1 - 1 / 2) * matInner B2 A := by
          rw [hI_symm, hI_add, hI_smul, hI_smul, hI_symm A B1, hI_symm A B2]
        have e1 : matInner B1 (A + θ) = matInner B1 A + matInner B1 θ := hI_add _ _ _
        have e2 : matInner B2 (A - θ) = matInner B2 A - matInner B2 θ := by
          rw [sub_eq_add_neg, hI_add, ← neg_one_smul ℝ θ, hI_smul]; ring
        have e3 := hI_subl B1 B2 θ
        have hd := hdual (B1 - B2) θ
        have key : dualNorm N (B1 - B2) * N θ - α / 4 * dualNorm N (B1 - B2) ^ 2 ≤ N θ ^ 2 / α := by
          rw [le_div_iff₀ hα]; nlinarith [sq_nonneg (α / 2 * dualNorm N (B1 - B2) - N θ)]
        rw [eM] at hΦM
        nlinarith
      have havg : ∀ lam : ℝ, 0 < lam → ∀ A, ∀ y ∈ 𝒳,
          (1 / 2 ^ d : ℝ) * ∑ b : Fin d → Bool, Φ (A + lam • signOuter b y)
            ≤ Φ A + lam ^ 2 * Ω ^ 2 / (2 * α) := by
        intro lam hlam A y hy
        have hsum_eq : ∑ b : Fin d → Bool, Φ (A + lam • signOuter b y)
            = ∑ b : Fin d → Bool, Φ (A - lam • signOuter b y) := by
          refine Fintype.sum_equiv (Equiv.mk (fun b i => !b i) (fun b i => !b i)
            (fun b => by simp) (fun b => by simp)) _ _ ?_
          intro b
          show Φ (A + lam • signOuter b y) = Φ (A - lam • signOuter (fun i => !b i) y)
          rw [hneg, smul_neg, sub_neg_eq_add]
        have hterm : ∀ b : Fin d → Bool, Φ (A + lam • signOuter b y) + Φ (A - lam • signOuter b y)
            ≤ 2 * Φ A + lam ^ 2 * Ω ^ 2 / α := by
          intro b
          have h1 := hpair A (lam • signOuter b y)
          have hn : N (lam • signOuter b y) ≤ lam * Ω := by
            rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hlam]
            exact mul_le_mul_of_nonneg_left (hΩ b y hy) hlam.le
          have hn0 := apply_nonneg N (lam • signOuter b y)
          have h2 : N (lam • signOuter b y) ^ 2 / α ≤ lam ^ 2 * Ω ^ 2 / α := by
            apply div_le_div_of_nonneg_right _ hα.le; nlinarith
          linarith
        have hS := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin d → Bool))) => hterm b)
        rw [Finset.sum_add_distrib, ← hsum_eq, Finset.sum_const, Finset.card_univ] at hS
        simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul] at hS
        push_cast at hS
        have h2d : (0 : ℝ) < 2 ^ d := by positivity
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ h2d]
        have e : lam ^ 2 * Ω ^ 2 / (2 * α) = lam ^ 2 * Ω ^ 2 / α / 2 := by field_simp
        rw [e]
        linarith
      have hind : ∀ lam : ℝ, 0 < lam → ∀ m : ℕ, ∀ y : Fin m → EuclideanSpace ℝ (Fin p),
          (∀ i, y i ∈ 𝒳) → ∀ A,
          (1 / 2 ^ (m * d) : ℝ) * ∑ σ : Fin m → Fin d → Bool,
              Φ (A + lam • ∑ i, signOuter (σ i) (y i))
            ≤ Φ A + m * (lam ^ 2 * Ω ^ 2 / (2 * α)) := by
        intro lam hlam m
        induction m with
        | zero => intro y hy A; simp
        | succ m ih =>
          intro y hy A
          rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin d → Bool)).sum_comp, Fintype.sum_prod_type]
          have step : ∀ b : Fin d → Bool, (1 / 2 ^ (m * d) : ℝ) * ∑ τ : Fin m → Fin d → Bool,
              Φ (A + lam • ∑ i, signOuter
                ((Fin.consEquiv (fun _ : Fin (m + 1) => Fin d → Bool)) (b, τ) i) (y i))
              ≤ Φ (A + lam • signOuter b (y 0)) + m * (lam ^ 2 * Ω ^ 2 / (2 * α)) := by
            intro b
            have := ih (fun i => y i.succ) (fun i => hy _) (A + lam • signOuter b (y 0))
            simpa only [Fin.sum_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ,
              smul_add, add_assoc] using this
          have h2 := havg lam hlam A (y 0) (hy 0)
          have hsplit : (1 / 2 ^ ((m + 1) * d) : ℝ) = (1 / 2 ^ d) * (1 / 2 ^ (m * d)) := by
            rw [add_mul, one_mul, pow_add]; field_simp
          rw [hsplit, mul_assoc, Finset.mul_sum]
          calc (1 / 2 ^ d : ℝ) * ∑ b : Fin d → Bool, (1 / 2 ^ (m * d) : ℝ) * ∑ τ : Fin m → Fin d → Bool,
                Φ (A + lam • ∑ i, signOuter
                  ((Fin.consEquiv (fun _ : Fin (m + 1) => Fin d → Bool)) (b, τ) i) (y i))
              ≤ (1 / 2 ^ d : ℝ) * ∑ b : Fin d → Bool,
                  (Φ (A + lam • signOuter b (y 0)) + m * (lam ^ 2 * Ω ^ 2 / (2 * α))) := by
                gcongr with b; exact step b
            _ = (1 / 2 ^ d : ℝ) * ∑ b : Fin d → Bool, Φ (A + lam • signOuter b (y 0))
                  + m * (lam ^ 2 * Ω ^ 2 / (2 * α)) := by
                rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
                simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
                push_cast
                field_simp
            _ ≤ Φ A + (↑(m + 1) : ℝ) * (lam ^ 2 * Ω ^ 2 / (2 * α)) := by
                push_cast; linarith
      have hne_H : Nonempty (linearClass ℬ) := ⟨⟨linPred B0, B0, hB0, rfl⟩⟩
      have hR : ∀ lam : ℝ, 0 < lam →
          empRademacherMulti (linearClass ℬ) x ≤ β ^ 2 / (lam * n) + lam * Ω ^ 2 / (2 * α) := by
        intro lam hlam
        have hσ : ∀ σ : Fin n → Fin d → Bool, multiSignedSup (linearClass ℬ) x σ
            ≤ (Φ (0 + lam • ∑ i, signOuter (σ i) (x i)) + β ^ 2) / (lam * n) := by
          intro σ
          unfold multiSignedSup
          apply ciSup_le
          rintro ⟨f, B, hB, rfl⟩
          show (1 / n : ℝ) * ∑ i, linPred B (x i) (signVec (σ i)) ≤ _
          simp only [hlin]
          rw [← hI_sum]
          have h1 := hΦle (0 + lam • ∑ i, signOuter (σ i) (x i)) B (hℬ hB)
          rw [zero_add, hI_smul] at h1
          rw [zero_add]
          have h2 := (hℬ hB).2
          rw [le_div_iff₀ (by positivity)]
          have e : (1 / n : ℝ) * matInner B (∑ i, signOuter (σ i) (x i)) * (lam * n)
              = lam * matInner B (∑ i, signOuter (σ i) (x i)) := by field_simp
          rw [e]; linarith
        have hI := hind lam hlam n x hx 0
        unfold empRademacherMulti
        have h2nd : (0 : ℝ) < 2 ^ (n * d) := by positivity
        calc (1 / 2 ^ (n * d) : ℝ) * ∑ σ : Fin n → Fin d → Bool, multiSignedSup (linearClass ℬ) x σ
            ≤ (1 / 2 ^ (n * d) : ℝ) * ∑ σ : Fin n → Fin d → Bool,
                (Φ (0 + lam • ∑ i, signOuter (σ i) (x i)) + β ^ 2) / (lam * n) := by
              gcongr with σ; exact hσ σ
          _ = ((1 / 2 ^ (n * d) : ℝ) * ∑ σ : Fin n → Fin d → Bool,
                Φ (0 + lam • ∑ i, signOuter (σ i) (x i)) + β ^ 2) / (lam * n) := by
              rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
              simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
              push_cast
              rw [← pow_mul]
              field_simp
              ring
          _ ≤ (Φ 0 + n * (lam ^ 2 * Ω ^ 2 / (2 * α)) + β ^ 2) / (lam * n) := by
              gcongr
          _ ≤ (n * (lam ^ 2 * Ω ^ 2 / (2 * α)) + β ^ 2) / (lam * n) := by
              gcongr; linarith
          _ = β ^ 2 / (lam * n) + lam * Ω ^ 2 / (2 * α) := by
              field_simp
              ring
      set R := empRademacherMulti (linearClass ℬ) x with hRdef
      set s := Real.sqrt (2 / (α * n)) with hsdef
      have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
      have hs2 : s ^ 2 = 2 / (α * n) := Real.sq_sqrt (by positivity)
      have hns : α * n * s ^ 2 = 2 := by rw [hs2]; field_simp
      have key : ∀ ε : ℝ, 0 < ε → R ≤ Ω * β * s + ε * (s * (β + Ω) / 2) := by
        intro ε hε
        have hlam : 0 < (β + ε) * α * s / (Ω + ε) := by positivity
        have h := hR _ hlam
        have t1 : β ^ 2 / ((β + ε) * α * s / (Ω + ε) * n) ≤ β * (Ω + ε) * s / 2 := by
          rw [div_le_iff₀ (by positivity)]
          have e : β * (Ω + ε) * s / 2 * ((β + ε) * α * s / (Ω + ε) * n)
              = β * (β + ε) * (α * n * s ^ 2) / 2 := by field_simp
          rw [e, hns]; nlinarith
        have t2 : (β + ε) * α * s / (Ω + ε) * Ω ^ 2 / (2 * α) ≤ (β + ε) * Ω * s / 2 := by
          have e : (β + ε) * α * s / (Ω + ε) * Ω ^ 2 / (2 * α)
              = (β + ε) * s * (Ω ^ 2 / (Ω + ε)) / 2 := by field_simp
          rw [e]
          have h3 : Ω ^ 2 / (Ω + ε) ≤ Ω := by rw [div_le_iff₀ (by positivity)]; nlinarith
          have h4 : 0 ≤ (β + ε) * s := by positivity
          nlinarith
        nlinarith
      by_contra hcon
      push Not at hcon
      have hK : 0 ≤ s * (β + Ω) / 2 := by positivity
      have hεpos : 0 < (R - Ω * β * s) / (s * (β + Ω) / 2 + 1) := div_pos (by linarith) (by linarith)
      have h1 := key _ hεpos
      have h2 : (R - Ω * β * s) / (s * (β + Ω) / 2 + 1) * (s * (β + Ω) / 2 + 1) = R - Ω * β * s :=
        div_mul_cancel₀ _ (by linarith)
      nlinarith
