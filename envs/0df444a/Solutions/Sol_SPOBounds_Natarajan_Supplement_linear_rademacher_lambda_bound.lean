-- Prove2me | solution 1 for SPOBounds.Natarajan.Supplement.linear_rademacher_lambda_bound
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:06:19.518819+00:00
-- url     : https://prove2.me/submissions/9efe7eb7-afc0-4d97-8996-a531de47927f

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Supplement_LinearClass

open SPOBounds
open SPOBounds.Natarajan
open SPOBounds.Natarajan.Supplement

/-- **Proof of Theorem 6, bound for arbitrary `λ > 0`** (arXiv:1905.11488v3, Appendix C.2,
p. 34). Let `N` be a norm on `ℝ^{d×p}` and `N_*` its dual norm under the trace pairing
`⟨B, A⟩ = ∑ B_{ij} A_{ij}`. Let `𝒮` be closed and convex, `F` `α`-strongly convex on `𝒮` with
respect to `N_*` (`α > 0`) with `inf_{B ∈ 𝒮} F(B) = 0`, and `ℬ ⊆ {B ∈ 𝒮 : F(B) ≤ β²}`. Fix
features `x₁, …, xₙ` (`n > 0`) with `N(σ xᵢᵀ) ≤ Ω` for every `i` and every `σ ∈ {±1}^d`. Then for
every `λ > 0`, with `Θ = (1/n) ∑ᵢ σᵢ xᵢᵀ` for uniform signs `σ ∈ {±1}^{n×d}`,
`E_σ[sup_{B ∈ ℬ} ⟨B, Θ⟩] ≤ β²/λ + λ Ω² / (2 α n)`; the expectation is the average over all
`2^{nd}` sign matrices. -/
theorem solution {d p n : ℕ}
    (N : Seminorm ℝ (Matrix (Fin d) (Fin p) ℝ)) (hN : IsMatrixNorm N)
    (𝒮 : Set (Matrix (Fin d) (Fin p) ℝ)) (h𝒮c : IsClosed 𝒮) (h𝒮v : Convex ℝ 𝒮)
    (F : Matrix (Fin d) (Fin p) ℝ → ℝ) (α : ℝ) (hα : 0 < α)
    (hF : StronglyConvexWrt (dualNorm N) 𝒮 α F) (hinf : IsGLB (F '' 𝒮) 0)
    (ℬ : Set (Matrix (Fin d) (Fin p) ℝ)) (β : ℝ) (hℬ : ℬ ⊆ {B | B ∈ 𝒮 ∧ F B ≤ β ^ 2})
    (Ω : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin p))
    (hx : ∀ i, ∀ σ : Fin d → Bool, N (signOuter σ (x i)) ≤ Ω)
    (hn : 0 < n) (lam : ℝ) (hlam : 0 < lam) :
    (1 / 2 ^ (n * d) : ℝ) * ∑ σ : Fin n → Fin d → Bool,
        (⨆ B : ℬ, matInner (B : Matrix (Fin d) (Fin p) ℝ)
          ((1 / n : ℝ) • ∑ i, signOuter (σ i) (x i))) ≤
      β ^ 2 / lam + lam * Ω ^ 2 / (2 * α * n) := by
        classical
        have hbdd : ∀ D : Matrix (Fin d) (Fin p) ℝ,
            BddAbove ((fun B => matInner B D) '' {B | N B ≤ 1}) := by
          classical
          have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin d) (Fin p) ℝ),
              N (∑ i ∈ s, f i) ≤ ∑ i ∈ s, N (f i) := fun s f =>
            Finset.le_sum_of_subadditive N (map_zero N).le (map_add_le_add N) s f
          let g : (Fin d → Fin p → ℝ) → ℝ := fun C => N (Matrix.of C)
          let L : ℝ := ∑ i, ∑ j, N (Matrix.single i j (1:ℝ))
          have hup : ∀ C : Fin d → Fin p → ℝ, g C ≤ L * ‖C‖ := by
            intro C
            have hC : Matrix.of C = ∑ i, ∑ j, (C i j) • Matrix.single i j (1:ℝ) := by
              conv_lhs => rw [Matrix.matrix_eq_sum_single (Matrix.of C)]
              simp [Matrix.smul_single]
            calc g C = N (∑ i, ∑ j, (C i j) • Matrix.single i j (1:ℝ)) := by simp only [g]; rw [← hC]
              _ ≤ ∑ i, N (∑ j, (C i j) • Matrix.single i j (1:ℝ)) := hsum _ _
              _ ≤ ∑ i, ∑ j, N ((C i j) • Matrix.single i j (1:ℝ)) :=
                  Finset.sum_le_sum fun i _ => hsum _ _
              _ = ∑ i, ∑ j, ‖C i j‖ * N (Matrix.single i j (1:ℝ)) := by
                  simp only [map_smul_eq_mul]
              _ ≤ ∑ i, ∑ j, ‖C‖ * N (Matrix.single i j (1:ℝ)) := by
                  gcongr with i _ j _
                  exact (norm_le_pi_norm (C i) j).trans (norm_le_pi_norm C i)
              _ = L * ‖C‖ := by simp only [L, ← Finset.mul_sum]; ring
          have gsmul : ∀ (c : ℝ) C, g (c • C) = |c| * g C := by
            intro c C
            simp only [g]
            rw [show Matrix.of (c • C) = c • Matrix.of C from rfl, map_smul_eq_mul, Real.norm_eq_abs]
          have hcont : Continuous g := by
            apply LipschitzWith.continuous (K := L.toNNReal)
            apply LipschitzWith.of_dist_le_mul
            intro C C'
            rw [Real.dist_eq, dist_eq_norm]
            have h1 : |g C - g C'| ≤ g (C - C') := abs_sub_map_le_sub N (Matrix.of C) (Matrix.of C')
            have h2 := hup (C - C')
            rw [Real.coe_toNNReal']
            calc |g C - g C'| ≤ g (C - C') := h1
              _ ≤ L * ‖C - C'‖ := h2
              _ ≤ max L 0 * ‖C - C'‖ := by gcongr; exact le_max_left _ _
          have g0 : g 0 = 0 := map_zero N
          have hlow : ∃ m > 0, ∀ C : Fin d → Fin p → ℝ, m * ‖C‖ ≤ g C := by
            by_cases hS : (Metric.sphere (0 : Fin d → Fin p → ℝ) 1).Nonempty
            · obtain ⟨C0, hC0, hmin⟩ := (isCompact_sphere (0 : Fin d → Fin p → ℝ) 1).exists_isMinOn hS
                hcont.continuousOn
              have hC0n : ‖C0‖ = 1 := by simpa using hC0
              have hC0ne : C0 ≠ 0 := by intro h; rw [h] at hC0n; simp at hC0n
              refine ⟨g C0, ?_, ?_⟩
              · rcases (apply_nonneg N (Matrix.of C0)).lt_or_eq with h | h
                · exact h
                · exact absurd (hN _ h.symm) hC0ne
              · intro C
                by_cases hC : C = 0
                · subst hC; rw [g0]; simp
                · have hpos : 0 < ‖C‖ := norm_pos_iff.mpr hC
                  have hmem : ‖C‖⁻¹ • C ∈ Metric.sphere (0 : Fin d → Fin p → ℝ) 1 := by
                    simp [norm_smul, hpos.ne']
                  have := hmin hmem
                  simp only [Set.mem_setOf_eq] at this
                  rw [gsmul, abs_of_pos (inv_pos.mpr hpos)] at this
                  have := mul_le_mul_of_nonneg_left this hpos.le
                  rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_comm] at this
            · refine ⟨1, one_pos, fun C => ?_⟩
              by_cases hC : C = 0
              · subst hC; rw [g0]; simp
              · exfalso; apply hS
                refine ⟨‖C‖⁻¹ • C, ?_⟩
                have hpos : 0 < ‖C‖ := norm_pos_iff.mpr hC
                simp [norm_smul, hpos.ne']
          obtain ⟨m, hm, hmC⟩ := hlow
          intro D
          refine ⟨∑ i, ∑ j, m⁻¹ * |D i j|, ?_⟩
          rintro _ ⟨C, hC, rfl⟩
          simp only [Set.mem_setOf_eq] at hC
          let C' : Fin d → Fin p → ℝ := Matrix.of.symm C
          have hgC : g C' ≤ 1 := hC
          have hCn : ‖C'‖ ≤ m⁻¹ := by
            calc ‖C'‖ = m⁻¹ * (m * ‖C'‖) := by field_simp
              _ ≤ m⁻¹ * 1 := by gcongr; exact (hmC C').trans hgC
              _ = m⁻¹ := mul_one _
          show ∑ i, ∑ j, C i j * D i j ≤ _
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          calc C i j * D i j ≤ |C i j * D i j| := le_abs_self _
            _ = |C i j| * |D i j| := abs_mul _ _
            _ ≤ m⁻¹ * |D i j| := by
              gcongr
              exact ((norm_le_pi_norm (C' i) j).trans (norm_le_pi_norm C' i)).trans hCn
        have hdual : ∀ D Z : Matrix (Fin d) (Fin p) ℝ, matInner D Z ≤ dualNorm N D * N Z := by
          intro D Z
          by_cases hZ : N Z = 0
          · have := hN Z hZ; subst this; simp [matInner]
          · have hpos : 0 < N Z := lt_of_le_of_ne (apply_nonneg N Z) (Ne.symm hZ)
            have hmem : matInner ((N Z)⁻¹ • Z) D ≤ dualNorm N D := by
              apply le_csSup (hbdd D)
              refine ⟨(N Z)⁻¹ • Z, ?_, rfl⟩
              show N ((N Z)⁻¹ • Z) ≤ 1
              rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
            have e : matInner ((N Z)⁻¹ • Z) D = (N Z)⁻¹ * matInner D Z := by
              simp only [matInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              ring
            rw [e] at hmem
            have := mul_le_mul_of_nonneg_left hmem hpos.le
            rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_comm] at this
        have hpair : ∀ A ∈ 𝒮, ∀ B ∈ 𝒮, ∀ Y Z : Matrix (Fin d) (Fin p) ℝ, ∀ K : ℝ, N Z ≤ K →
            (matInner A (Z + Y) - F A) + (matInner B (-Z + Y) - F B) ≤
              2 * (matInner ((1/2:ℝ) • A + (1 - 1/2:ℝ) • B) Y
                - F ((1/2:ℝ) • A + (1 - 1/2:ℝ) • B)) + K ^ 2 / α := by
          intro A hA B hB Y Z K hK
          have h1 := hF A hA B hB (1/2) (by norm_num) (by norm_num)
          have h2 := hdual (A - B) Z
          have h3 : matInner A (Z + Y) + matInner B (-Z + Y) = matInner (A - B) Z
              + 2 * matInner ((1/2:ℝ) • A + (1 - 1/2:ℝ) • B) Y := by
            simp only [matInner, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
              Matrix.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            ring
          have hNZ := apply_nonneg N Z
          set u := dualNorm N (A - B)
          have h4 : K ^ 2 / α ≥ N Z ^ 2 / α := by
            apply div_le_div_of_nonneg_right _ hα.le
            nlinarith
          have h5 : α / 4 * u ^ 2 + N Z ^ 2 / α - u * N Z = (α * u / 2 - N Z) ^ 2 / α := by
            field_simp; ring
          have h6 : 0 ≤ (α * u / 2 - N Z) ^ 2 / α := by positivity
          nlinarith
        let negB : (Fin d → Bool) ≃ (Fin d → Bool) :=
          ⟨fun b j => !b j, fun b j => !b j, fun b => by funext j; simp, fun b => by funext j; simp⟩
        have claim : ∀ m : ℕ, ∀ (w : Fin m → (Fin d → Bool) → Matrix (Fin d) (Fin p) ℝ) (K : ℝ),
            (∀ i b, w i (negB b) = - w i b) → (∀ i b, N (w i b) ≤ K) →
            ∀ G : (Fin m → Fin d → Bool) → Matrix (Fin d) (Fin p) ℝ, (∀ σ, G σ ∈ 𝒮) →
            ∑ σ, (matInner (G σ) (∑ i, w i (σ i)) - F (G σ)) ≤
              2 ^ (m * d) * (m * K ^ 2 / (2 * α)) := by
          intro m
          induction m with
          | zero =>
            intro w K _ _ G hG
            have h0 : ∀ σ : Fin 0 → Fin d → Bool, 0 ≤ F (G σ) := fun σ => hinf.1 ⟨G σ, hG σ, rfl⟩
            simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, zero_mul, pow_zero,
              zero_div, mul_zero]
            apply Finset.sum_nonpos
            intro σ _
            have : matInner (G σ) 0 = 0 := by simp [matInner]
            rw [this]; linarith [h0 σ]
          | succ m ih =>
            intro w K hw hK G hG
            let f : (Fin (m+1) → Fin d → Bool) → ℝ :=
              fun σ => matInner (G σ) (∑ i, w i (σ i)) - F (G σ)
            have hsplit : ∑ σ, f σ = ∑ b, ∑ τ, f (Fin.cons b τ) := by
              rw [← Fintype.sum_prod_type']
              exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin d → Bool) _ _ (fun _ => rfl)).symm
            have hneg : ∀ g : (Fin d → Bool) → ℝ, ∑ b, g b = ∑ b, g (negB b) := fun g =>
              (Fintype.sum_equiv negB _ _ (fun _ => rfl)).symm
            let Y : (Fin m → Fin d → Bool) → Matrix (Fin d) (Fin p) ℝ := fun τ => ∑ i, w i.succ (τ i)
            let M : (Fin d → Bool) → (Fin m → Fin d → Bool) → Matrix (Fin d) (Fin p) ℝ := fun b τ =>
              (1/2:ℝ) • G (Fin.cons b τ) + (1 - 1/2:ℝ) • G (Fin.cons (negB b) τ)
            have hM : ∀ b τ, M b τ ∈ 𝒮 := fun b τ =>
              h𝒮v (hG _) (hG _) (by norm_num) (by norm_num) (by norm_num)
            have hstep : ∀ b τ, f (Fin.cons b τ) + f (Fin.cons (negB b) τ) ≤
                2 * (matInner (M b τ) (Y τ) - F (M b τ)) + K ^ 2 / α := by
              intro b τ
              have := hpair _ (hG (Fin.cons b τ)) _ (hG (Fin.cons (negB b) τ)) (Y τ) (w 0 b) K (hK 0 b)
              simp only [f, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hw]
              exact this
            have hIH : ∀ b, ∑ τ, (matInner (M b τ) (Y τ) - F (M b τ)) ≤
                2 ^ (m * d) * (m * K ^ 2 / (2 * α)) := fun b =>
              ih (fun i => w i.succ) K (fun i b => hw _ _) (fun i b => hK _ _) (M b) (hM b)
            have hcard : (∑ _b : Fin d → Bool, (1:ℝ)) = 2 ^ d := by
              simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
            have h2 : 2 * ∑ σ, f σ ≤ 2 ^ d * (2 * (2 ^ (m * d) * (m * K ^ 2 / (2 * α)))
                + 2 ^ (m * d) * (K ^ 2 / α)) := by
              rw [hsplit, two_mul]
              conv_lhs => arg 2; rw [hneg (fun b => ∑ τ, f (Fin.cons b τ))]
              rw [← Finset.sum_add_distrib]
              calc ∑ b, (∑ τ, f (Fin.cons b τ) + ∑ τ, f (Fin.cons (negB b) τ))
                  ≤ ∑ b : Fin d → Bool, (2 * (2 ^ (m * d) * (m * K ^ 2 / (2 * α)))
                    + 2 ^ (m * d) * (K ^ 2 / α)) := by
                    refine Finset.sum_le_sum fun b _ => ?_
                    rw [← Finset.sum_add_distrib]
                    calc ∑ τ, (f (Fin.cons b τ) + f (Fin.cons (negB b) τ))
                        ≤ ∑ τ, (2 * (matInner (M b τ) (Y τ) - F (M b τ)) + K ^ 2 / α) :=
                          Finset.sum_le_sum fun τ _ => hstep b τ
                      _ = 2 * ∑ τ, (matInner (M b τ) (Y τ) - F (M b τ)) + 2 ^ (m * d) * (K ^ 2 / α) := by
                          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
                            Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
                            Fintype.card_fin, nsmul_eq_mul]
                          push_cast; ring
                      _ ≤ _ := by linarith [hIH b]
                _ = _ := by
                    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
                      Fintype.card_fin, nsmul_eq_mul]
                    push_cast; ring
            have e : (2:ℝ) ^ ((m + 1) * d) = 2 ^ (m * d) * 2 ^ d := by rw [add_mul, one_mul, pow_add]
            rw [e]
            push_cast
            have hα' : α ≠ 0 := hα.ne'
            have key : 2 ^ d * (2 * (2 ^ (m * d) * (m * K ^ 2 / (2 * α))) + 2 ^ (m * d) * (K ^ 2 / α))
                = 2 * (2 ^ (m * d) * 2 ^ d * ((m + 1) * K ^ 2 / (2 * α))) := by
              field_simp
            linarith
        have mi_smul : ∀ (B A : Matrix (Fin d) (Fin p) ℝ) (c : ℝ), matInner B (c • A) = c * matInner B A := by
          intro B A c
          simp only [matInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
        have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr hn
        have h2pos : (0:ℝ) < 2 ^ (n * d) := by positivity
        rcases isEmpty_or_nonempty ℬ with hE | hE
        · have : ∀ σ : Fin n → Fin d → Bool, (⨆ B : ℬ, matInner (B : Matrix (Fin d) (Fin p) ℝ)
                ((1 / n : ℝ) • ∑ i, signOuter (σ i) (x i))) = 0 := fun σ => Real.iSup_of_isEmpty _
          simp only [this, Finset.sum_const_zero, mul_zero]
          positivity
        set Θ : (Fin n → Fin d → Bool) → Matrix (Fin d) (Fin p) ℝ :=
          fun σ => (1 / n : ℝ) • ∑ i, signOuter (σ i) (x i) with hΘdef
        let w : Fin n → (Fin d → Bool) → Matrix (Fin d) (Fin p) ℝ := fun i b => (lam / n) • signOuter b (x i)
        let K := lam / n * Ω
        have hw : ∀ i b, w i (negB b) = - w i b := by
          intro i b
          simp only [w]
          rw [← smul_neg]
          congr 1
          ext k l
          simp only [signOuter, negB, Equiv.coe_fn_mk, Matrix.of_apply, Matrix.neg_apply]
          rcases Bool.eq_false_or_eq_true (b k) with h | h <;> simp [h]
        have hK : ∀ i b, N (w i b) ≤ K := by
          intro i b
          simp only [w, K]
          rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (by positivity)]
          exact mul_le_mul_of_nonneg_left (hx i b) (by positivity)
        have hΘ : ∀ σ : Fin n → Fin d → Bool, ∑ i, w i (σ i) = lam • Θ σ := by
          intro σ
          simp only [w, Θ]
          rw [Finset.smul_sum, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul]
          congr 1
          ring
        apply le_of_forall_pos_le_add
        intro ε hε
        have hsel : ∀ σ : Fin n → Fin d → Bool, ∃ B ∈ ℬ,
            (⨆ B : ℬ, matInner (B : Matrix (Fin d) (Fin p) ℝ) (Θ σ)) - ε < matInner B (Θ σ) := by
          intro σ
          obtain ⟨⟨B, hB⟩, h⟩ := exists_lt_of_lt_ciSup (sub_lt_self
            (⨆ B : ℬ, matInner (B : Matrix (Fin d) (Fin p) ℝ) (Θ σ)) hε)
          exact ⟨B, hB, h⟩
        choose G hGℬ hGlt using hsel
        have hGS : ∀ σ, G σ ∈ 𝒮 := fun σ => (hℬ (hGℬ σ)).1
        have hGF : ∀ σ, F (G σ) ≤ β ^ 2 := fun σ => (hℬ (hGℬ σ)).2
        have hc := claim n w K hw hK G hGS
        have hper : ∀ σ, (⨆ B : ℬ, matInner (B : Matrix (Fin d) (Fin p) ℝ) (Θ σ)) ≤
            (1 / lam) * (matInner (G σ) (∑ i, w i (σ i)) - F (G σ)) + (β ^ 2 / lam + ε) := by
          intro σ
          rw [hΘ σ, mi_smul]
          have h1 := hGlt σ
          have h2 : F (G σ) / lam ≤ β ^ 2 / lam := div_le_div_of_nonneg_right (hGF σ) hlam.le
          have e : (1 / lam) * (lam * matInner (G σ) (Θ σ) - F (G σ))
              = matInner (G σ) (Θ σ) - F (G σ) / lam := by
            field_simp
          rw [e]
          linarith
        have hsum : ∑ σ, (⨆ B : ℬ, matInner (B : Matrix (Fin d) (Fin p) ℝ) (Θ σ)) ≤
            (1 / lam) * (2 ^ (n * d) * (n * K ^ 2 / (2 * α))) + 2 ^ (n * d) * (β ^ 2 / lam + ε) := by
          calc _ ≤ ∑ σ, ((1 / lam) * (matInner (G σ) (∑ i, w i (σ i)) - F (G σ)) + (β ^ 2 / lam + ε)) :=
                Finset.sum_le_sum fun σ _ => hper σ
            _ = (1 / lam) * ∑ σ, (matInner (G σ) (∑ i, w i (σ i)) - F (G σ))
                + 2 ^ (n * d) * (β ^ 2 / lam + ε) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
                  Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
                  Fintype.card_fin, nsmul_eq_mul]
                push_cast; ring
            _ ≤ _ := by gcongr
        calc (1 / 2 ^ (n * d) : ℝ) * ∑ σ, (⨆ B : ℬ, matInner (B : Matrix (Fin d) (Fin p) ℝ) (Θ σ))
            ≤ (1 / 2 ^ (n * d) : ℝ) * ((1 / lam) * (2 ^ (n * d) * (n * K ^ 2 / (2 * α)))
                + 2 ^ (n * d) * (β ^ 2 / lam + ε)) := by gcongr
          _ = β ^ 2 / lam + lam * Ω ^ 2 / (2 * α * n) + ε := by
            simp only [K]
            field_simp
            ring
