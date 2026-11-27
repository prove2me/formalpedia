-- Prove2me | solution 1 for RSSubspaceDesign.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:47:31.793894+00:00
-- url     : https://prove2.me/submissions/17b2ee35-fde2-4f6a-ba80-07c1618a0449

import Mathlib
import Definitions.Def_RSSubspaceDesign_IsSubspaceDesign

open Module

/-- `ρ(S) = dim_{E₁} span_{E₁} S`. -/
noncomputable def L45_rho (E₁ : Type*) {E₀ V : Type*} [Field E₀] [Field E₁] [AddCommGroup V]
    [Module E₁ V] [Module E₀ V] (S : Submodule E₀ V) : ℕ :=
  finrank E₁ (Submodule.span E₁ (S : Set V))

/-- Slope of `S` relative to `B`. -/
noncomputable def L45_slope (E₁ : Type*) {E₀ V : Type*} [Field E₀] [Field E₁] [AddCommGroup V]
    [Module E₁ V] [Module E₀ V] (B S : Submodule E₀ V) : ℝ :=
  ((finrank E₀ S : ℝ) - finrank E₀ B) / ((L45_rho E₁ S : ℝ) - L45_rho E₁ B)

section L45Dev

variable {E₀ E₁ V : Type*} [Field E₀] [Field E₁] [Algebra E₀ E₁] [AddCommGroup V]
    [Module E₁ V] [Module E₀ V] [IsScalarTower E₀ E₁ V]

theorem L45_fd_span (S : Submodule E₀ V) [FiniteDimensional E₀ S] :
    FiniteDimensional E₁ (Submodule.span E₁ (S : Set V)) := by
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional S).mpr inferInstance
  subst ht
  rw [Submodule.span_span_of_tower]
  exact FiniteDimensional.span_of_finite E₁ t.finite_toSet

theorem L45_rho_mono {S T : Submodule E₀ V} [FiniteDimensional E₀ T] (h : S ≤ T) :
    L45_rho E₁ S ≤ L45_rho E₁ T := by
  have := L45_fd_span (E₁ := E₁) T
  exact Submodule.finrank_mono (Submodule.span_mono h)

omit [Algebra E₀ E₁] [IsScalarTower E₀ E₁ V] in
theorem L45_rho_bot : L45_rho E₁ (⊥ : Submodule E₀ V) = 0 := by
  simp [L45_rho]

theorem L45_span_cl (U S : Submodule E₀ V) (hS : S ≤ U) :
    Submodule.span E₁ ((U ⊓ (Submodule.span E₁ (S : Set V)).restrictScalars E₀ :
      Submodule E₀ V) : Set V) = Submodule.span E₁ (S : Set V) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact (Submodule.mem_inf.mp hx).2
  · apply Submodule.span_mono
    intro x hx
    exact Submodule.mem_inf.mpr ⟨hS hx, Submodule.subset_span hx⟩

theorem L45_rho_lt (U B S : Submodule E₀ V) [FiniteDimensional E₀ U]
    (hB : B = U ⊓ (Submodule.span E₁ (B : Set V)).restrictScalars E₀)
    (hBS : B ≤ S) (hSU : S ≤ U) (hne : S ≠ B) : L45_rho E₁ B < L45_rho E₁ S := by
  have : FiniteDimensional E₀ S := Submodule.finiteDimensional_of_le hSU
  have := L45_fd_span (E₁ := E₁) S
  by_contra hlt
  push Not at hlt
  have heq : Submodule.span E₁ (B : Set V) = Submodule.span E₁ (S : Set V) :=
    Submodule.eq_of_le_of_finrank_le (Submodule.span_mono hBS) hlt
  apply hne
  apply le_antisymm _ hBS
  have : S ≤ U ⊓ (Submodule.span E₁ (B : Set V)).restrictScalars E₀ := by
    intro x hx
    refine Submodule.mem_inf.mpr ⟨hSU hx, ?_⟩
    rw [Submodule.restrictScalars_mem, heq]
    exact Submodule.subset_span hx
  exact this.trans hB.ge

theorem L45_submod (A B C : Submodule E₀ V) [FiniteDimensional E₀ A] [FiniteDimensional E₀ B]
    (hCA : C ≤ A) (hCB : C ≤ B) :
    L45_rho E₁ (A ⊔ B) + L45_rho E₁ C ≤ L45_rho E₁ A + L45_rho E₁ B := by
  have := L45_fd_span (E₁ := E₁) A
  have := L45_fd_span (E₁ := E₁) B
  have h1 : Submodule.span E₁ ((A ⊔ B : Submodule E₀ V) : Set V) ≤
      Submodule.span E₁ (A : Set V) ⊔ Submodule.span E₁ (B : Set V) := by
    rw [Submodule.span_le]
    have : A ⊔ B ≤ (Submodule.span E₁ (A : Set V) ⊔
        Submodule.span E₁ (B : Set V)).restrictScalars E₀ :=
      sup_le (fun y hy => Submodule.mem_sup_left (Submodule.subset_span hy))
        (fun y hy => Submodule.mem_sup_right (Submodule.subset_span hy))
    exact fun x hx => this hx
  have h2 : Submodule.span E₁ (C : Set V) ≤
      Submodule.span E₁ (A : Set V) ⊓ Submodule.span E₁ (B : Set V) :=
    le_inf (Submodule.span_mono hCA) (Submodule.span_mono hCB)
  have e := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span E₁ (A : Set V))
    (Submodule.span E₁ (B : Set V))
  have i1 := Submodule.finrank_mono h1
  have i2 := Submodule.finrank_mono h2
  unfold L45_rho
  omega

theorem L45_main (U : Submodule E₀ V) [FiniteDimensional E₀ U] (k : ℕ) :
    ∀ (B : Submodule E₀ V), finrank E₀ U - finrank E₀ B = k → B ≤ U →
    B = U ⊓ (Submodule.span E₁ (B : Set V)).restrictScalars E₀ →
    ∀ μ : ℝ, 0 ≤ μ → (∀ S : Submodule E₀ V, B ≤ S → S ≤ U →
      (finrank E₀ S : ℝ) - finrank E₀ B ≤ μ * ((L45_rho E₁ S : ℝ) - L45_rho E₁ B)) →
    ∃ (h : ℕ) (Us : Fin (h + 1) → Submodule E₀ V) (a : Fin h → ℝ),
      Us 0 = B ∧ Us (Fin.last h) = U ∧ StrictMono Us ∧
      (∀ i, Us i = U ⊓ (Submodule.span E₁ (Us i : Set V)).restrictScalars E₀) ∧
      (∀ ℓ, 0 ≤ a ℓ) ∧ ∑ ℓ, a ℓ ≤ μ ∧
      (∀ S : Submodule E₀ V, S ≤ U → (finrank E₀ S : ℝ) - finrank E₀ ↥(S ⊓ B) ≤
          ∑ ℓ, a ℓ * ((L45_rho E₁ (S ⊓ Us ℓ.succ) : ℝ) - L45_rho E₁ (S ⊓ B))) ∧
      ∑ ℓ, a ℓ * ((L45_rho E₁ (Us ℓ.succ) : ℝ) - L45_rho E₁ B) =
        (finrank E₀ U : ℝ) - finrank E₀ B := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro B hk hBU hB μ hμ0 hμ
  by_cases hBU' : B = U
  · subst hBU'
    refine ⟨0, fun _ => B, fun i => i.elim0, rfl, rfl, Fin.strictMono_iff_lt_succ.mpr (fun i => i.elim0),
      fun _ => hB, fun i => i.elim0, by simpa using hμ0, ?_, by simp⟩
    intro S hS
    rw [inf_eq_left.mpr hS]
    simp
  have hfin : ((fun S => L45_slope E₁ B S) ''
      {S : Submodule E₀ V | B ≤ S ∧ S ≤ U ∧ S ≠ B}).Finite := by
    apply Set.Finite.subset ((((Finset.range (finrank E₀ U + 1)) ×ˢ
      (Finset.range (L45_rho E₁ U + 1)) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).toFinite.image
      (fun p : ℕ × ℕ => ((p.1 : ℝ) - finrank E₀ B) / ((p.2 : ℝ) - L45_rho E₁ B)))
    rintro _ ⟨S, ⟨_, hSU, -⟩, rfl⟩
    refine ⟨(finrank E₀ S, L45_rho E₁ S), ?_, rfl⟩
    have h1 : finrank E₀ S ≤ finrank E₀ U := Submodule.finrank_mono hSU
    have h2 : L45_rho E₁ S ≤ L45_rho E₁ U := L45_rho_mono hSU
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
    omega
  have hne : ((fun S => L45_slope E₁ B S) ''
      {S : Submodule E₀ V | B ≤ S ∧ S ≤ U ∧ S ≠ B}).Nonempty :=
    ⟨_, U, ⟨hBU, le_rfl, Ne.symm hBU'⟩, rfl⟩
  obtain ⟨_, ⟨U1, ⟨hBU1, hU1U, hU1B⟩, rfl⟩, hmax⟩ := Set.exists_max_image _ id hfin hne
  obtain ⟨U1', hU1'⟩ : ∃ W : Submodule E₀ V,
      W = U ⊓ (Submodule.span E₁ (U1 : Set V)).restrictScalars E₀ := ⟨_, rfl⟩
  have hU1U1' : U1 ≤ U1' := by
    rw [hU1']
    exact fun x hx => Submodule.mem_inf.mpr ⟨hU1U hx, Submodule.subset_span hx⟩
  have hU1'U : U1' ≤ U := by rw [hU1']; exact inf_le_left
  have hspan : Submodule.span E₁ (U1' : Set V) = Submodule.span E₁ (U1 : Set V) := by
    rw [hU1']; exact L45_span_cl U U1 hU1U
  have hrhoeq : L45_rho E₁ U1' = L45_rho E₁ U1 := by unfold L45_rho; rw [hspan]
  have hBU1' : B ≤ U1' := hBU1.trans hU1U1'
  have hU1'B : U1' ≠ B := fun h => hU1B (le_antisymm (h ▸ hU1U1') hBU1)
  have hU1'closed : U1' = U ⊓ (Submodule.span E₁ (U1' : Set V)).restrictScalars E₀ := by
    rw [hspan]; exact hU1'
  have : FiniteDimensional E₀ U1' := Submodule.finiteDimensional_of_le hU1'U
  have hdpos : (0 : ℝ) < (L45_rho E₁ U1' : ℝ) - L45_rho E₁ B := by
    have := L45_rho_lt U B U1' hB hBU1' hU1'U hU1'B
    have : (L45_rho E₁ B : ℝ) < L45_rho E₁ U1' := by exact_mod_cast this
    linarith
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = L45_slope E₁ B U1' := ⟨_, rfl⟩
  have hfU1 : L45_slope E₁ B U1 ≤ lam := by
    rw [hlam]
    unfold L45_slope
    rw [← hrhoeq]
    apply div_le_div_of_nonneg_right _ hdpos.le
    have : finrank E₀ U1 ≤ finrank E₀ U1' := Submodule.finrank_mono hU1U1'
    have : (finrank E₀ U1 : ℝ) ≤ finrank E₀ U1' := by exact_mod_cast this
    linarith
  have hslope : ∀ S : Submodule E₀ V, B ≤ S → S ≤ U →
      (finrank E₀ S : ℝ) - finrank E₀ B ≤ lam * ((L45_rho E₁ S : ℝ) - L45_rho E₁ B) := by
    intro S hBS hSU
    by_cases hSB : S = B
    · subst hSB; simp
    · have hd : (0 : ℝ) < (L45_rho E₁ S : ℝ) - L45_rho E₁ B := by
        have := L45_rho_lt U B S hB hBS hSU hSB
        have : (L45_rho E₁ B : ℝ) < L45_rho E₁ S := by exact_mod_cast this
        linarith
      have h1 : L45_slope E₁ B S ≤ L45_slope E₁ B U1 := hmax _ ⟨S, ⟨hBS, hSU, hSB⟩, rfl⟩
      have h2 := h1.trans hfU1
      unfold L45_slope at h2
      rwa [div_le_iff₀ hd] at h2
  have hlam_nonneg : 0 ≤ lam := by
    rw [hlam]
    unfold L45_slope
    apply div_nonneg _ hdpos.le
    have : finrank E₀ B ≤ finrank E₀ U1' := Submodule.finrank_mono hBU1'
    have : (finrank E₀ B : ℝ) ≤ finrank E₀ U1' := by exact_mod_cast this
    linarith
  have hlam_eq : lam * ((L45_rho E₁ U1' : ℝ) - L45_rho E₁ B) =
      (finrank E₀ U1' : ℝ) - finrank E₀ B := by
    rw [hlam]
    unfold L45_slope
    exact div_mul_cancel₀ _ hdpos.ne'
  have hlam_le : lam ≤ μ := by
    have := hμ U1' hBU1' hU1'U
    by_contra hc
    push Not at hc
    have := mul_lt_mul_of_pos_right hc hdpos
    linarith
  have hk' : finrank E₀ U - finrank E₀ U1' < k := by
    have := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hBU1' (Ne.symm hU1'B))
    have := Submodule.finrank_mono hU1'U
    omega
  obtain ⟨h', Us', a', h0, hlast, hmono, hclosed, ha, hsum, hineq, heq⟩ :=
    ih _ hk' U1' rfl hU1'U hU1'closed lam hlam_nonneg (by
      intro S hS1 hSU
      have e1 := hslope S (hBU1'.trans hS1) hSU
      linarith)
  refine ⟨h' + 1, Fin.cons B Us', Fin.cons (lam - ∑ j, a' j) a', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · rw [← Fin.succ_last, Fin.cons_succ]; exact hlast
  · exact StrictMono.vecCons hmono (by rw [h0]; exact lt_of_le_of_ne hBU1' (Ne.symm hU1'B))
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]; exact hB
    · simp only [Fin.cons_succ]; exact hclosed j
  · intro ℓ
    refine Fin.cases ?_ (fun j => ?_) ℓ
    · simp only [Fin.cons_zero]; linarith
    · simp only [Fin.cons_succ]; exact ha j
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    linarith
  · intro S hSU
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, h0]
    have : FiniteDimensional E₀ S := Submodule.finiteDimensional_of_le hSU
    have step : (finrank E₀ ↥(S ⊓ U1') : ℝ) - finrank E₀ ↥(S ⊓ B) ≤
        lam * ((L45_rho E₁ (S ⊓ U1') : ℝ) - L45_rho E₁ (S ⊓ B)) := by
      have hT1 : B ≤ (S ⊓ U1') ⊔ B := le_sup_right
      have hT2 : (S ⊓ U1') ⊔ B ≤ U := sup_le (inf_le_right.trans hU1'U) hBU
      have e1 := hslope _ hT1 hT2
      have : FiniteDimensional E₀ B := Submodule.finiteDimensional_of_le hBU
      have e2 := Submodule.finrank_sup_add_finrank_inf_eq (S ⊓ U1') B
      have e3 : S ⊓ U1' ⊓ B = S ⊓ B := by rw [inf_assoc, inf_eq_right.mpr hBU1']
      have e4 := L45_submod (E₁ := E₁) (S ⊓ U1') B (S ⊓ B) (inf_le_inf_left S hBU1') inf_le_right
      rw [e3] at e2
      have e4' : (L45_rho E₁ ((S ⊓ U1') ⊔ B) : ℝ) + L45_rho E₁ (S ⊓ B) ≤
          L45_rho E₁ (S ⊓ U1') + L45_rho E₁ B := by exact_mod_cast e4
      have e2' : (finrank E₀ ↥((S ⊓ U1') ⊔ B) : ℝ) + finrank E₀ ↥(S ⊓ B) =
          finrank E₀ ↥(S ⊓ U1') + finrank E₀ B := by exact_mod_cast e2
      have e5 : lam * ((L45_rho E₁ ((S ⊓ U1') ⊔ B) : ℝ) - L45_rho E₁ B) ≤
          lam * ((L45_rho E₁ (S ⊓ U1') : ℝ) - L45_rho E₁ (S ⊓ B)) :=
        mul_le_mul_of_nonneg_left (by linarith) hlam_nonneg
      linarith
    have ih1 := hineq S hSU
    have split : ∑ j, a' j * ((L45_rho E₁ (S ⊓ Us' j.succ) : ℝ) - L45_rho E₁ (S ⊓ B)) =
        ∑ j, a' j * ((L45_rho E₁ (S ⊓ Us' j.succ) : ℝ) - L45_rho E₁ (S ⊓ U1')) +
        (∑ j, a' j) * ((L45_rho E₁ (S ⊓ U1') : ℝ) - L45_rho E₁ (S ⊓ B)) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [split]
    nlinarith
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, h0]
    have split : ∑ j, a' j * ((L45_rho E₁ (Us' j.succ) : ℝ) - L45_rho E₁ B) =
        ∑ j, a' j * ((L45_rho E₁ (Us' j.succ) : ℝ) - L45_rho E₁ U1') +
        (∑ j, a' j) * ((L45_rho E₁ U1' : ℝ) - L45_rho E₁ B) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [split, heq]
    linarith

theorem L45_dimcomp (U : Submodule E₀ V) [FiniteDimensional E₀ U] :
    ∃ (h : ℕ) (Us : Fin (h + 1) → Submodule E₀ V) (a : Fin h → ℝ),
      Us 0 = ⊥ ∧ Us (Fin.last h) = U ∧ StrictMono Us ∧
      (∀ i, Us i = U ⊓ (Submodule.span E₁ (Us i : Set V)).restrictScalars E₀) ∧
      (∀ ℓ, 0 ≤ a ℓ) ∧
      (∀ S : Submodule E₀ V, S ≤ U →
        (finrank E₀ S : ℝ) ≤ ∑ ℓ : Fin h, a ℓ * (L45_rho E₁ (S ⊓ Us ℓ.succ) : ℝ)) ∧
      ∑ ℓ : Fin h, a ℓ * (L45_rho E₁ (Us ℓ.succ) : ℝ) = finrank E₀ U := by
  have hbot : (⊥ : Submodule E₀ V) =
      U ⊓ (Submodule.span E₁ ((⊥ : Submodule E₀ V) : Set V)).restrictScalars E₀ := by
    simp
  obtain ⟨h, Us, a, h0, hlast, hmono, hclosed, ha, -, hineq, heq⟩ :=
    L45_main (E₁ := E₁) U _ ⊥ rfl bot_le hbot (finrank E₀ U) (Nat.cast_nonneg _) (by
      intro S _ hSU
      rw [L45_rho_bot, finrank_bot]
      simp only [Nat.cast_zero, sub_zero]
      by_cases hS : S = ⊥
      · subst hS
        rw [finrank_bot, Nat.cast_zero]
        exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · have h1 := L45_rho_lt U ⊥ S hbot bot_le hSU hS
        rw [L45_rho_bot] at h1
        have h2 : (1 : ℝ) ≤ L45_rho E₁ S := by exact_mod_cast h1
        have h3 : (finrank E₀ S : ℝ) ≤ finrank E₀ U := by
          exact_mod_cast Submodule.finrank_mono hSU
        nlinarith)
  refine ⟨h, Us, a, h0, hlast, hmono, hclosed, ha, ?_, ?_⟩
  · intro S hS
    have := hineq S hS
    have e : finrank E₀ ↥(S ⊓ ⊥) = 0 := by rw [inf_bot_eq]; exact finrank_bot _ _
    simp only [inf_bot_eq, L45_rho_bot, Nat.cast_zero, sub_zero, e] at this
    exact this
  · simp only [L45_rho_bot, finrank_bot, Nat.cast_zero, sub_zero] at heq
    exact heq

end L45Dev

theorem L45_transfer {E₀ E₁ V : Type*} [Field E₀] [Field E₁] [Algebra E₀ E₁] [AddCommGroup V]
    [Module E₁ V] [Module E₀ V] [IsScalarTower E₀ E₁ V]
    (C : Submodule E₀ V) {n : ℕ} (H : Fin n → Submodule E₀ V)
    (r : ℕ) (τ : ℝ)
    (hyp : ∀ W : Submodule E₀ V, W ≤ C → W ≠ ⊥ → FiniteDimensional E₀ W →
      Module.finrank E₀ W ≤ r →
      (∑ i, (Module.finrank E₁ (Submodule.span E₁ ((W ⊓ H i : Submodule E₀ V) : Set V)) : ℝ)) ≤
        n * τ * (Module.finrank E₁ (Submodule.span E₁ (W : Set V)) : ℝ)) :
    ∀ U : Submodule E₀ V, U ≤ C → 1 ≤ Module.finrank E₀ U → Module.finrank E₀ U ≤ r →
      (∑ i, (Module.finrank E₀ ↥(U ⊓ H i) : ℝ)) ≤ n * τ * Module.finrank E₀ U := by
  intro U hUC hU1 hUr
  have : FiniteDimensional E₀ U := Module.finite_of_finrank_pos (by omega)
  obtain ⟨h, Us, a, h0, -, hmono, hclosed, ha, hineq, heq⟩ := L45_dimcomp (E₁ := E₁) U
  have hWU : ∀ ℓ : Fin h, Us ℓ.succ ≤ U := fun ℓ => (hclosed ℓ.succ).le.trans inf_le_left
  have hWne : ∀ ℓ : Fin h, Us ℓ.succ ≠ ⊥ := by
    intro ℓ hℓ
    have := hmono (Fin.succ_pos ℓ)
    rw [h0, hℓ] at this
    exact lt_irrefl _ this
  have hW : ∀ ℓ : Fin h, (∑ i, (L45_rho E₁ (Us ℓ.succ ⊓ H i) : ℝ)) ≤
      n * τ * (L45_rho E₁ (Us ℓ.succ) : ℝ) := by
    intro ℓ
    exact hyp _ ((hWU ℓ).trans hUC) (hWne ℓ) (Submodule.finiteDimensional_of_le (hWU ℓ))
      ((Submodule.finrank_mono (hWU ℓ)).trans hUr)
  have hinter : ∀ (i : Fin n) (ℓ : Fin h), U ⊓ H i ⊓ Us ℓ.succ = Us ℓ.succ ⊓ H i := by
    intro i ℓ
    rw [inf_comm, ← inf_assoc, inf_eq_left.mpr (hWU ℓ)]
  calc (∑ i, (Module.finrank E₀ ↥(U ⊓ H i) : ℝ))
      ≤ ∑ i, ∑ ℓ : Fin h, a ℓ * (L45_rho E₁ (U ⊓ H i ⊓ Us ℓ.succ) : ℝ) :=
        Finset.sum_le_sum (fun i _ => hineq _ inf_le_left)
    _ = ∑ ℓ : Fin h, a ℓ * ∑ i, (L45_rho E₁ (Us ℓ.succ ⊓ H i) : ℝ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun ℓ _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hinter]
    _ ≤ ∑ ℓ : Fin h, a ℓ * (n * τ * (L45_rho E₁ (Us ℓ.succ) : ℝ)) :=
        Finset.sum_le_sum (fun ℓ _ => mul_le_mul_of_nonneg_left (hW ℓ) (ha ℓ))
    _ = n * τ * ∑ ℓ : Fin h, a ℓ * (L45_rho E₁ (Us ℓ.succ) : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun ℓ _ => ?_)
        ring
    _ = n * τ * Module.finrank E₀ U := by rw [heq]

theorem L45_span_finrank_le {E₀ E₁ V : Type*} [Field E₀] [Field E₁] [Algebra E₀ E₁]
    [AddCommGroup V] [Module E₁ V] [Module E₀ V] [IsScalarTower E₀ E₁ V]
    (W : Submodule E₀ V) [FiniteDimensional E₀ W] :
    finrank E₁ (Submodule.span E₁ (W : Set V)) ≤ finrank E₀ W := by
  let b := Module.finBasis E₀ W
  have hWspan : Submodule.span E₀ (Set.range (W.subtype ∘ b)) = W := by
    have := congrArg (Submodule.map W.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at this
    exact this
  calc finrank E₁ (Submodule.span E₁ (W : Set V))
      = finrank E₁ (Submodule.span E₁
          ((Submodule.span E₀ (Set.range (W.subtype ∘ b)) : Submodule E₀ V) : Set V)) := by
        rw [hWspan]
    _ = finrank E₁ (Submodule.span E₁ (Set.range (W.subtype ∘ b))) := by
        rw [Submodule.span_span_of_tower]
    _ ≤ Fintype.card (Fin (finrank E₀ W)) := finrank_range_le_card _
    _ = finrank E₀ W := Fintype.card_fin _

theorem solution {K₀ K V : Type*} [Field K₀] [Field K] [Finite K] [Algebra K₀ K]
    [AddCommGroup V] [Module K V] [Module K₀ V] [IsScalarTower K₀ K V]
    {n : ℕ} (C : Submodule K (Fin n → V)) (τ : ℕ → ℝ)
    (hC : RSSubspaceDesign.IsSubspaceDesign K C τ) :
    RSSubspaceDesign.IsSubspaceDesign K₀ (C.restrictScalars K₀) τ := by
  intro r hr A hAC hAfd hAr
  by_cases hA : finrank K₀ A = 0
  · have hAbot : A = ⊥ := Submodule.finrank_eq_zero.mp hA
    subst hAbot
    have h0 : ∀ i : Fin n, finrank K₀ ↥((⊥ : Submodule K₀ (Fin n → V)) ⊓
        LinearMap.ker (LinearMap.proj i)) = 0 := fun i => by
      rw [bot_inf_eq]; exact finrank_bot _ _
    simp [h0]
  have hnpos : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exfalso
      subst hn
      apply hA
      have : A = ⊥ := (Submodule.eq_bot_iff A).mpr (fun x _ => funext (fun i => i.elim0))
      subst this
      exact finrank_bot _ _
    · exact_mod_cast hn
  let H : Fin n → Submodule K₀ (Fin n → V) := fun i => A ⊓ LinearMap.ker (LinearMap.proj i)
  have key := L45_transfer (E₁ := K) A H r (τ r) (by
    intro W hWA _ hWfd hWr
    let Wt : Submodule K (Fin n → V) := Submodule.span K (W : Set (Fin n → V))
    have hWtC : Wt ≤ C := by
      rw [Submodule.span_le]
      exact fun x hx => hAC (hWA hx)
    have hWtfd : FiniteDimensional K Wt := L45_fd_span W
    have hWtr : finrank K Wt ≤ r := (L45_span_finrank_le W).trans hWr
    have hCi := hC r hr Wt hWtC hWtfd hWtr
    rw [div_le_iff₀ hnpos] at hCi
    have hle : ∀ i, (finrank K (Submodule.span K ((W ⊓ H i : Submodule K₀ (Fin n → V)) :
        Set (Fin n → V))) : ℝ) ≤ finrank K ↥(Wt ⊓ LinearMap.ker (LinearMap.proj i)) := by
      intro i
      have hsub : Submodule.span K ((W ⊓ H i : Submodule K₀ (Fin n → V)) : Set (Fin n → V)) ≤
          Wt ⊓ LinearMap.ker (LinearMap.proj i) := by
        rw [Submodule.span_le]
        intro x hx
        have hx' := Submodule.mem_inf.mp hx
        have hx'' := Submodule.mem_inf.mp hx'.2
        refine Submodule.mem_inf.mpr ⟨Submodule.subset_span hx'.1, ?_⟩
        have := hx''.2
        rw [LinearMap.mem_ker] at this ⊢
        exact this
      exact_mod_cast Submodule.finrank_mono hsub
    calc (∑ i, (finrank K (Submodule.span K ((W ⊓ H i : Submodule K₀ (Fin n → V)) :
          Set (Fin n → V))) : ℝ))
        ≤ ∑ i, (finrank K ↥(Wt ⊓ LinearMap.ker (LinearMap.proj i)) : ℝ) :=
          Finset.sum_le_sum (fun i _ => hle i)
      _ ≤ (finrank K Wt : ℝ) * τ r * n := hCi
      _ = n * τ r * (finrank K Wt : ℝ) := by ring) A le_rfl (by omega) hAr
  have e : ∀ i, A ⊓ H i = A ⊓ LinearMap.ker (LinearMap.proj i) := fun i => inf_left_idem _ _
  have hsumeq : (∑ i, (finrank K₀ ↥(A ⊓ H i) : ℝ)) =
      ∑ i, (finrank K₀ ↥(A ⊓ LinearMap.ker (LinearMap.proj i)) : ℝ) :=
    Finset.sum_congr rfl (fun i _ => by rw [e i])
  rw [hsumeq] at key
  rw [div_le_iff₀ hnpos]
  calc (∑ i, (finrank K₀ ↥(A ⊓ LinearMap.ker (LinearMap.proj i)) : ℝ))
      ≤ n * τ r * finrank K₀ A := key
    _ = finrank K₀ A * τ r * n := by ring
