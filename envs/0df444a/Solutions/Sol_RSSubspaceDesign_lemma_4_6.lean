-- Prove2me | solution 1 for RSSubspaceDesign.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:47:32.290124+00:00
-- url     : https://prove2.me/submissions/56a9fca4-d9ef-4c87-b747-1b90aaf6e334

import Mathlib

open Module

/-- `ρ(S) = dim_{E₁} span_{E₁} S`. -/
noncomputable def T44_rho (E₁ : Type*) {E₀ V : Type*} [Field E₀] [Field E₁] [AddCommGroup V]
    [Module E₁ V] [Module E₀ V] (S : Submodule E₀ V) : ℕ :=
  finrank E₁ (Submodule.span E₁ (S : Set V))

/-- Slope of `S` relative to `B`. -/
noncomputable def T44_slope (E₁ : Type*) {E₀ V : Type*} [Field E₀] [Field E₁] [AddCommGroup V]
    [Module E₁ V] [Module E₀ V] (B S : Submodule E₀ V) : ℝ :=
  ((finrank E₀ S : ℝ) - finrank E₀ B) / ((T44_rho E₁ S : ℝ) - T44_rho E₁ B)

section T44Dev

variable {E₀ E₁ V : Type*} [Field E₀] [Field E₁] [Algebra E₀ E₁] [AddCommGroup V]
    [Module E₁ V] [Module E₀ V] [IsScalarTower E₀ E₁ V]

theorem T44_fd_span (S : Submodule E₀ V) [FiniteDimensional E₀ S] :
    FiniteDimensional E₁ (Submodule.span E₁ (S : Set V)) := by
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional S).mpr inferInstance
  subst ht
  rw [Submodule.span_span_of_tower]
  exact FiniteDimensional.span_of_finite E₁ t.finite_toSet

theorem T44_rho_mono {S T : Submodule E₀ V} [FiniteDimensional E₀ T] (h : S ≤ T) :
    T44_rho E₁ S ≤ T44_rho E₁ T := by
  have := T44_fd_span (E₁ := E₁) T
  exact Submodule.finrank_mono (Submodule.span_mono h)

omit [Algebra E₀ E₁] [IsScalarTower E₀ E₁ V] in
theorem T44_rho_bot : T44_rho E₁ (⊥ : Submodule E₀ V) = 0 := by
  simp [T44_rho]

theorem T44_span_cl (U S : Submodule E₀ V) (hS : S ≤ U) :
    Submodule.span E₁ ((U ⊓ (Submodule.span E₁ (S : Set V)).restrictScalars E₀ :
      Submodule E₀ V) : Set V) = Submodule.span E₁ (S : Set V) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact (Submodule.mem_inf.mp hx).2
  · apply Submodule.span_mono
    intro x hx
    exact Submodule.mem_inf.mpr ⟨hS hx, Submodule.subset_span hx⟩

theorem T44_rho_lt (U B S : Submodule E₀ V) [FiniteDimensional E₀ U]
    (hB : B = U ⊓ (Submodule.span E₁ (B : Set V)).restrictScalars E₀)
    (hBS : B ≤ S) (hSU : S ≤ U) (hne : S ≠ B) : T44_rho E₁ B < T44_rho E₁ S := by
  have : FiniteDimensional E₀ S := Submodule.finiteDimensional_of_le hSU
  have := T44_fd_span (E₁ := E₁) S
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

theorem T44_submod (A B C : Submodule E₀ V) [FiniteDimensional E₀ A] [FiniteDimensional E₀ B]
    (hCA : C ≤ A) (hCB : C ≤ B) :
    T44_rho E₁ (A ⊔ B) + T44_rho E₁ C ≤ T44_rho E₁ A + T44_rho E₁ B := by
  have := T44_fd_span (E₁ := E₁) A
  have := T44_fd_span (E₁ := E₁) B
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
  unfold T44_rho
  omega

theorem T44_main (U : Submodule E₀ V) [FiniteDimensional E₀ U] (k : ℕ) :
    ∀ (B : Submodule E₀ V), finrank E₀ U - finrank E₀ B = k → B ≤ U →
    B = U ⊓ (Submodule.span E₁ (B : Set V)).restrictScalars E₀ →
    ∀ μ : ℝ, 0 ≤ μ → (∀ S : Submodule E₀ V, B ≤ S → S ≤ U →
      (finrank E₀ S : ℝ) - finrank E₀ B ≤ μ * ((T44_rho E₁ S : ℝ) - T44_rho E₁ B)) →
    ∃ (h : ℕ) (Us : Fin (h + 1) → Submodule E₀ V) (a : Fin h → ℝ),
      Us 0 = B ∧ Us (Fin.last h) = U ∧ StrictMono Us ∧
      (∀ i, Us i = U ⊓ (Submodule.span E₁ (Us i : Set V)).restrictScalars E₀) ∧
      (∀ ℓ, 0 ≤ a ℓ) ∧ ∑ ℓ, a ℓ ≤ μ ∧
      (∀ S : Submodule E₀ V, S ≤ U → (finrank E₀ S : ℝ) - finrank E₀ ↥(S ⊓ B) ≤
          ∑ ℓ, a ℓ * ((T44_rho E₁ (S ⊓ Us ℓ.succ) : ℝ) - T44_rho E₁ (S ⊓ B))) ∧
      ∑ ℓ, a ℓ * ((T44_rho E₁ (Us ℓ.succ) : ℝ) - T44_rho E₁ B) =
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
  have hfin : ((fun S => T44_slope E₁ B S) ''
      {S : Submodule E₀ V | B ≤ S ∧ S ≤ U ∧ S ≠ B}).Finite := by
    apply Set.Finite.subset ((((Finset.range (finrank E₀ U + 1)) ×ˢ
      (Finset.range (T44_rho E₁ U + 1)) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).toFinite.image
      (fun p : ℕ × ℕ => ((p.1 : ℝ) - finrank E₀ B) / ((p.2 : ℝ) - T44_rho E₁ B)))
    rintro _ ⟨S, ⟨_, hSU, -⟩, rfl⟩
    refine ⟨(finrank E₀ S, T44_rho E₁ S), ?_, rfl⟩
    have h1 : finrank E₀ S ≤ finrank E₀ U := Submodule.finrank_mono hSU
    have h2 : T44_rho E₁ S ≤ T44_rho E₁ U := T44_rho_mono hSU
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
    omega
  have hne : ((fun S => T44_slope E₁ B S) ''
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
    rw [hU1']; exact T44_span_cl U U1 hU1U
  have hrhoeq : T44_rho E₁ U1' = T44_rho E₁ U1 := by unfold T44_rho; rw [hspan]
  have hBU1' : B ≤ U1' := hBU1.trans hU1U1'
  have hU1'B : U1' ≠ B := fun h => hU1B (le_antisymm (h ▸ hU1U1') hBU1)
  have hU1'closed : U1' = U ⊓ (Submodule.span E₁ (U1' : Set V)).restrictScalars E₀ := by
    rw [hspan]; exact hU1'
  have : FiniteDimensional E₀ U1' := Submodule.finiteDimensional_of_le hU1'U
  have hdpos : (0 : ℝ) < (T44_rho E₁ U1' : ℝ) - T44_rho E₁ B := by
    have := T44_rho_lt U B U1' hB hBU1' hU1'U hU1'B
    have : (T44_rho E₁ B : ℝ) < T44_rho E₁ U1' := by exact_mod_cast this
    linarith
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = T44_slope E₁ B U1' := ⟨_, rfl⟩
  have hfU1 : T44_slope E₁ B U1 ≤ lam := by
    rw [hlam]
    unfold T44_slope
    rw [← hrhoeq]
    apply div_le_div_of_nonneg_right _ hdpos.le
    have : finrank E₀ U1 ≤ finrank E₀ U1' := Submodule.finrank_mono hU1U1'
    have : (finrank E₀ U1 : ℝ) ≤ finrank E₀ U1' := by exact_mod_cast this
    linarith
  have hslope : ∀ S : Submodule E₀ V, B ≤ S → S ≤ U →
      (finrank E₀ S : ℝ) - finrank E₀ B ≤ lam * ((T44_rho E₁ S : ℝ) - T44_rho E₁ B) := by
    intro S hBS hSU
    by_cases hSB : S = B
    · subst hSB; simp
    · have hd : (0 : ℝ) < (T44_rho E₁ S : ℝ) - T44_rho E₁ B := by
        have := T44_rho_lt U B S hB hBS hSU hSB
        have : (T44_rho E₁ B : ℝ) < T44_rho E₁ S := by exact_mod_cast this
        linarith
      have h1 : T44_slope E₁ B S ≤ T44_slope E₁ B U1 := hmax _ ⟨S, ⟨hBS, hSU, hSB⟩, rfl⟩
      have h2 := h1.trans hfU1
      unfold T44_slope at h2
      rwa [div_le_iff₀ hd] at h2
  have hlam_nonneg : 0 ≤ lam := by
    rw [hlam]
    unfold T44_slope
    apply div_nonneg _ hdpos.le
    have : finrank E₀ B ≤ finrank E₀ U1' := Submodule.finrank_mono hBU1'
    have : (finrank E₀ B : ℝ) ≤ finrank E₀ U1' := by exact_mod_cast this
    linarith
  have hlam_eq : lam * ((T44_rho E₁ U1' : ℝ) - T44_rho E₁ B) =
      (finrank E₀ U1' : ℝ) - finrank E₀ B := by
    rw [hlam]
    unfold T44_slope
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
        lam * ((T44_rho E₁ (S ⊓ U1') : ℝ) - T44_rho E₁ (S ⊓ B)) := by
      have hT1 : B ≤ (S ⊓ U1') ⊔ B := le_sup_right
      have hT2 : (S ⊓ U1') ⊔ B ≤ U := sup_le (inf_le_right.trans hU1'U) hBU
      have e1 := hslope _ hT1 hT2
      have : FiniteDimensional E₀ B := Submodule.finiteDimensional_of_le hBU
      have e2 := Submodule.finrank_sup_add_finrank_inf_eq (S ⊓ U1') B
      have e3 : S ⊓ U1' ⊓ B = S ⊓ B := by rw [inf_assoc, inf_eq_right.mpr hBU1']
      have e4 := T44_submod (E₁ := E₁) (S ⊓ U1') B (S ⊓ B) (inf_le_inf_left S hBU1') inf_le_right
      rw [e3] at e2
      have e4' : (T44_rho E₁ ((S ⊓ U1') ⊔ B) : ℝ) + T44_rho E₁ (S ⊓ B) ≤
          T44_rho E₁ (S ⊓ U1') + T44_rho E₁ B := by exact_mod_cast e4
      have e2' : (finrank E₀ ↥((S ⊓ U1') ⊔ B) : ℝ) + finrank E₀ ↥(S ⊓ B) =
          finrank E₀ ↥(S ⊓ U1') + finrank E₀ B := by exact_mod_cast e2
      have e5 : lam * ((T44_rho E₁ ((S ⊓ U1') ⊔ B) : ℝ) - T44_rho E₁ B) ≤
          lam * ((T44_rho E₁ (S ⊓ U1') : ℝ) - T44_rho E₁ (S ⊓ B)) :=
        mul_le_mul_of_nonneg_left (by linarith) hlam_nonneg
      linarith
    have ih1 := hineq S hSU
    have split : ∑ j, a' j * ((T44_rho E₁ (S ⊓ Us' j.succ) : ℝ) - T44_rho E₁ (S ⊓ B)) =
        ∑ j, a' j * ((T44_rho E₁ (S ⊓ Us' j.succ) : ℝ) - T44_rho E₁ (S ⊓ U1')) +
        (∑ j, a' j) * ((T44_rho E₁ (S ⊓ U1') : ℝ) - T44_rho E₁ (S ⊓ B)) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [split]
    nlinarith
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, h0]
    have split : ∑ j, a' j * ((T44_rho E₁ (Us' j.succ) : ℝ) - T44_rho E₁ B) =
        ∑ j, a' j * ((T44_rho E₁ (Us' j.succ) : ℝ) - T44_rho E₁ U1') +
        (∑ j, a' j) * ((T44_rho E₁ U1' : ℝ) - T44_rho E₁ B) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [split, heq]
    linarith

theorem T44_dimcomp (U : Submodule E₀ V) [FiniteDimensional E₀ U] :
    ∃ (h : ℕ) (Us : Fin (h + 1) → Submodule E₀ V) (a : Fin h → ℝ),
      Us 0 = ⊥ ∧ Us (Fin.last h) = U ∧ StrictMono Us ∧
      (∀ i, Us i = U ⊓ (Submodule.span E₁ (Us i : Set V)).restrictScalars E₀) ∧
      (∀ ℓ, 0 ≤ a ℓ) ∧
      (∀ S : Submodule E₀ V, S ≤ U →
        (finrank E₀ S : ℝ) ≤ ∑ ℓ : Fin h, a ℓ * (T44_rho E₁ (S ⊓ Us ℓ.succ) : ℝ)) ∧
      ∑ ℓ : Fin h, a ℓ * (T44_rho E₁ (Us ℓ.succ) : ℝ) = finrank E₀ U := by
  have hbot : (⊥ : Submodule E₀ V) =
      U ⊓ (Submodule.span E₁ ((⊥ : Submodule E₀ V) : Set V)).restrictScalars E₀ := by
    simp
  obtain ⟨h, Us, a, h0, hlast, hmono, hclosed, ha, -, hineq, heq⟩ :=
    T44_main (E₁ := E₁) U _ ⊥ rfl bot_le hbot (finrank E₀ U) (Nat.cast_nonneg _) (by
      intro S _ hSU
      rw [T44_rho_bot, finrank_bot]
      simp only [Nat.cast_zero, sub_zero]
      by_cases hS : S = ⊥
      · subst hS
        rw [finrank_bot, Nat.cast_zero]
        exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · have h1 := T44_rho_lt U ⊥ S hbot bot_le hSU hS
        rw [T44_rho_bot] at h1
        have h2 : (1 : ℝ) ≤ T44_rho E₁ S := by exact_mod_cast h1
        have h3 : (finrank E₀ S : ℝ) ≤ finrank E₀ U := by
          exact_mod_cast Submodule.finrank_mono hSU
        nlinarith)
  refine ⟨h, Us, a, h0, hlast, hmono, hclosed, ha, ?_, ?_⟩
  · intro S hS
    have := hineq S hS
    have e : finrank E₀ ↥(S ⊓ ⊥) = 0 := by rw [inf_bot_eq]; exact finrank_bot _ _
    simp only [inf_bot_eq, T44_rho_bot, Nat.cast_zero, sub_zero, e] at this
    exact this
  · simp only [T44_rho_bot, finrank_bot, Nat.cast_zero, sub_zero] at heq
    exact heq

end T44Dev

theorem solution {E₀ E₁ V : Type*} [Field E₀] [Field E₁] [Algebra E₀ E₁] [AddCommGroup V]
    [Module E₁ V] [Module E₀ V] [IsScalarTower E₀ E₁ V]
    (U : Submodule E₀ V) [FiniteDimensional E₀ U] :
    ∃ (h : ℕ) (Us : Fin (h + 1) → Submodule E₀ V) (a : Fin h → ℝ),
      Us 0 = ⊥ ∧ Us (Fin.last h) = U ∧ StrictMono Us ∧
      (∀ i, Us i = U ⊓ (Submodule.span E₁ (Us i : Set V)).restrictScalars E₀) ∧
      (∀ ℓ, 0 ≤ a ℓ) ∧
      (∀ S : Submodule E₀ V, S ≤ U →
        (Module.finrank E₀ S : ℝ) ≤
          ∑ ℓ : Fin h, a ℓ *
            (Module.finrank E₁ (Submodule.span E₁ ((S ⊓ Us ℓ.succ : Submodule E₀ V) : Set V)) : ℝ)) ∧
      ∑ ℓ : Fin h, a ℓ * (Module.finrank E₁ (Submodule.span E₁ (Us ℓ.succ : Set V)) : ℝ) =
        Module.finrank E₀ U :=
  T44_dimcomp (E₁ := E₁) U
