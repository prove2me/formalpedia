-- Prove2me | solution 1 for ProxGapTight.supercode_prob
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:48:59.217825+00:00
-- url     : https://prove2.me/submissions/487fcccf-1bf5-4393-bf13-4d41298dabc7

import Mathlib

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ProxGapTight.Dev.Supercode

open Module

section Gen

variable (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [Finite V]

/-- number of `j`-dim subspaces containing `v` is invariant under linear equivalences. -/
lemma ncard_equiv (j : ℕ) (g : V ≃ₗ[F] V) (v : V) :
    Set.ncard {S : Submodule F V | finrank F S = j ∧ g v ∈ S} =
      Set.ncard {S : Submodule F V | finrank F S = j ∧ v ∈ S} := by
  symm
  refine Set.ncard_congr (fun S _ => S.map (g : V →ₗ[F] V)) ?_ ?_ ?_
  · rintro S ⟨h1, h2⟩
    refine ⟨?_, Submodule.mem_map_of_mem h2⟩
    rw [← h1]
    exact LinearEquiv.finrank_map_eq g S
  · intro S T _ _ h
    exact Submodule.map_injective_of_injective g.injective h
  · rintro T ⟨h1, h2⟩
    refine ⟨T.map (g.symm : V →ₗ[F] V), ⟨?_, ?_⟩, ?_⟩
    · rw [← h1]
      exact LinearEquiv.finrank_map_eq g.symm T
    · exact ⟨g v, h2, by simp⟩
    · ext x
      simp only [Submodule.mem_map, LinearEquiv.coe_coe]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨g.symm x, ⟨x, hx, rfl⟩, by simp⟩

lemma ncard_eq_of_ne_zero (j : ℕ) (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    Set.ncard {S : Submodule F V | finrank F S = j ∧ w ∈ S} =
      Set.ncard {S : Submodule F V | finrank F S = j ∧ v ∈ S} := by
  haveI : Module.Finite F V := Module.Finite.of_finite
  let f : (F ∙ v) ≃ₗ[F] (F ∙ w) :=
    (LinearEquiv.toSpanNonzeroSingleton F V v hv).symm ≪≫ₗ
      LinearEquiv.toSpanNonzeroSingleton F V w hw
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have h1 : g v = w := by
    have := hg ⟨v, Submodule.mem_span_singleton_self v⟩
    have h2 : f ⟨v, Submodule.mem_span_singleton_self v⟩ = ⟨w, Submodule.mem_span_singleton_self w⟩ := by
      have : (LinearEquiv.toSpanNonzeroSingleton F V v hv).symm
          ⟨v, Submodule.mem_span_singleton_self v⟩ = 1 := by
        rw [LinearEquiv.symm_apply_eq]
        ext
        simp
      simp only [f, LinearEquiv.trans_apply, this]
      ext
      simp
    rw [h2] at this
    exact this.symm
  rw [← h1]
  exact ncard_equiv F V j g v

/-- double counting -/
lemma double_count [Fintype F] (j : ℕ) (hj : j ≤ finrank F V) (v : V) (hv : v ≠ 0) :
    Set.ncard {S : Submodule F V | finrank F S = j} * (Fintype.card F ^ j - 1) =
      (Fintype.card F ^ (finrank F V) - 1) * Set.ncard {S : Submodule F V | finrank F S = j ∧ v ∈ S} := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (Submodule F V) := Fintype.ofFinite _
  set T : Finset (Submodule F V) := Finset.univ.filter (fun S => finrank F S = j) with hT
  set R : Finset V := Finset.univ.filter (fun x => x ≠ 0) with hR
  have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := T) (t := R) (fun S x => x ∈ S)
  have hA : ∀ S ∈ T, (R.bipartiteAbove (fun S x => x ∈ S) S).card = Fintype.card F ^ j - 1 := by
    intro S hS
    have hS' : finrank F S = j := by simpa [hT] using hS
    have h1 : R.bipartiteAbove (fun S x => x ∈ S) S =
        (Finset.univ.filter (fun x : V => x ∈ S)).erase 0 := by
      ext x
      simp [Finset.bipartiteAbove, hR, and_comm]
    rw [h1, Finset.card_erase_of_mem (by simp)]
    have : (Finset.univ.filter (fun x : V => x ∈ S)).card = Fintype.card S := by
      rw [← Fintype.card_subtype]
    rw [this, Module.card_eq_pow_finrank (K := F) (V := S), hS']
  have hB : ∀ x ∈ R, (T.bipartiteBelow (fun S x => x ∈ S) x).card =
      Set.ncard {S : Submodule F V | finrank F S = j ∧ v ∈ S} := by
    intro x hx
    have hx' : x ≠ 0 := by simpa [hR] using hx
    rw [← ncard_eq_of_ne_zero F V j v x hv hx']
    rw [← Set.ncard_coe_finset]
    congr 1
    ext S
    simp [Finset.bipartiteBelow, hT]
  rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hB] at key
  simp only [Finset.sum_const, smul_eq_mul] at key
  have hTc : T.card = Set.ncard {S : Submodule F V | finrank F S = j} := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext S
    simp [hT]
  have hRc : R.card = Fintype.card F ^ (finrank F V) - 1 := by
    have : R = (Finset.univ : Finset V).erase 0 := by
      ext x; simp [hR]
    rw [this, Finset.card_erase_of_mem (by simp), Finset.card_univ,
      Module.card_eq_pow_finrank (K := F) (V := V)]
  rw [hTc, hRc] at key
  exact key

end Gen

section Quot

variable (F : Type) [Field F] (E : Type) [AddCommGroup E] [Module F E] [Module.Finite F E]
  (C₀ : Submodule F E)

lemma finrank_map_mkQ (C : Submodule F E) (h : C₀ ≤ C) :
    finrank F (C.map C₀.mkQ) + finrank F C₀ = finrank F C := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (C₀.mkQ.domRestrict C)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h1
  have h2 : finrank F (Submodule.comap C.subtype C₀) = finrank F C₀ :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe h)
  rw [h2] at h1
  exact h1

lemma ncard_transfer (k : ℕ) (hk : finrank F C₀ ≤ k) (Q : Submodule F (E ⧸ C₀) → Prop) :
    Set.ncard {C : Submodule F E | finrank F C = k ∧ C₀ ≤ C ∧ Q (C.map C₀.mkQ)} =
      Set.ncard {S : Submodule F (E ⧸ C₀) | finrank F S = k - finrank F C₀ ∧ Q S} := by
  refine Set.ncard_congr (fun C _ => C.map C₀.mkQ) ?_ ?_ ?_
  · rintro C ⟨h1, h2, h3⟩
    refine ⟨?_, h3⟩
    have := finrank_map_mkQ F E C₀ C h2
    omega
  · rintro C C' ⟨_, h2, _⟩ ⟨_, h2', _⟩ h
    have e1 := Submodule.comap_map_mkQ C₀ C
    have e2 := Submodule.comap_map_mkQ C₀ C'
    rw [h] at e1
    rw [e1] at e2
    rw [← sup_eq_right.mpr h2, ← sup_eq_right.mpr h2', e2]
  · rintro S ⟨h1, h2⟩
    have hle : C₀ ≤ S.comap C₀.mkQ := by
      intro x hx
      simp [Submodule.mem_comap, (Submodule.Quotient.mk_eq_zero C₀).mpr hx]
    have hm : (S.comap C₀.mkQ).map C₀.mkQ = S := Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective C₀) S
    refine ⟨S.comap C₀.mkQ, ⟨?_, hle, by rw [hm]; exact h2⟩, hm⟩
    have := finrank_map_mkQ F E C₀ _ hle
    rw [hm] at this
    omega

end Quot

lemma exists_sub (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V]
    (j : ℕ) (hj : j ≤ finrank F V) : ∃ S : Submodule F V, finrank F S = j := by
  let b := Module.finBasis F V
  have hli : LinearIndependent F (fun i : Fin j => b (Fin.castLE (by simpa using hj) i)) :=
    b.linearIndependent.comp _ (Fin.castLE_injective _)
  refine ⟨Submodule.span F (Set.range (fun i : Fin j => b (Fin.castLE (by simpa using hj) i))), ?_⟩
  rw [finrank_span_eq_card hli]
  simp

lemma bound (q : ℝ) (hq : 2 ≤ q) (j M : ℕ) (hjM : j ≤ M) (hM : 1 ≤ M) :
    (q ^ j - 1) / (q ^ M - 1) ≤ 2 * q ^ ((j : ℤ) - (M : ℤ)) := by
  have hb : 2 ≤ q ^ M := by
    calc (2 : ℝ) ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ M := pow_le_pow_right₀ (by linarith) hM
  have hpos : 0 < q ^ M - 1 := by linarith
  rw [zpow_sub₀ (by linarith), zpow_natCast, zpow_natCast, div_le_iff₀ hpos]
  have ha : 0 ≤ q ^ j := by positivity
  have : 2 * (q ^ j / q ^ M) * (q ^ M - 1) = 2 * q ^ j - 2 * q ^ j / q ^ M := by
    field_simp
  rw [this]
  have : 2 * q ^ j / q ^ M ≤ q ^ j := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

end ProxGapTight.Dev.Supercode

namespace ProxGapTight

open Module ProxGapTight.Dev.Supercode in
theorem chk_supercode_prob (F : Type) [Field F] [Fintype F] (N k : ℕ)
    (C₀ : Submodule F (Fin N → F)) (hk₀ : Module.finrank F C₀ ≤ k) (hkN : k ≤ N)
    (x : Fin N → F) (hx : x ∉ C₀) :
    ((Set.ncard {C : Submodule F (Fin N → F) | Module.finrank F C = k ∧ C₀ ≤ C ∧ x ∈ C} : ℝ) /
        (Set.ncard {C : Submodule F (Fin N → F) | Module.finrank F C = k ∧ C₀ ≤ C} : ℝ) =
      ((Fintype.card F : ℝ) ^ (k - Module.finrank F C₀) - 1) /
        ((Fintype.card F : ℝ) ^ (N - Module.finrank F C₀) - 1)) ∧
    ((Fintype.card F : ℝ) ^ (k - Module.finrank F C₀) - 1) /
        ((Fintype.card F : ℝ) ^ (N - Module.finrank F C₀) - 1) ≤
      2 * (Fintype.card F : ℝ) ^ ((k : ℤ) - (N : ℤ)) := by
  set d0 := finrank F C₀ with hd0
  have hM : finrank F ((Fin N → F) ⧸ C₀) = N - d0 := by
    have := Submodule.finrank_quotient_add_finrank C₀
    rw [Module.finrank_fin_fun] at this
    omega
  have hxne : (Submodule.Quotient.mk x : (Fin N → F) ⧸ C₀) ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  have hMpos : 1 ≤ N - d0 := by
    have : 0 < finrank F ((Fin N → F) ⧸ C₀) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hxne⟩
    omega
  have hjM : k - d0 ≤ finrank F ((Fin N → F) ⧸ C₀) := by omega
  have hA : Set.ncard {C : Submodule F (Fin N → F) | finrank F C = k ∧ C₀ ≤ C ∧ x ∈ C} =
      Set.ncard {S : Submodule F ((Fin N → F) ⧸ C₀) | finrank F S = k - d0 ∧
        (Submodule.Quotient.mk x : (Fin N → F) ⧸ C₀) ∈ S} := by
    rw [← ncard_transfer F (Fin N → F) C₀ k hk₀ (fun S => (Submodule.Quotient.mk x : (Fin N → F) ⧸ C₀) ∈ S)]
    congr 1
    ext C
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, Submodule.mem_map_of_mem h3⟩
    · rintro ⟨h1, h2, y, hy, hyx⟩
      refine ⟨h1, h2, ?_⟩
      have : y - x ∈ C₀ := by
        rw [← Submodule.Quotient.eq]
        exact hyx
      have := h2 this
      simpa using C.add_mem hy (C.neg_mem this)
  have hB : Set.ncard {C : Submodule F (Fin N → F) | finrank F C = k ∧ C₀ ≤ C} =
      Set.ncard {S : Submodule F ((Fin N → F) ⧸ C₀) | finrank F S = k - d0} := by
    have := ncard_transfer F (Fin N → F) C₀ k hk₀ (fun _ => True)
    simpa using this
  have hdc := double_count F ((Fin N → F) ⧸ C₀) (k - d0) hjM _ hxne
  rw [hM, ← hA, ← hB] at hdc
  obtain ⟨S, hS⟩ := exists_sub F ((Fin N → F) ⧸ C₀) (k - d0) hjM
  have htpos : 0 < Set.ncard {C : Submodule F (Fin N → F) | finrank F C = k ∧ C₀ ≤ C} := by
    rw [hB]
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨S, hS⟩
  have hq : (2 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.one_lt_card
  have hq1 : 1 ≤ (Fintype.card F : ℝ) ^ (k - d0) := one_le_pow₀ (by linarith)
  have hq2 : 1 ≤ (Fintype.card F : ℝ) ^ (N - d0) := one_le_pow₀ (by linarith)
  have hqM : (2 : ℝ) ≤ (Fintype.card F : ℝ) ^ (N - d0) := by
    calc (2 : ℝ) ≤ Fintype.card F := hq
      _ = (Fintype.card F : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) hMpos
  have hdcR := congrArg (fun n : ℕ => (n : ℝ)) hdc
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos),
    Nat.cast_one] at hdcR
  refine ⟨?_, ?_⟩
  · rw [div_eq_div_iff (by exact_mod_cast htpos.ne') (by linarith)]
    linarith
  · have := bound (Fintype.card F : ℝ) hq (k - d0) (N - d0) (by omega) hMpos
    have e : ((k - d0 : ℕ) : ℤ) - ((N - d0 : ℕ) : ℤ) = (k : ℤ) - (N : ℤ) := by omega
    rwa [e] at this

end ProxGapTight
end

theorem solution : type_of% @ProxGapTight.chk_supercode_prob := @ProxGapTight.chk_supercode_prob
