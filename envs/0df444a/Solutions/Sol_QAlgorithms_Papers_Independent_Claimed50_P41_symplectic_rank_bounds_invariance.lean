-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.symplectic_rank_bounds_invariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:34:55.04662+00:00
-- url     : https://prove2.me/submissions/0fbec8f4-1320-458b-8af1-9d1cf7e876a6

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41
noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

open QAlgorithms.Papers.Independent.Claimed50.P41

lemma g68k_rank {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsAlt) (W : Submodule ℝ V) :
    symplecticRank B W + Module.finrank ℝ (W ⊓ B.orthogonal W : Submodule ℝ V) =
      Module.finrank ℝ W := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (B.restrict W)
  have h3 : Submodule.map W.subtype (LinearMap.ker (B.restrict W)) = W ⊓ B.orthogonal W := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf,
      LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.BilinForm.IsOrtho, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun z hz => ?_⟩
      have := LinearMap.congr_fun hy ⟨z, hz⟩
      simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
        LinearMap.zero_apply] at this
      rw [← hB.neg_eq]; simp [this]
    · rintro ⟨hx, h⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      ext z
      simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
        LinearMap.zero_apply]
      rw [← hB.neg_eq, h z z.2, neg_zero]
  have h2 : Module.finrank ℝ (LinearMap.ker (B.restrict W)) =
      Module.finrank ℝ (W ⊓ B.orthogonal W : Submodule ℝ V) := by
    rw [← h3]
    exact (Submodule.equivMapOfInjective _ W.injective_subtype _).finrank_eq
  unfold symplecticRank
  omega

lemma g68k_iso_iff {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (W : Submodule ℝ V) :
    IsIsotropic B W ↔ W ≤ B.orthogonal W := by
  constructor
  · intro h x hx y hy
    exact h y hy x hx
  · intro h x hx y hy
    exact h hy x hx

lemma g68k_step {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsAlt) (W : Submodule ℝ V) (hne : W ≠ ⊥)
    (hnd : ∀ x ∈ W, (∀ y ∈ W, B x y = 0) → x = 0) :
    ∃ W' : Submodule ℝ V, Module.finrank ℝ W' + 2 = Module.finrank ℝ W ∧
      (∀ x ∈ W', (∀ y ∈ W', B x y = 0) → x = 0) := by
    obtain ⟨e, heW, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have : ∃ g ∈ W, B e g ≠ 0 := by
      by_contra h; push_neg at h; exact he0 (hnd e heW h)
    obtain ⟨g, hgW, hg⟩ := this
    set f := (B e g)⁻¹ • g with hfdef
    have hfW : f ∈ W := W.smul_mem _ hgW
    have hef : B e f = 1 := by simp [hfdef, hg]
    have hfe : B f e = -1 := by rw [← hB.neg_eq, hef]
    have hee : B e e = 0 := hB.self_eq_zero e
    have hff : B f f = 0 := hB.self_eq_zero f
    set W' : Submodule ℝ V := W ⊓ LinearMap.ker (B e) ⊓ LinearMap.ker (B f) with hW'
    have memW' : ∀ x, x ∈ W' ↔ x ∈ W ∧ B e x = 0 ∧ B f x = 0 := by
      intro x; simp [hW', and_assoc]
    have dec : ∀ w ∈ W, w - B w f • e + B w e • f ∈ W' := by
      intro w hw
      rw [memW']
      refine ⟨W.add_mem (W.sub_mem hw (W.smul_mem _ heW)) (W.smul_mem _ hfW), ?_, ?_⟩
      · simp only [map_add, map_sub, map_smul, hee, hef, smul_eq_mul]
        rw [← hB.neg_eq w e]; ring
      · simp only [map_add, map_sub, map_smul, hfe, hff, smul_eq_mul]
        rw [← hB.neg_eq w f]; ring
    have hnd' : ∀ x ∈ W', (∀ y ∈ W', B x y = 0) → x = 0 := by
      intro x hx hxy
      rw [memW'] at hx
      apply hnd x hx.1
      intro w hw
      have h1 := hxy _ (dec w hw)
      have hxe : B x e = 0 := by rw [← hB.neg_eq, hx.2.1, neg_zero]
      have hxf : B x f = 0 := by rw [← hB.neg_eq, hx.2.2, neg_zero]
      simp only [map_add, map_sub, map_smul, hxe, hxf, smul_eq_mul, mul_zero, sub_zero,
        add_zero] at h1
      exact h1
    set P : Submodule ℝ V := Submodule.span ℝ (Set.range ![e, f]) with hP
    have hli : LinearIndependent ℝ ![e, f] := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hc
      have h1 := congrArg (B e) hc
      have h2 := congrArg (B f) hc
      simp only [map_add, map_smul, hee, hef, hfe, hff, smul_eq_mul, map_zero] at h1 h2
      intro i; fin_cases i
      · simp; linarith
      · simp; linarith
    have hPr : Module.finrank ℝ P = 2 := by
      rw [hP, finrank_span_eq_card hli]; simp
    have hinf : W' ⊓ P = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
      rw [memW'] at hx1
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx2
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hx1 ⊢
      have h1 := hx1.2.1
      have h2 := hx1.2.2
      simp only [map_add, map_smul, hee, hef, hfe, hff, smul_eq_mul] at h1 h2
      have c0 : c 0 = 0 := by linarith
      have c1 : c 1 = 0 := by linarith
      simp [c0, c1]
    have hsup : W' ⊔ P = W := by
      apply le_antisymm
      · apply sup_le
        · intro x hx; exact ((memW' x).1 hx).1
        · rw [hP, Submodule.span_le]
          rintro _ ⟨i, rfl⟩; fin_cases i
          · simpa using heW
          · simpa using hfW
      · intro w hw
        have : w = (w - B w f • e + B w e • f) + (B w f • e - B w e • f) := by abel
        rw [this]
        apply Submodule.add_mem_sup (dec w hw)
        apply P.sub_mem
        · exact P.smul_mem _ (Submodule.subset_span ⟨0, by simp⟩)
        · exact P.smul_mem _ (Submodule.subset_span ⟨1, by simp⟩)
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq W' P
    rw [hsup, hinf, finrank_bot, hPr] at hdim
    exact ⟨W', by omega, hnd'⟩

lemma g68k_even {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsAlt) :
    ∀ m : ℕ, ∀ W : Submodule ℝ V, Module.finrank ℝ W = m →
      (∀ x ∈ W, (∀ y ∈ W, B x y = 0) → x = 0) → Even m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro W hW hnd
    by_cases h : W = ⊥
    · rw [h, finrank_bot] at hW; subst hW; exact ⟨0, rfl⟩
    · obtain ⟨W', h1, h2⟩ := g68k_step B hB W h hnd
      have := ih (Module.finrank ℝ W') (by omega) W' rfl h2
      have e : m = Module.finrank ℝ W' + 2 := by omega
      rw [e]; exact this.add even_two



/-- PDF pp.8–9, (3.6)–(3.8): even rank, sharp dimension bounds, and
invariance under symplectic automorphisms, hence obstruction to mapping subspaces. -/
theorem solution (n : ℕ) (hn : 0 < n)
    (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 2 * n) (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (W : Submodule ℝ V) :
    Even (symplecticRank B W) ∧ symplecticRank B W ≤ Module.finrank ℝ W ∧
    max (0 : ℤ) (2 * ((Module.finrank ℝ W : ℤ) - (n : ℤ))) ≤ (symplecticRank B W : ℤ) ∧
    (∀ f : V ≃ₗ[ℝ] V, (∀ x y, B (f x) (f y) = B x y) →
      symplecticRank B (W.map f.toLinearMap) = symplecticRank B W) ∧
    (∀ Wprime : Submodule ℝ V,
      Module.finrank ℝ Wprime = Module.finrank ℝ W →
      symplecticRank B Wprime ≠ symplecticRank B W →
        ¬ ∃ f : V ≃ₗ[ℝ] V, (∀ x y, B (f x) (f y) = B x y) ∧
          W.map f.toLinearMap = Wprime) := by
  have r := g68k_rank B hB W
  have hfo := LinearMap.BilinForm.finrank_orthogonal hnd W
  have hlw := Submodule.finrank_le W
  have inv : ∀ f : V ≃ₗ[ℝ] V, (∀ x y, B (f x) (f y) = B x y) →
      symplecticRank B (W.map f.toLinearMap) = symplecticRank B W := by
    intro f hf
    have r' := g68k_rank B hB (W.map f.toLinearMap)
    have ho : B.orthogonal (W.map f.toLinearMap) = (B.orthogonal W).map f.toLinearMap := by
      ext y
      simp only [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.BilinForm.IsOrtho,
        Submodule.mem_map, LinearEquiv.coe_coe]
      constructor
      · intro h
        refine ⟨f.symm y, fun w hw => ?_, by simp⟩
        have := h (f w) ⟨w, hw, rfl⟩
        rwa [← hf w (f.symm y), LinearEquiv.apply_symm_apply]
      · rintro ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
        rw [hf]; exact hz w hw
    rw [ho, ← Submodule.map_inf _ f.injective] at r'
    rw [LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq] at r'
    omega
  refine ⟨?_, by omega, ?_, inv, ?_⟩
  · -- complement of the radical
    set K := W ⊓ B.orthogonal W with hK
    obtain ⟨U, hU⟩ := Submodule.exists_isCompl (K.comap W.subtype)
    set U' := U.map W.subtype with hU'
    have hU'W : U' ≤ W := by
      rw [hU']; intro x hx; obtain ⟨y, _, rfl⟩ := hx; exact y.2
    have hdU : Module.finrank ℝ U' = symplecticRank B W := by
      have h1 := Submodule.finrank_add_eq_of_isCompl hU
      have h2 : Module.finrank ℝ (K.comap W.subtype) = Module.finrank ℝ K := by
        have : (K.comap W.subtype).map W.subtype = K := by
          rw [Submodule.map_comap_eq, Submodule.range_subtype, hK, ← inf_assoc, inf_idem]
        have h2 := (Submodule.equivMapOfInjective _ W.injective_subtype (K.comap W.subtype)).finrank_eq
        rw [this] at h2; exact h2
      have h3 : Module.finrank ℝ U' = Module.finrank ℝ U :=
        ((Submodule.equivMapOfInjective _ W.injective_subtype _).finrank_eq).symm
      omega
    rw [← hdU]
    refine g68k_even B hB _ U' rfl ?_
    intro x hx hxy
    obtain ⟨u, hu, rfl⟩ := hx
    have hxK : (u : V) ∈ K := by
      refine ⟨u.2, fun w hw => ?_⟩
      show B w u = 0
      -- decompose w = k + u'
      have hw' : (⟨w, hw⟩ : W) ∈ (K.comap W.subtype) ⊔ U := by rw [hU.sup_eq_top]; trivial
      obtain ⟨k, hk, u2, hu2, hsum⟩ := Submodule.mem_sup.1 hw'
      have hw2 : w = (k : V) + (u2 : V) := by rw [← Submodule.coe_add, hsum]
      rw [hw2, map_add, LinearMap.add_apply]
      have e1 : B k u = 0 := by
        have := hk.2 u u.2
        simp only [Submodule.subtype_apply] at this
        rw [← hB.neg_eq, this, neg_zero]
      have e2 : B u2 u = 0 := by
        have := hxy _ ⟨u2, hu2, rfl⟩
        simp only [Submodule.subtype_apply] at this
        rw [← hB.neg_eq, this, neg_zero]
      rw [e1, e2, add_zero]
    have : u ∈ K.comap W.subtype := hxK
    have h0 : u = 0 := by
      have := hU.inf_eq_bot
      rw [eq_bot_iff] at this
      exact (Submodule.mem_bot ℝ).1 (this ⟨‹u ∈ K.comap W.subtype›, hu⟩)
    simp [h0]
  · have hk := Submodule.finrank_mono (inf_le_right : W ⊓ B.orthogonal W ≤ B.orthogonal W)
    apply max_le
    · positivity
    · omega
  · intro Wp hdim' hne ⟨f, hf, hmap⟩
    exact hne (hmap ▸ inv f hf)



end
