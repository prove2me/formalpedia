-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.symplectic_bases_pairing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:30:42.837977+00:00
-- url     : https://prove2.me/submissions/f89ba2b7-4f1d-432c-afcf-86aaa9cd4706

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41
noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

open QAlgorithms.Papers.Independent.Claimed50.P41

lemma g68k_sigma (n : ℕ) : sigma n = -Matrix.J (Fin n) ℝ := by
  simp [sigma, Matrix.J, Matrix.fromBlocks_neg]

lemma g68k_pres_iff {n : ℕ} (S : Matrix (Phase n) (Phase n) ℝ) :
    PreservesCanonicalForm S ↔ S ∈ Matrix.symplecticGroup (Fin n) ℝ := by
  rw [SymplecticGroup.mem_iff, PreservesCanonicalForm, g68k_sigma]
  simp [Matrix.mul_neg, Matrix.neg_mul]

lemma g68k_sigma_inv (n : ℕ) : (sigma n)⁻¹ = Matrix.J (Fin n) ℝ := by
  rw [g68k_sigma]
  apply Matrix.inv_eq_left_inv
  simp [Matrix.mul_neg, Matrix.J_squared]

lemma g68k_bracket {n : ℕ} (S : Matrix (Phase n) (Phase n) ℝ) (a b : Phase n) :
    linearCanonicalBracket S a b = (S * sigma n * S.transpose) a b := by
  simp only [linearCanonicalBracket, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

@[simp] lemma g68k_s_ll (n : ℕ) (i j : Fin n) : sigma n (Sum.inl i) (Sum.inl j) = 0 := by
  simp [sigma]
@[simp] lemma g68k_s_rr (n : ℕ) (i j : Fin n) : sigma n (Sum.inr i) (Sum.inr j) = 0 := by
  simp [sigma]
@[simp] lemma g68k_s_lr (n : ℕ) (i j : Fin n) :
    sigma n (Sum.inl i) (Sum.inr j) = if i = j then 1 else 0 := by
  simp [sigma, Matrix.one_apply]
@[simp] lemma g68k_s_rl (n : ℕ) (i j : Fin n) :
    sigma n (Sum.inr i) (Sum.inl j) = -(if i = j then 1 else 0) := by
  simp [sigma, Matrix.one_apply]

lemma g68k_darboux {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsAlt) :
    ∀ k : ℕ, ∀ W : Submodule ℝ V, Module.finrank ℝ W = 2 * k →
      (∀ x ∈ W, (∀ y ∈ W, B x y = 0) → x = 0) →
      ∃ v : Phase k → V, (∀ a, v a ∈ W) ∧ ∀ a b, B (v a) (v b) = sigma k a b := by
  intro k
  induction k with
  | zero =>
    intro W _ _
    refine ⟨fun _ => 0, fun _ => W.zero_mem, fun a => ?_⟩
    rcases a with a | a <;> exact a.elim0
  | succ k ih =>
    intro W hW hnd
    have hne : W ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hW; omega
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
    -- decomposition
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
    -- dimension
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
    rw [hsup, hinf, finrank_bot, hPr, hW] at hdim
    obtain ⟨v', hv'W, hv'⟩ := ih W' (by omega) hnd'
    have hv'e : ∀ a, B e (v' a) = 0 := fun a => ((memW' _).1 (hv'W a)).2.1
    have hv'f : ∀ a, B f (v' a) = 0 := fun a => ((memW' _).1 (hv'W a)).2.2
    have hev' : ∀ a, B (v' a) e = 0 := fun a => by rw [← hB.neg_eq, hv'e, neg_zero]
    have hfv' : ∀ a, B (v' a) f = 0 := fun a => by rw [← hB.neg_eq, hv'f, neg_zero]
    let v : Phase (k + 1) → V := fun a => match a with
      | Sum.inl i => Fin.cases e (fun j => v' (Sum.inl j)) i
      | Sum.inr i => Fin.cases f (fun j => v' (Sum.inr j)) i
    refine ⟨v, ?_, ?_⟩
    · rintro (i | i) <;> refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [v, heW, hfW, ((memW' _).1 (hv'W _)).1]
    · rintro (i | i) (j | j) <;> refine Fin.cases ?_ (fun i' => ?_) i <;>
        refine Fin.cases ?_ (fun j' => ?_) j <;>
        simp [v, hee, hef, hfe, hff, hv'e, hv'f, hev', hfv', hv', Fin.succ_ne_zero,
          (Fin.succ_ne_zero _).symm]

lemma g68k_li {V : Type*} [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V) {k : ℕ}
    (v : Phase k → V) (hv : ∀ a b, B (v a) (v b) = sigma k a b) : LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have key : ∀ a, ∑ b, c b * sigma k a b = 0 := by
    intro a
    have := congrArg (B (v a)) hc
    simpa [map_sum, hv, mul_comm] using this
  rintro (i | i)
  · have := key (Sum.inr i)
    simpa [Fintype.sum_sum_type] using this
  · have := key (Sum.inl i)
    simpa [Fintype.sum_sum_type] using this



/-- PDF pp.7–8, (3.3)–(3.5): grouped and paired symplectic bases exist;
the pairing is preserved, with no Euclidean orthogonality claim. -/
theorem solution (n : ℕ) (hn : 0 < n)
    (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 2 * n) (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    (∃ b : Module.Basis (Phase n) ℝ V, ∀ i j, B (b i) (b j) = sigma n i j) ∧
    (∃ b : Module.Basis (Fin n × Bool) ℝ V, ∀ i j,
      B (b i) (b j) = sigma n
        (if i.2 then Sum.inr i.1 else Sum.inl i.1)
        (if j.2 then Sum.inr j.1 else Sum.inl j.1)) ∧
    (∀ S : Matrix (Phase n) (Phase n) ℝ, PreservesCanonicalForm S →
      ∀ x y : Phase n → ℝ,
        (∑ i, ∑ j, (Matrix.mulVec (S) x) i * sigma n i j * (Matrix.mulVec (S) y) j) =
          ∑ i, ∑ j, x i * sigma n i j * y j) := by
  obtain ⟨v, -, hv⟩ := g68k_darboux B hB n ⊤ (by rw [finrank_top]; exact hdim)
    (fun x _ hx => hnd.1 x (fun y => hx y Submodule.mem_top))
  have hcard : Fintype.card (Phase n) = Module.finrank ℝ V := by simp [hdim]; ring
  let b := basisOfLinearIndependentOfCardEqFinrank' v (g68k_li B v hv) hcard
  have hb : ∀ i, b i = v i := fun i => by simp [b, basisOfLinearIndependentOfCardEqFinrank']
  let eqv : Fin n × Bool ≃ Phase n :=
    { toFun := fun p => if p.2 then Sum.inr p.1 else Sum.inl p.1
      invFun := Sum.elim (fun i => (i, false)) (fun i => (i, true))
      left_inv := by rintro ⟨i, (_ | _)⟩ <;> rfl
      right_inv := by rintro (i | i) <;> rfl }
  refine ⟨⟨b, fun i j => by rw [hb, hb, hv]⟩, ⟨b.reindex eqv.symm, fun i j => ?_⟩, ?_⟩
  · simp only [Module.Basis.reindex_apply, Equiv.symm_symm, hb, hv]
    rfl
  · intro S hS x y
    rw [g68k_pres_iff, SymplecticGroup.mem_iff'] at hS
    have hS' : S.transpose * sigma n * S = sigma n := by
      rw [g68k_sigma]; simp [Matrix.mul_neg, Matrix.neg_mul, hS]
    have e1 : ∀ u w : Phase n → ℝ, ∑ i, ∑ j, u i * sigma n i j * w j =
        dotProduct u ((sigma n).mulVec w) := by
      intro u w
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rw [e1, e1, ← Matrix.vecMul_transpose S x, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, hS']



end
