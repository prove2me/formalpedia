-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.euler_passive_squeeze_passive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:41:20.859905+00:00
-- url     : https://prove2.me/submissions/ab38eeb2-70bf-4d66-aa49-bc266519b777

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41
noncomputable section
open scoped InnerProductSpace RealInnerProductSpace Matrix

namespace X5ED

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma ed_eigen (M : E →ₗ[ℝ] E) (hM : ∀ x y, ⟪M x, y⟫ = ⟪x, M y⟫) (W : Submodule ℝ E)
    (hW : ∀ x ∈ W, M x ∈ W) (hne : 0 < Module.finrank ℝ W) :
    ∃ e ∈ W, ⟪e, e⟫ = 1 ∧ ∃ c : ℝ, M e = c • e := by
  set T : W →ₗ[ℝ] W := M.restrict hW
  have hT : T.IsSymmetric := by
    intro x y
    simp only [T, Submodule.coe_inner, LinearMap.coe_restrict_apply]
    exact hM x y
  set b := hT.eigenvectorBasis rfl
  set i0 : Fin (Module.finrank ℝ W) := ⟨0, hne⟩
  refine ⟨(b i0 : E), (b i0).2, ?_, hT.eigenvalues rfl i0, ?_⟩
  · rw [← Submodule.coe_inner]; exact b.orthonormal.1 i0 |> fun h => by
      rw [real_inner_self_eq_norm_sq, h]; norm_num
  · have h5 := congrArg Subtype.val (hT.apply_eigenvectorBasis rfl i0)
    simp only [T, LinearMap.coe_restrict_apply, Submodule.coe_smul] at h5
    exact h5

lemma ed_core (J M : E →ₗ[ℝ] E) (hskew : ∀ x y, ⟪J x, y⟫ = -⟪x, J y⟫)
    (hJJ : ∀ x, J (J x) = -x) (hM : ∀ x y, ⟪M x, y⟫ = ⟪x, M y⟫)
    (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, M x⟫) (hMJ : ∀ x, M (J (M x)) = J x) :
    ∀ k : ℕ, ∀ W : Submodule ℝ E, (∀ x ∈ W, J x ∈ W) → (∀ x ∈ W, M x ∈ W) →
      Module.finrank ℝ W = 2 * k →
      ∃ e : Fin k → E, ∃ mu : Fin k → ℝ, (∀ i, e i ∈ W) ∧ (∀ i, 0 < mu i) ∧
        (∀ i, M (e i) = mu i • e i) ∧ (∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0) ∧
        (∀ i j, ⟪e i, J (e j)⟫ = 0) := by
  have hself : ∀ x, ⟪x, J x⟫ = 0 := by
    intro x
    have := hskew x x
    rw [real_inner_comm] at this
    linarith
  intro k
  induction k with
  | zero =>
    intro W _ _ _
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    intro W hJW hMW hdim
    obtain ⟨e, heW, hee, c, hc⟩ := ed_eigen M hM W hMW (by omega)
    have he0 : e ≠ 0 := fun h => by rw [h, inner_zero_left] at hee; norm_num at hee
    have hcpos : 0 < c := by
      have := hpos e he0
      rw [hc, inner_smul_right, hee, mul_one] at this
      exact this
    set f := J e with hf
    have hfW : f ∈ W := hJW e heW
    have hef : ⟪e, f⟫ = 0 := hself e
    have hfe : ⟪f, e⟫ = 0 := by rw [real_inner_comm]; exact hef
    have hff : ⟪f, f⟫ = 1 := by
      rw [hf, hskew, hJJ, inner_neg_right, neg_neg, hee]
    have hMf : M f = c⁻¹ • f := by
      have h1 : M (c⁻¹ • e) = e := by
        rw [map_smul, hc, smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]
      have := hMJ (c⁻¹ • e)
      rw [h1, map_smul] at this
      rw [hf, this]
    set W' : Submodule ℝ E := W ⊓ LinearMap.ker (innerₛₗ ℝ e) ⊓ LinearMap.ker (innerₛₗ ℝ f)
      with hW'
    have memW' : ∀ x, x ∈ W' ↔ x ∈ W ∧ ⟪e, x⟫ = 0 ∧ ⟪f, x⟫ = 0 := by
      intro x; simp [hW', and_assoc]
    have hJW' : ∀ x ∈ W', J x ∈ W' := by
      intro x hx
      rw [memW'] at hx ⊢
      refine ⟨hJW _ hx.1, ?_, ?_⟩
      · have := hskew e x; rw [← hf, hx.2.2] at this; linarith
      · have := hskew f x
        rw [hf, hJJ, inner_neg_left, hx.2.1] at this; rw [← hf] at this; linarith
    have hMW' : ∀ x ∈ W', M x ∈ W' := by
      intro x hx
      rw [memW'] at hx ⊢
      refine ⟨hMW _ hx.1, ?_, ?_⟩
      · rw [← hM, hc, inner_smul_left, hx.2.1, mul_zero]
      · rw [← hM, hMf, inner_smul_left, hx.2.2, mul_zero]
    have dec : ∀ w ∈ W, w - ⟪e, w⟫ • e - ⟪f, w⟫ • f ∈ W' := by
      intro w hw
      rw [memW']
      refine ⟨W.sub_mem (W.sub_mem hw (W.smul_mem _ heW)) (W.smul_mem _ hfW), ?_, ?_⟩
      · simp only [inner_sub_right, inner_smul_right, hee, hef]; ring
      · simp only [inner_sub_right, inner_smul_right, hff, hfe]; ring
    set P : Submodule ℝ E := Submodule.span ℝ (Set.range ![e, f]) with hP
    have hli : LinearIndependent ℝ ![e, f] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
      have h1 := congrArg (fun x => ⟪e, x⟫) hg
      have h2 := congrArg (fun x => ⟪f, x⟫) hg
      simp only [inner_add_right, inner_smul_right, hee, hef, hfe, hff, inner_zero_right] at h1 h2
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
      obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx2
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hx1 ⊢
      have h1 := hx1.2.1
      have h2 := hx1.2.2
      simp only [inner_add_right, inner_smul_right, hee, hef, hfe, hff] at h1 h2
      have c0 : g 0 = 0 := by linarith
      have c1 : g 1 = 0 := by linarith
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
        have : w = (w - ⟪e, w⟫ • e - ⟪f, w⟫ • f) + (⟪e, w⟫ • e + ⟪f, w⟫ • f) := by abel
        rw [this]
        apply Submodule.add_mem_sup (dec w hw)
        apply P.add_mem
        · exact P.smul_mem _ (Submodule.subset_span ⟨0, by simp⟩)
        · exact P.smul_mem _ (Submodule.subset_span ⟨1, by simp⟩)
    have hdim' := Submodule.finrank_sup_add_finrank_inf_eq W' P
    rw [hsup, hinf, finrank_bot, hPr, hdim] at hdim'
    obtain ⟨e', mu', he'W, hmu', hMe', hG', hJ'⟩ := ih W' hJW' hMW' (by omega)
    have hee' : ∀ j, ⟪e, e' j⟫ = 0 := fun j => ((memW' _).1 (he'W j)).2.1
    have hfe' : ∀ j, ⟪f, e' j⟫ = 0 := fun j => ((memW' _).1 (he'W j)).2.2
    have he'e : ∀ j, ⟪e' j, e⟫ = 0 := fun j => by rw [real_inner_comm]; exact hee' j
    have he'f : ∀ j, ⟪e' j, f⟫ = 0 := fun j => by rw [real_inner_comm]; exact hfe' j
    have heJe' : ∀ j, ⟪e, J (e' j)⟫ = 0 := fun j => by
      have := hskew e (e' j); rw [← hf, hfe' j] at this; linarith
    refine ⟨Fin.cons e e', Fin.cons c mu', ?_, ?_, ?_, ?_, ?_⟩
    · intro i; refine Fin.cases ?_ (fun j => ?_) i
      · simpa using heW
      · simpa using ((memW' _).1 (he'W j)).1
    · intro i; refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hcpos
      · simpa using hmu' j
    · intro i; refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hc
      · simpa using hMe' j
    · have hn : ‖e‖ = 1 := by
        have h := hee; rw [real_inner_self_eq_norm_sq] at h
        have := norm_nonneg e; nlinarith
      intro i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
        simp [hn, hee, hee', he'e, hG', Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
        simp [← hf, hef, heJe', he'f, hJ']

end X5ED

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace Matrix

namespace X5MGP

abbrev QuadratureIndex (n : ℕ) := Fin n × Fin 2

def interleavedSymplecticForm (n : ℕ) : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ :=
  fun i j => if i.1 = j.1 then
    (if i.2 = j.2 then 0 else if i.2 = 0 then 1 else -1) else 0

def isSymplectic {n : ℕ} (S : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ) : Prop :=
  S * interleavedSymplecticForm n * S.transpose = interleavedSymplecticForm n

def williamsonDiagonal {n : ℕ} (nu : Fin n → ℝ) :
    Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ :=
  Matrix.diagonal (fun i => nu i.1)

end X5MGP

lemma wl_eigen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E) (hskew : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) (W : Submodule ℝ E)
    (hW : ∀ x ∈ W, A x ∈ W) (hne : 0 < Module.finrank ℝ W) :
    ∃ e ∈ W, e ≠ 0 ∧ ∃ c : ℝ, A (A e) = c • e := by
  have h2 : ∀ x ∈ W, (A ∘ₗ A) x ∈ W := fun x hx => hW _ (hW x hx)
  set T : W →ₗ[ℝ] W := (A ∘ₗ A).restrict h2
  have hT : T.IsSymmetric := by
    intro x y
    simp only [T, Submodule.coe_inner, LinearMap.coe_restrict_apply, LinearMap.comp_apply]
    rw [hskew, hskew, neg_neg]
  have : Nontrivial W := Module.nontrivial_of_finrank_pos hne
  obtain ⟨v, hv, hv0⟩ := (hT.hasEigenvalue_iSup_of_finiteDimensional).exists_hasEigenvector
  refine ⟨v, v.2, fun h => hv0 (Subtype.ext h), ?_⟩
  refine ⟨(⨆ x : {x : W // x ≠ 0}, RCLike.re ⟪T x, x⟫ / ‖(x : W)‖ ^ 2), ?_⟩
  have := Module.End.mem_eigenspace_iff.1 hv
  have := congrArg Subtype.val this
  simpa [T] using this

open X5MGP in
lemma wl_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E) (hskew : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) (hinj : ∀ x, A x = 0 → x = 0) :
    ∀ k : ℕ, ∀ W : Submodule ℝ E, (∀ x ∈ W, A x ∈ W) → Module.finrank ℝ W = 2 * k →
      ∃ v : Fin k × Fin 2 → E, ∃ nu : Fin k → ℝ, (∀ a, v a ∈ W) ∧ (∀ i, 0 < nu i) ∧
        (∀ a b, ⟪v a, v b⟫ = williamsonDiagonal nu a b) ∧
        (∀ a b, ⟪v a, A (v b)⟫ = interleavedSymplecticForm k a b) := by
  have hself : ∀ x, ⟪x, A x⟫ = 0 := by
    intro x
    have := hskew x x
    rw [real_inner_comm] at this
    linarith
  intro k
  induction k with
  | zero =>
    intro W _ _
    refine ⟨fun _ => 0, fun _ => 0, fun _ => W.zero_mem, fun i => i.elim0, fun a => a.1.elim0,
      fun a => a.1.elim0⟩
  | succ k ih =>
    intro W hW hdim
    obtain ⟨e0, he0W, he00, c, hc⟩ := wl_eigen A hskew W hW (by rw [hdim]; omega)
    have hAe0 : A e0 ≠ 0 := fun h => he00 (hinj _ h)
    have hpos1 : 0 < ⟪A e0, A e0⟫ := real_inner_self_pos.2 hAe0
    have hpos2 : 0 < ⟪e0, e0⟫ := real_inner_self_pos.2 he00
    have hrel : ⟪A e0, A e0⟫ = -c * ⟪e0, e0⟫ := by
      rw [hskew, hc, inner_smul_right]; ring
    have hcneg : 0 < -c := by
      by_contra h; push Not at h; nlinarith
    set s := Real.sqrt (-c) with hs
    have hspos : 0 < s := Real.sqrt_pos.2 hcneg
    have hss : s * s = -c := Real.mul_self_sqrt hcneg.le
    set r := (Real.sqrt (s * ⟪e0, e0⟫))⁻¹ with hr
    have hrr : r * r * ⟪e0, e0⟫ = s⁻¹ := by
      have h1 := Real.mul_self_sqrt (mul_pos hspos hpos2).le
      rw [hr]
      have h3 : 0 < Real.sqrt (s * ⟪e0, e0⟫) := Real.sqrt_pos.2 (mul_pos hspos hpos2)
      field_simp
      nlinarith
    set e := r • e0 with he
    have heW : e ∈ W := W.smul_mem _ he0W
    have hAAe : A (A e) = -(s * s) • e := by
      rw [he, map_smul, map_smul, hc, hss, neg_neg, smul_comm]
    have hee : ⟪e, e⟫ = s⁻¹ := by
      rw [he, inner_smul_left, inner_smul_right]; simpa [mul_assoc] using hrr
    set f := -(s⁻¹) • A e with hf
    have hfW : f ∈ W := W.smul_mem _ (hW _ heW)
    have hAe : A e = -s • f := by
      rw [hf, smul_smul]; field_simp; simp
    have hAf : A f = s • e := by
      rw [hf, map_smul, hAAe, smul_smul]; congr 1; field_simp
    have hxAe : ∀ x, ⟪x, A e⟫ = -s * ⟪x, f⟫ := fun x => by rw [hAe, inner_smul_right]
    have hxAf : ∀ x, ⟪x, A f⟫ = s * ⟪x, e⟫ := fun x => by rw [hAf, inner_smul_right]
    have heAx : ∀ x, ⟪e, A x⟫ = s * ⟪f, x⟫ := fun x => by
      have := hskew e x; rw [hAe, inner_smul_left] at this; simp at this; linarith
    have hfAx : ∀ x, ⟪f, A x⟫ = -s * ⟪e, x⟫ := fun x => by
      have := hskew f x; rw [hAf, inner_smul_left] at this; simp at this; linarith
    have hef : ⟪e, f⟫ = 0 := by
      have := hxAe e; rw [hself] at this
      have : s * ⟪e, f⟫ = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact h
    have hfe : ⟪f, e⟫ = 0 := by rw [real_inner_comm]; exact hef
    have hff : ⟪f, f⟫ = s⁻¹ := by
      have h1 := hxAf f
      have h2 := hfAx f
      rw [hAf, inner_smul_right] at h2
      have h3 := hxAe f
      -- ⟪f, A f⟫ = 0 and ⟪f, A e⟫ = -s⟪f,f⟫ ; also ⟪f, A e⟫ = ⟪f, -s f⟫
      have h4 : ⟪f, A e⟫ = -1 := by
        have := hfAx e
        rw [hee] at this; rw [this]; field_simp
      rw [h4] at h3
      field_simp; linarith
    -- complement
    set W' : Submodule ℝ E := W ⊓ LinearMap.ker (innerₛₗ ℝ e) ⊓ LinearMap.ker (innerₛₗ ℝ f)
      with hW'
    have memW' : ∀ x, x ∈ W' ↔ x ∈ W ∧ ⟪e, x⟫ = 0 ∧ ⟪f, x⟫ = 0 := by
      intro x; simp [hW', and_assoc]
    have hW'inv : ∀ x ∈ W', A x ∈ W' := by
      intro x hx
      rw [memW'] at hx ⊢
      refine ⟨hW _ hx.1, ?_, ?_⟩
      · rw [heAx, hx.2.2, mul_zero]
      · rw [hfAx, hx.2.1, mul_zero]
    have dec : ∀ w ∈ W, w - (s * ⟪e, w⟫) • e - (s * ⟪f, w⟫) • f ∈ W' := by
      intro w hw
      rw [memW']
      refine ⟨W.sub_mem (W.sub_mem hw (W.smul_mem _ heW)) (W.smul_mem _ hfW), ?_, ?_⟩
      · simp only [inner_sub_right, inner_smul_right, hee, hef]; field_simp; ring
      · simp only [inner_sub_right, inner_smul_right, hff, hfe]; field_simp; ring
    set P : Submodule ℝ E := Submodule.span ℝ (Set.range ![e, f]) with hP
    have hli : LinearIndependent ℝ ![e, f] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
      have h1 := congrArg (fun x => ⟪e, x⟫) hg
      have h2 := congrArg (fun x => ⟪f, x⟫) hg
      simp only [inner_add_right, inner_smul_right, hee, hef, hfe, hff, inner_zero_right] at h1 h2
      have hsi : 0 < s⁻¹ := inv_pos.2 hspos
      intro i; fin_cases i
      · simp; nlinarith
      · simp; nlinarith
    have hPr : Module.finrank ℝ P = 2 := by
      rw [hP, finrank_span_eq_card hli]; simp
    have hinf : W' ⊓ P = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
      rw [memW'] at hx1
      obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx2
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hx1 ⊢
      have h1 := hx1.2.1
      have h2 := hx1.2.2
      simp only [inner_add_right, inner_smul_right, hee, hef, hfe, hff] at h1 h2
      have hsi : 0 < s⁻¹ := inv_pos.2 hspos
      have c0 : g 0 = 0 := by nlinarith
      have c1 : g 1 = 0 := by nlinarith
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
        have : w = (w - (s * ⟪e, w⟫) • e - (s * ⟪f, w⟫) • f) +
            ((s * ⟪e, w⟫) • e + (s * ⟪f, w⟫) • f) := by abel
        rw [this]
        apply Submodule.add_mem_sup (dec w hw)
        apply P.add_mem
        · exact P.smul_mem _ (Submodule.subset_span ⟨0, by simp⟩)
        · exact P.smul_mem _ (Submodule.subset_span ⟨1, by simp⟩)
    have hdim' := Submodule.finrank_sup_add_finrank_inf_eq W' P
    rw [hsup, hinf, finrank_bot, hPr, hdim] at hdim'
    obtain ⟨v', nu', hv'W, hnu', hv'G, hv'O⟩ := ih W' hW'inv (by omega)
    have hev' : ∀ a, ⟪e, v' a⟫ = 0 := fun a => ((memW' _).1 (hv'W a)).2.1
    have hfv' : ∀ a, ⟪f, v' a⟫ = 0 := fun a => ((memW' _).1 (hv'W a)).2.2
    have hv'e : ∀ a, ⟪v' a, e⟫ = 0 := fun a => by rw [real_inner_comm]; exact hev' a
    have hv'f : ∀ a, ⟪v' a, f⟫ = 0 := fun a => by rw [real_inner_comm]; exact hfv' a
    have hAee : ⟪e, A e⟫ = 0 := hself e
    have hAff : ⟪f, A f⟫ = 0 := hself f
    have hAef : ⟪e, A f⟫ = 1 := by rw [hxAf, hee]; field_simp
    have hAfe : ⟪f, A e⟫ = -1 := by rw [hfAx, hee]; field_simp
    let v : Fin (k + 1) × Fin 2 → E := fun a => Fin.cases (![e, f] a.2) (fun j => v' (j, a.2)) a.1
    refine ⟨v, Fin.cases s⁻¹ nu', ?_, ?_, ?_, ?_⟩
    · rintro ⟨i, t⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · fin_cases t <;> simp [v, heW, hfW]
      · simp only [v, Fin.cases_succ]; exact ((memW' _).1 (hv'W _)).1
    · intro i; refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hspos
      · simpa using hnu' j
    · have hee2 : ‖e‖ ^ 2 = s⁻¹ := by rw [← real_inner_self_eq_norm_sq, hee]
      have hff2 : ‖f‖ ^ 2 = s⁻¹ := by rw [← real_inner_self_eq_norm_sq, hff]
      rintro ⟨i, t⟩ ⟨j, u⟩
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
        fin_cases t <;> fin_cases u <;>
        simp [v, williamsonDiagonal, Matrix.diagonal_apply, hee2, hff2, hef, hfe, hff, hev', hfv', hv'e,
          hv'f, hv'G, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]
    · rintro ⟨i, t⟩ ⟨j, u⟩
      have hsne : s ≠ 0 := hspos.ne'
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
        fin_cases t <;> fin_cases u <;>
        simp [v, interleavedSymplecticForm, hAee, hAff, hAef, hAfe, heAx, hfAx, hxAe, hxAf,
          hev', hfv', hv'e, hv'f, hv'O, hsne, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

open X5MGP in
lemma wl_euclid (n : ℕ) (M : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ)
    (hMt : M.transpose = -M) (hM : M.det ≠ 0) :
    ∃ U : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ, ∃ nu : Fin n → ℝ, (∀ k, 0 < nu k) ∧
      U.transpose * U = williamsonDiagonal nu ∧
      U.transpose * M * U = interleavedSymplecticForm n := by
  let A : EuclideanSpace ℝ (QuadratureIndex n) →ₗ[ℝ] EuclideanSpace ℝ (QuadratureIndex n) :=
    Matrix.toLpLin 2 2 M
  have hin : ∀ x y : EuclideanSpace ℝ (QuadratureIndex n),
      ⟪x, A y⟫ = WithLp.ofLp x ⬝ᵥ (M *ᵥ WithLp.ofLp y) := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply]
    simp [dotProduct_comm]
  have hskew : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫ := by
    intro x y
    rw [real_inner_comm, hin, hin, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hMt,
      Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]
  have hinj : ∀ x, A x = 0 → x = 0 := by
    intro x hx
    have h1 : M *ᵥ WithLp.ofLp x = 0 := by
      have := congrArg WithLp.ofLp hx
      simpa [A, Matrix.toLpLin_apply] using this
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hM h1
    have := congrArg (WithLp.toLp 2) h2
    simpa using this
  obtain ⟨v, nu, -, hnu, hG, hO⟩ := wl_core A hskew hinj n ⊤ (fun _ _ => Submodule.mem_top)
    (by rw [finrank_top, finrank_euclideanSpace]; simp [mul_comm])
  refine ⟨Matrix.of fun i a => WithLp.ofLp (v a) i, nu, hnu, ?_, ?_⟩
  · ext a b
    rw [← hG a b, EuclideanSpace.inner_eq_star_dotProduct]
    simp [Matrix.mul_apply, dotProduct, mul_comm]
  · ext a b
    rw [← hO a b, hin, Matrix.mul_assoc]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

namespace X5Williamson
open X5MGP

lemma wl_omega_t (n : ℕ) : (interleavedSymplecticForm n).transpose = -interleavedSymplecticForm n := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;> simp [interleavedSymplecticForm, eq_comm] <;> split_ifs <;> norm_num

lemma wl_omega_sq (n : ℕ) :
    interleavedSymplecticForm n * interleavedSymplecticForm n = -1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;>
    simp [interleavedSymplecticForm, Matrix.one_apply, Finset.sum_ite_eq, eq_comm] <;>
    split_ifs <;> norm_num

lemma wl_omega_det (n : ℕ) : (interleavedSymplecticForm n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (wl_omega_sq n)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_neg, Matrix.det_one] at this
  simp at this

lemma wl_factor {a : Type*} [Fintype a] [DecidableEq a] (V : Matrix a a ℝ) (hV : V.PosDef) :
    ∃ B : Matrix a a ℝ, V = B * B.transpose ∧ B.det ≠ 0 := by
  have hM := hV.isHermitian
  have hst : ∀ X : Matrix a a ℝ, star X = X.transpose := fun X => by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  set U : Matrix a a ℝ := (hM.eigenvectorUnitary : Matrix a a ℝ)
  set ev := hM.eigenvalues
  have hev : ∀ i, 0 < ev i := fun i => hV.eigenvalues_pos i
  have hVU : V = U * Matrix.diagonal ev * U.transpose := by
    conv_lhs => rw [hM.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, hst]
    congr 2
  set B : Matrix a a ℝ := U * Matrix.diagonal (fun i => Real.sqrt (ev i)) with hB
  have hBB : V = B * B.transpose := by
    rw [hVU, hB, Matrix.transpose_mul, Matrix.diagonal_transpose]
    have : Matrix.diagonal (fun i => Real.sqrt (ev i)) * Matrix.diagonal (fun i => Real.sqrt (ev i)) =
        Matrix.diagonal ev := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1; funext i; exact Real.mul_self_sqrt (hev i).le
    rw [← this]; simp only [Matrix.mul_assoc]
  refine ⟨B, hBB, fun h => ?_⟩
  have := hV.det_pos
  rw [hBB, Matrix.det_mul, h, zero_mul] at this
  exact lt_irrefl _ this

end X5Williamson

open X5MGP X5Williamson in
theorem wl_williamson (n : ℕ)
    (V : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ) (hV : V.PosDef) :
    ∃ nu : Fin n → ℝ, ∃ S : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ,
      (∀ k, 0 < nu k) ∧ isSymplectic S ∧
      V = S * williamsonDiagonal nu * S.transpose := by
  set Om := interleavedSymplecticForm n with hOm
  obtain ⟨B, hVB, hB⟩ := wl_factor V hV
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  set M := B⁻¹ * Om * B⁻¹.transpose with hMdef
  have hMt : M.transpose = -M := by
    rw [hMdef, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hOm,
      wl_omega_t]
    simp [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
  have hBi : B⁻¹.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det B hBu).ne_zero
  have hMdet : M.det ≠ 0 := by
    rw [hMdef, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hBi (wl_omega_det n)) hBi
  obtain ⟨U, nu, hnu, hUU, hUO⟩ := wl_euclid n M hMt hMdet
  have hU : U.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hUO
    rw [Matrix.det_mul, Matrix.det_mul, h, mul_zero] at this
    exact wl_omega_det n this.symm
  have hUu : IsUnit U.det := isUnit_iff_ne_zero.2 hU
  have e1 : U⁻¹.transpose * U.transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hUu, Matrix.transpose_one]
  have e2 : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv _ hUu
  have e3 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBu
  have e4 : B⁻¹.transpose * B.transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hBu, Matrix.transpose_one]
  refine ⟨nu, B * U⁻¹.transpose, hnu, ?_, ?_⟩
  · unfold isSymplectic
    rw [← hOm]
    calc B * U⁻¹.transpose * Om * (B * U⁻¹.transpose).transpose
        = B * (U⁻¹.transpose * U.transpose) * M * (U * U⁻¹) * B.transpose := by
          rw [Matrix.transpose_mul, Matrix.transpose_transpose]
          conv_lhs => rw [hOm, ← hUO]
          simp only [Matrix.mul_assoc]
      _ = (B * B⁻¹) * Om * (B⁻¹.transpose * B.transpose) := by
          rw [e1, e2, hMdef]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Om := by rw [e3, e4, Matrix.one_mul, Matrix.mul_one]
  · rw [← hUU]
    calc V = B * B.transpose := hVB
      _ = B * (U⁻¹.transpose * U.transpose) * (U * U⁻¹) * B.transpose := by
          rw [e1, e2, Matrix.mul_one, Matrix.mul_one]
      _ = B * U⁻¹.transpose * (U.transpose * U) * (B * U⁻¹.transpose).transpose := by
          rw [Matrix.transpose_mul, Matrix.transpose_transpose]
          simp only [Matrix.mul_assoc]



end

noncomputable section
open scoped Matrix ComplexOrder

namespace X5MGP
open QAlgorithms.Papers.Independent.Dependency50.P10 Matrix

variable {n : ℕ}

def ep (n : ℕ) : QuadratureIndex n ≃ Phase n where
  toFun p := if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  invFun := Sum.elim (fun i => (i, 0)) (fun i => (i, 1))
  left_inv := by rintro ⟨i, a⟩; fin_cases a <;> rfl
  right_inv := by rintro (i | i) <;> rfl

lemma ep_sigma (n : ℕ) : (sigma n).submatrix (ep n) (ep n) = interleavedSymplecticForm n := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [ep, sigma, interleavedSymplecticForm, Matrix.one_apply, eq_comm] <;> split_ifs <;> simp

lemma ep_thermal (D : Fin n → ℝ) :
    (thermalCovariance D).submatrix (ep n) (ep n) = williamsonDiagonal D := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [ep, thermalCovariance, williamsonDiagonal, diagonal_apply, eq_comm]

lemma sigma_t (n : ℕ) : (sigma n)ᵀ = -sigma n := by
  simp [sigma, fromBlocks_transpose, fromBlocks_neg]

lemma sigma_sq (n : ℕ) : sigma n * sigma n = -1 := by
  simp [sigma, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

lemma sigma_det (n : ℕ) : (sigma n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (sigma_sq n)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_neg, Matrix.det_one] at this
  simp at this

theorem williamson_phase (G : Matrix (Phase n) (Phase n) ℝ) (hG : G.PosDef) :
    ∃ D : Fin n → ℝ, ∃ T : Matrix (Phase n) (Phase n) ℝ, (∀ k, 0 < D k) ∧
      T * sigma n * Tᵀ = sigma n ∧ G = T * thermalCovariance D * Tᵀ := by
  obtain ⟨nu, S, hnu, hS, hV⟩ := wl_williamson n (G.submatrix (ep n) (ep n))
    (hG.submatrix (ep n).injective)
  set e := ep n
  refine ⟨nu, S.submatrix e.symm e.symm, hnu, ?_, ?_⟩
  · have h1 : sigma n = (interleavedSymplecticForm n).submatrix e.symm e.symm := by
      rw [← ep_sigma]; simp [e]
    unfold isSymplectic at hS
    rw [h1, transpose_submatrix, submatrix_mul_equiv _ _ _ e.symm,
      submatrix_mul_equiv _ _ _ e.symm, hS]
  · have h1 : thermalCovariance nu = (williamsonDiagonal nu).submatrix e.symm e.symm := by
      rw [← ep_thermal]; simp [e]
    have h2 : G = (G.submatrix e e).submatrix e.symm e.symm := by simp
    rw [h1, h2, hV, transpose_submatrix, submatrix_mul_equiv _ _ _ e.symm,
      submatrix_mul_equiv _ _ _ e.symm]

end X5MGP

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace Matrix

namespace X5ED
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)
open QAlgorithms.Papers.Independent.Claimed50.P41
open Matrix

variable {n : ℕ}

lemma symp_t (M : Matrix (Phase n) (Phase n) ℝ) (h : Mᵀ * sigma n * M = sigma n) :
    M * sigma n * Mᵀ = sigma n := by
  have h1 : (-(sigma n * Mᵀ * sigma n)) * M = 1 := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᵀ, h,
      X5MGP.sigma_sq, neg_neg]
  have h2 := mul_eq_one_comm.mp h1
  have e1 : M * sigma n * Mᵀ * sigma n = -1 := by
    have := h2
    rw [Matrix.mul_neg] at this
    simp only [Matrix.mul_assoc] at this ⊢
    exact neg_eq_iff_eq_neg.mp this
  calc M * sigma n * Mᵀ = M * sigma n * Mᵀ * sigma n * (-sigma n) := by
        rw [Matrix.mul_neg, Matrix.mul_assoc (M * sigma n * Mᵀ), X5MGP.sigma_sq, Matrix.mul_neg,
          Matrix.mul_one, neg_neg]
    _ = sigma n := by rw [e1]; simp

lemma sq_symp (κ : Fin n → ℝ) (hκ : ∀ i, κ i ≠ 0) :
    squeezeMatrix κ * sigma n * (squeezeMatrix κ)ᵀ = sigma n := by
  simp only [squeezeMatrix, sigma, fromBlocks_transpose, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [diagonal_apply, one_apply] <;> split_ifs <;> simp_all

lemma sq_mul (κ : Fin n → ℝ) (hκ : ∀ i, κ i ≠ 0) :
    squeezeMatrix (fun i => (κ i)⁻¹) * squeezeMatrix κ = 1 := by
  simp only [squeezeMatrix, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> ext i j <;> simp [diagonal_apply, one_apply] <;> split_ifs <;> simp_all

lemma sq_mul_gen (a b : Fin n → ℝ) :
    squeezeMatrix a * squeezeMatrix b = squeezeMatrix (fun i => a i * b i) := by
  simp only [squeezeMatrix, fromBlocks_multiply, diagonal_mul_diagonal, mul_inv]
  simp

lemma sq_one : squeezeMatrix (fun _ : Fin n => (1 : ℝ)) = 1 := by
  simp [squeezeMatrix, ← fromBlocks_one]

lemma sq_t (a : Fin n → ℝ) : (squeezeMatrix a)ᵀ = squeezeMatrix a := by
  simp [squeezeMatrix, fromBlocks_transpose]

theorem ed_main (S : Matrix (Phase n) (Phase n) ℝ) (hS : S * sigma n * Sᵀ = sigma n) :
    ∃ K L : Matrix (Phase n) (Phase n) ℝ, ∃ kappa : Fin n → ℝ,
      IsPassive K ∧ IsPassive L ∧ (∀ i, 0 < kappa i) ∧
      IsPositiveSymplectic (squeezeMatrix kappa) ∧ S = K * squeezeMatrix kappa * L := by
  have hSt : Sᵀ * sigma n * S = sigma n := by
    have := symp_t Sᵀ (by rw [transpose_transpose]; exact hS)
    rwa [transpose_transpose] at this
  have hdetS : S.det ≠ 0 := by
    intro h0
    have := congrArg det hS
    rw [det_mul, det_mul, det_transpose, h0, zero_mul, zero_mul] at this
    exact X5MGP.sigma_det n this.symm
  set Mm := Sᵀ * S
  have hMmt : Mmᵀ = Mm := by simp [Mm, transpose_mul]
  have hMJM : Mm * (-sigma n) * Mm = -sigma n := by
    simp only [Mm, Matrix.mul_neg, Matrix.neg_mul]
    congr 1
    calc Sᵀ * S * sigma n * (Sᵀ * S) = Sᵀ * (S * sigma n * Sᵀ) * S := by simp only [Matrix.mul_assoc]
      _ = sigma n := by rw [hS, hSt]
  -- Euclidean setup
  have hin : ∀ (X : Matrix (Phase n) (Phase n) ℝ) (x y : EuclideanSpace ℝ (Phase n)),
      ⟪x, Matrix.toLpLin 2 2 X y⟫ = WithLp.ofLp x ⬝ᵥ (X *ᵥ WithLp.ofLp y) := by
    intro X x y
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply]
    simp [dotProduct_comm]
  have hsymm : ∀ (X : Matrix (Phase n) (Phase n) ℝ) (x y : EuclideanSpace ℝ (Phase n)),
      ⟪Matrix.toLpLin 2 2 X x, y⟫ = WithLp.ofLp x ⬝ᵥ (Xᵀ *ᵥ WithLp.ofLp y) := by
    intro X x y
    rw [real_inner_comm, hin, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      dotProduct_comm]
  have happ : ∀ (X : Matrix (Phase n) (Phase n) ℝ) (x : EuclideanSpace ℝ (Phase n)),
      WithLp.ofLp (Matrix.toLpLin 2 2 X x) = X *ᵥ WithLp.ofLp x := by
    intro X x; rw [Matrix.toLpLin_apply]
  have hext : ∀ x y : EuclideanSpace ℝ (Phase n), WithLp.ofLp x = WithLp.ofLp y → x = y :=
    fun x y h => by simpa using congrArg (WithLp.toLp 2) h
  set J := Matrix.toLpLin 2 2 (-sigma n)
  set Mo := Matrix.toLpLin 2 2 Mm
  have hskew : ∀ x y, ⟪J x, y⟫ = -⟪x, J y⟫ := by
    intro x y
    rw [hsymm, hin, transpose_neg, X5MGP.sigma_t, neg_neg, Matrix.neg_mulVec, dotProduct_neg,
      neg_neg]
  have hJJ : ∀ x, J (J x) = -x := by
    intro x; apply hext
    simp [J, happ, Matrix.mulVec_mulVec, X5MGP.sigma_sq, Matrix.neg_mulVec]
  have hMs : ∀ x y, ⟪Mo x, y⟫ = ⟪x, Mo y⟫ := by
    intro x y; rw [hsymm, hin, hMmt]
  have hpos : ∀ x, x ≠ 0 → 0 < ⟪x, Mo x⟫ := by
    intro x hx
    rw [hin]
    have hSx : S *ᵥ WithLp.ofLp x ≠ 0 := by
      intro h0
      apply hx; apply hext
      rw [Matrix.eq_zero_of_mulVec_eq_zero hdetS h0]; rfl
    have : WithLp.ofLp x ⬝ᵥ (Mm *ᵥ WithLp.ofLp x) =
        (S *ᵥ WithLp.ofLp x) ⬝ᵥ (S *ᵥ WithLp.ofLp x) := by
      simp only [Mm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [this]
    have := (dotProduct_self_star_pos_iff (v := S *ᵥ WithLp.ofLp x)).mpr hSx
    simpa using this
  have hMJ : ∀ x, Mo (J (Mo x)) = J x := by
    intro x; apply hext
    simp only [J, Mo, happ, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hMJM]
  obtain ⟨e, mu, -, hmu, hMe, hG, hJe⟩ := ed_core J Mo hskew hJJ hMs hpos hMJ n ⊤
    (fun _ _ => Submodule.mem_top) (fun _ _ => Submodule.mem_top)
    (by rw [finrank_top, finrank_euclideanSpace]; simp; ring)
  have hJe' : ∀ i j, ⟪J (e i), e j⟫ = 0 := fun i j => by rw [hskew, hJe]; simp
  have hJJe : ∀ i j, ⟪J (e i), J (e j)⟫ = if i = j then 1 else 0 := fun i j => by
    rw [hskew, hJJ, inner_neg_right, neg_neg, hG]
  have hMJe : ∀ j, Mo (J (e j)) = (mu j)⁻¹ • J (e j) := by
    intro j
    have h1 : Mo ((mu j)⁻¹ • e j) = e j := by
      rw [map_smul, hMe, smul_smul, inv_mul_cancel₀ (hmu j).ne', one_smul]
    have := hMJ ((mu j)⁻¹ • e j)
    rw [h1, map_smul] at this
    exact this
  have hJneg : Matrix.toLpLin 2 2 (sigma n) = -J := by
    simp only [J, map_neg, neg_neg]
  set col : Phase n → EuclideanSpace ℝ (Phase n) := Sum.elim e (fun i => J (e i))
  set O : Matrix (Phase n) (Phase n) ℝ := Matrix.of fun r a => WithLp.ofLp (col a) r
  have hO : ∀ (X : Matrix (Phase n) (Phase n) ℝ) a b,
      (Oᵀ * X * O) a b = ⟪col a, Matrix.toLpLin 2 2 X (col b)⟫ := by
    intro X a b
    rw [hin, Matrix.mul_assoc]
    simp [O, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hOO : Oᵀ * O = 1 := by
    ext a b
    have := hO 1 a b
    rw [Matrix.mul_one] at this
    rw [this, Matrix.toLpLin_one, LinearMap.id_apply]
    rcases a with i | i <;> rcases b with j | j <;>
      simp [col, hG, hJe, hJe', hJJe, one_apply]
  have hOsig : Oᵀ * sigma n * O = sigma n := by
    ext a b
    rw [hO, hJneg, LinearMap.neg_apply, inner_neg_right]
    rcases a with i | i <;> rcases b with j | j <;>
      simp [col, sigma, hJJ, hG, hJe, hJe', hJJe, one_apply]
  have hOM : Oᵀ * Mm * O = squeezeMatrix mu := by
    ext a b
    rw [hO]
    rcases a with i | i <;> rcases b with j | j <;>
      simp [col, squeezeMatrix, Mo, hMe, hMJe, inner_smul_right, hG, hJe, hJe', hJJe,
        diagonal_apply] <;> split_ifs <;> simp_all
  have hOOt : O * Oᵀ = 1 := mul_eq_one_comm.mp hOO
  set κ : Fin n → ℝ := fun i => Real.sqrt (mu i)
  have hκ : ∀ i, 0 < κ i := fun i => Real.sqrt_pos.mpr (hmu i)
  have hκ2 : ∀ i, κ i * κ i = mu i := fun i => Real.mul_self_sqrt (hmu i).le
  set Dinv := squeezeMatrix (fun i => (κ i)⁻¹)
  have hDD : Dinv * squeezeMatrix κ = 1 := by
    rw [sq_mul_gen, ← sq_one]; congr 1; funext i; exact inv_mul_cancel₀ (hκ i).ne'
  have hOsig' : O * sigma n * Oᵀ = sigma n := by
    calc O * sigma n * Oᵀ = O * (Oᵀ * sigma n * O) * Oᵀ := by rw [hOsig]
      _ = (O * Oᵀ) * sigma n * (O * Oᵀ) := by simp only [Matrix.mul_assoc]
      _ = sigma n := by rw [hOOt]; simp
  refine ⟨S * O * Dinv, Oᵀ, κ, ⟨?_, ?_⟩, ⟨?_, ?_⟩, hκ, ⟨sq_symp κ fun i => (hκ i).ne', ?_⟩, ?_⟩
  · show S * O * Dinv * sigma n * (S * O * Dinv)ᵀ = sigma n
    have h1 := sq_symp (fun i => (κ i)⁻¹) fun i => inv_ne_zero (hκ i).ne'
    calc S * O * Dinv * sigma n * (S * O * Dinv)ᵀ
        = S * (O * (Dinv * sigma n * Dinvᵀ) * Oᵀ) * Sᵀ := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = sigma n := by rw [h1, hOsig', hS]
  · rw [transpose_mul, transpose_mul]
    calc Dinvᵀ * (Oᵀ * Sᵀ) * (S * O * Dinv) = Dinvᵀ * (Oᵀ * Mm * O) * Dinv := by
          simp only [Mm, Matrix.mul_assoc]
      _ = 1 := by
          rw [hOM, sq_t, sq_mul_gen, sq_mul_gen, ← sq_one]
          congr 1; funext i
          rw [← hκ2 i]; field_simp [(hκ i).ne']
  · show Oᵀ * sigma n * Oᵀᵀ = sigma n
    rw [transpose_transpose, hOsig]
  · rw [transpose_transpose, hOOt]
  · rw [squeezeMatrix, fromBlocks_diagonal, posDef_diagonal_iff]
    rintro (i | i)
    · exact hκ i
    · simpa using inv_pos.mpr (hκ i)
  · calc S = S * (O * Oᵀ) := by rw [hOOt, Matrix.mul_one]
      _ = S * O * (Dinv * squeezeMatrix κ) * Oᵀ := by rw [hDD]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

end X5ED


open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance) in
open QAlgorithms.Papers.Independent.Claimed50.P41 in
theorem solution (n : ℕ) (hn : 0 < n)
    (S : Matrix (Phase n) (Phase n) ℝ) (hS : PreservesCanonicalForm S) :
    ∃ K L : Matrix (Phase n) (Phase n) ℝ, ∃ kappa : Fin n → ℝ,
      IsPassive K ∧ IsPassive L ∧ (∀ i, 0 < kappa i) ∧
      IsPositiveSymplectic (squeezeMatrix kappa) ∧ S = K * squeezeMatrix kappa * L :=
  X5ED.ed_main S hS

