-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P11.generalizedWilliamson
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:23:58.435592+00:00
-- url     : https://prove2.me/submissions/2a71bf6f-ac19-4e0e-92d5-732b78a92d43

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P11
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

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace Matrix

namespace X5MGP

def skw {k : ℕ} (mu : Fin k → ℝ) : Matrix (QuadratureIndex k) (QuadratureIndex k) ℝ :=
  fun a b => mu a.1 * interleavedSymplecticForm k a b

lemma sk_eigen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E) (hskew : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) (W : Submodule ℝ E)
    (hW : ∀ x ∈ W, A x ∈ W) (hne : ∃ x ∈ W, A x ≠ 0) :
    ∃ e ∈ W, A e ≠ 0 ∧ ∃ c : ℝ, A (A e) = c • e := by
  have h2 : ∀ x ∈ W, (A ∘ₗ A) x ∈ W := fun x hx => hW _ (hW x hx)
  set T : W →ₗ[ℝ] W := (A ∘ₗ A).restrict h2
  have hT : T.IsSymmetric := by
    intro x y
    simp only [T, Submodule.coe_inner, LinearMap.coe_restrict_apply, LinearMap.comp_apply]
    rw [hskew, hskew, neg_neg]
  set b := hT.eigenvectorBasis rfl
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hxW, hx⟩ := hne
  have hb : ∀ i, T (b i) = 0 := by
    intro i
    have hbi := hT.apply_eigenvectorBasis rfl i
    by_cases hA : A (b i : E) = 0
    · apply Subtype.ext
      simp [T, hA]
    · have := hcon (b i) (b i).2 hA (hT.eigenvalues rfl i)
      exfalso; apply this
      have h5 := congrArg Subtype.val hbi
      simp only [T, LinearMap.coe_restrict_apply, LinearMap.comp_apply] at h5
      rw [h5]; rfl
  have hT0 : T = 0 := b.toBasis.ext fun i => by simpa using hb i
  have : (A ∘ₗ A) x = 0 := by
    have := congrArg (fun f => ((f ⟨x, hxW⟩ : W) : E)) hT0
    simpa [T] using this
  have h3 : ⟪A x, A x⟫ = 0 := by
    rw [hskew]; simp only [LinearMap.comp_apply] at this; rw [this, inner_zero_right, neg_zero]
  exact hx (inner_self_eq_zero.1 h3)

end X5MGP

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace Matrix

namespace X5MGP

lemma sk_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E) (hskew : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) :
    ∀ k : ℕ, ∀ W : Submodule ℝ E, (∀ x ∈ W, A x ∈ W) → Module.finrank ℝ W = 2 * k →
      ∃ v : Fin k × Fin 2 → E, ∃ mu : Fin k → ℝ, (∀ a, v a ∈ W) ∧ (∀ i, 0 ≤ mu i) ∧
        (∀ a b, ⟪v a, v b⟫ = if a = b then 1 else 0) ∧
        (∀ a b, ⟪v a, A (v b)⟫ = skw mu a b) := by
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
    by_cases hne : ∃ x ∈ W, A x ≠ 0
    swap
    · push Not at hne
      set b := stdOrthonormalBasis ℝ W
      have hcard : Module.finrank ℝ W = (k + 1) * 2 := by rw [hdim]; ring
      set eq : Fin (k + 1) × Fin 2 ≃ Fin (Module.finrank ℝ W) :=
        finProdFinEquiv.trans (finCongr hcard.symm)
      refine ⟨fun a => (b (eq a) : E), fun _ => 0, fun a => (b (eq a)).2, fun _ => le_refl _,
        ?_, ?_⟩
      · intro a c
        rw [← Submodule.coe_inner, orthonormal_iff_ite.1 b.orthonormal]
        simp [eq.injective.eq_iff]
      · intro a c
        rw [hne _ (b (eq c)).2, inner_zero_right]
        simp [skw]
    obtain ⟨e0, he0W, hAe0, c, hc⟩ := sk_eigen A hskew W hW hne
    have he00 : e0 ≠ 0 := fun h => hAe0 (by rw [h, map_zero])
    have hpos1 : 0 < ⟪A e0, A e0⟫ := real_inner_self_pos.2 hAe0
    have hpos2 : 0 < ⟪e0, e0⟫ := real_inner_self_pos.2 he00
    have hrel : ⟪A e0, A e0⟫ = -c * ⟪e0, e0⟫ := by
      rw [hskew, hc, inner_smul_right]; ring
    have hcneg : 0 < -c := by
      by_contra h; push Not at h; nlinarith
    set s := Real.sqrt (-c) with hs
    have hspos : 0 < s := Real.sqrt_pos.2 hcneg
    have hss : s * s = -c := Real.mul_self_sqrt hcneg.le
    set r := (Real.sqrt ⟪e0, e0⟫)⁻¹ with hr
    have hrr : r * r * ⟪e0, e0⟫ = 1 := by
      have h1 := Real.mul_self_sqrt hpos2.le
      have h3 : 0 < Real.sqrt ⟪e0, e0⟫ := Real.sqrt_pos.2 hpos2
      rw [hr]
      field_simp
      linarith
    set e := r • e0 with he
    have heW : e ∈ W := W.smul_mem _ he0W
    have hAAe : A (A e) = -(s * s) • e := by
      rw [he, map_smul, map_smul, hc, hss, neg_neg, smul_comm]
    have hee : ⟪e, e⟫ = 1 := by
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
    have hff : ⟪f, f⟫ = 1 := by
      have h3 := hxAe f
      have h4 : ⟪f, A e⟫ = -s := by
        have := hfAx e
        rw [hee] at this; rw [this]; ring
      rw [h4] at h3
      have : s * (⟪f, f⟫ - 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
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
    obtain ⟨v', mu', hv'W, hmu', hv'G, hv'O⟩ := ih W' hW'inv (by omega)
    have hev' : ∀ a, ⟪e, v' a⟫ = 0 := fun a => ((memW' _).1 (hv'W a)).2.1
    have hfv' : ∀ a, ⟪f, v' a⟫ = 0 := fun a => ((memW' _).1 (hv'W a)).2.2
    have hv'e : ∀ a, ⟪v' a, e⟫ = 0 := fun a => by rw [real_inner_comm]; exact hev' a
    have hv'f : ∀ a, ⟪v' a, f⟫ = 0 := fun a => by rw [real_inner_comm]; exact hfv' a
    have hAee : ⟪e, A e⟫ = 0 := hself e
    have hAff : ⟪f, A f⟫ = 0 := hself f
    have hAef : ⟪e, A f⟫ = s := by rw [hxAf, hee]; ring
    have hAfe : ⟪f, A e⟫ = -s := by rw [hfAx, hee]; ring
    let v : Fin (k + 1) × Fin 2 → E := fun a => Fin.cases (![e, f] a.2) (fun j => v' (j, a.2)) a.1
    refine ⟨v, Fin.cases s mu', ?_, ?_, ?_, ?_⟩
    · rintro ⟨i, t⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · fin_cases t <;> simp [v, heW, hfW]
      · simp only [v, Fin.cases_succ]; exact ((memW' _).1 (hv'W _)).1
    · intro i; refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hspos.le
      · simpa using hmu' j
    · have hee2 : ‖e‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hee]
      have hff2 : ‖f‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hff]
      rintro ⟨i, t⟩ ⟨j, u⟩
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
        fin_cases t <;> fin_cases u <;>
        simp [v, hee2, hff2, hef, hfe, hff, hev', hfv', hv'e,
          hv'f, hv'G, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm, Prod.ext_iff]
    · rintro ⟨i, t⟩ ⟨j, u⟩
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
        fin_cases t <;> fin_cases u <;>
        simp [v, skw, interleavedSymplecticForm, hAee, hAff, hAef, hAfe, heAx, hfAx, hxAe, hxAf,
          hev', hfv', hv'e, hv'f, hv'O, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

end X5MGP

namespace X5KernelRank
lemma even_finrank_range_of_skew {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (hT : LinearMap.adjoint T = -T) :
    Even (Module.finrank ℝ (LinearMap.range T)) := by
  set W := LinearMap.range T
  let T' : W →ₗ[ℝ] W := T.restrict (fun x _ => LinearMap.mem_range_self T x)
  have hT'apply : ∀ w : W, (T' w : E) = T w := fun w => rfl
  have hadj : -T' = LinearMap.adjoint T' := by
    rw [LinearMap.eq_adjoint_iff]
    intro x y
    simp only [LinearMap.neg_apply, Submodule.coe_inner, hT'apply, inner_neg_left]
    rw [← LinearMap.adjoint_inner_left, hT, LinearMap.neg_apply, inner_neg_left]
  have hker : LinearMap.ker T' = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    have h1 : T w = 0 := by rw [← hT'apply, hw]; rfl
    have h2 : (w : E) ∈ Wᗮ := by
      rw [LinearMap.orthogonal_range, hT, LinearMap.mem_ker, LinearMap.neg_apply, h1, neg_zero]
    have h3 : (w : E) = 0 := by
      have := Submodule.inner_right_of_mem_orthogonal w.2 h2
      exact inner_self_eq_zero.1 this
    rw [Submodule.mem_bot]
    exact Subtype.ext h3
  have hdet : LinearMap.det T' ≠ 0 := by
    intro h
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.1 h) hker
  let b := stdOrthonormalBasis ℝ W
  have hdadj : LinearMap.det (LinearMap.adjoint T') = LinearMap.det T' := by
    rw [← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix b.toBasis,
      LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose]
    simp
  have hneg : LinearMap.det (-T') = (-1) ^ Module.finrank ℝ W * LinearMap.det T' := by
    rw [← neg_one_smul ℝ T', LinearMap.det_smul]
  rw [← hadj, hneg] at hdadj
  have : ((-1 : ℝ)) ^ Module.finrank ℝ W = 1 := by
    have := mul_right_cancel₀ hdet (hdadj.trans (one_mul _).symm)
    exact this
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).1 this
end X5KernelRank

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace Matrix

namespace X5GW
open X5MGP

def nf (q : ℕ) (m : Fin q → ℝ) {N : ℕ} (i j : Fin N) : ℝ :=
  if h : i.val < 2 * q ∧ j.val < 2 * q ∧ i.val / 2 = j.val / 2 then
    (if i.val % 2 = 0 ∧ j.val % 2 = 1 then -m ⟨i.val / 2, by omega⟩
     else if i.val % 2 = 1 ∧ j.val % 2 = 0 then m ⟨i.val / 2, by omega⟩ else 0)
  else 0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma ker_of_orth_range (A : E →ₗ[ℝ] E) (hskew : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫)
    (x : E) (hx : x ∈ (LinearMap.range A)ᗮ) : A x = 0 := by
  have h1 : ⟪A (A x), x⟫ = 0 := by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal' _ _).mp hx _ (LinearMap.mem_range_self A _)
  have h2 : ⟪A x, A x⟫ = 0 := by
    have := hskew (A x) x
    rw [h1] at this
    linarith
  exact inner_self_eq_zero.mp h2

lemma range_inf_ker (A : E →ₗ[ℝ] E) (hskew : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫)
    (x : E) (hx : x ∈ LinearMap.range A) (h0 : A x = 0) : x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  have := hskew y (A y)
  rw [h0, inner_zero_right, neg_zero] at this
  exact inner_self_eq_zero.mp this

lemma span_full {ι : Type*} [Fintype ι] (v : ι → E) (hv : Orthonormal ℝ v) (W : Submodule ℝ E)
    (hvW : ∀ a, v a ∈ W) (hcard : Fintype.card ι = Module.finrank ℝ W) (x : E) (hx : x ∈ W)
    (h0 : ∀ a, ⟪v a, x⟫ = 0) : x = 0 := by
  have hle : Submodule.span ℝ (Set.range v) ≤ W := by
    rw [Submodule.span_le]; rintro _ ⟨a, rfl⟩; exact hvW a
  have heq : Submodule.span ℝ (Set.range v) = W := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_span_eq_card hv.linearIndependent, hcard]
  rw [← heq] at hx
  have : x ∈ (Submodule.span ℝ (Set.range v))ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    refine Submodule.span_induction (p := fun u _ => ⟪x, u⟫ = 0) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨a, rfl⟩; rw [real_inner_comm]; exact h0 a
    · simp
    · intro a b _ _ ha hb; rw [inner_add_right, ha, hb, add_zero]
    · intro r a _ ha; rw [inner_smul_right, ha, mul_zero]
  exact inner_self_eq_zero.mp ((Submodule.mem_orthogonal' _ _).mp this x hx)

lemma gw_euclid (A Pl : E →ₗ[ℝ] E) (hskew : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫)
    (hPsym : ∀ x y, ⟪Pl x, y⟫ = ⟪x, Pl y⟫) (hPP : ∀ x, Pl (Pl x) = Pl x)
    (hAP : ∀ x, A (Pl x) = A x) (hPA : ∀ x, Pl (A x) = A x) (N : ℕ)
    (hN : Module.finrank ℝ E = N) :
    ∃ (q c z : ℕ) (m : Fin q → ℝ) (f : Fin N → E), 2 * q + c + z = N ∧ (∀ k, 0 < m k) ∧
      (∀ i j, ⟪f i, f j⟫ = if i = j then 1 else 0) ∧
      (∀ i j, ⟪f i, Pl (f j)⟫ = if i = j ∧ i.val < 2 * q + c then 1 else 0) ∧
      (∀ i j, ⟪f i, A (f j)⟫ = nf q m i j) := by
  set R := LinearMap.range Pl
  set W := LinearMap.range A
  have hRfix : ∀ x ∈ R, Pl x = x := by
    rintro x ⟨y, rfl⟩; exact hPP y
  have hRo : ∀ x ∈ Rᗮ, Pl x = 0 := by
    intro x hx
    have : ⟪Pl x, Pl x⟫ = 0 := by
      rw [hPsym, hPP]
      exact (Submodule.mem_orthogonal' _ _).mp hx _ (LinearMap.mem_range_self Pl x)
    exact inner_self_eq_zero.mp this
  have hARo : ∀ x ∈ Rᗮ, A x = 0 := by
    intro x hx; rw [← hAP, hRo x hx, map_zero]
  have hWR : W ≤ R := by
    rintro x ⟨y, rfl⟩; exact ⟨A y, hPA y⟩
  have hWo : ∀ x ∈ Wᗮ, A x = 0 := ker_of_orth_range A hskew
  have hadj : LinearMap.adjoint A = -A := by
    symm
    rw [LinearMap.eq_adjoint_iff]
    intro x y
    simp [hskew]
  obtain ⟨q, hq⟩ := X5KernelRank.even_finrank_range_of_skew A hadj
  have hWdim : Module.finrank ℝ W = 2 * q := by rw [hq]; ring
  obtain ⟨v, mu, hvW, hmu, hG, hO⟩ := sk_core A hskew q W
    (fun x _ => LinearMap.mem_range_self A x) hWdim
  have hvo : Orthonormal ℝ v := orthonormal_iff_ite.mpr hG
  have hmpos : ∀ k, 0 < mu k := by
    intro k
    rcases (hmu k).lt_or_eq with h | h
    · exact h
    exfalso
    have hk : mu k = 0 := h.symm
    clear h
    have hx0 : A (v (k, 1)) = 0 := by
      apply span_full v hvo W hvW (by simp [hWdim, mul_comm]) _ (LinearMap.mem_range_self A _)
      intro a
      rw [hO]
      simp only [skw, interleavedSymplecticForm]
      split_ifs with h1 <;> simp [h1, hk]
    have := range_inf_ker A hskew _ (hvW (k, 1)) hx0
    have h1 := hG (k, 1) (k, 1)
    rw [this, inner_zero_left] at h1
    simp at h1
  set U1 : Submodule ℝ E := Wᗮ ⊓ R
  set U2 : Submodule ℝ E := Rᗮ
  set c := Module.finrank ℝ U1
  set z := Module.finrank ℝ U2
  have hd1 : Module.finrank ℝ W + c = Module.finrank ℝ R :=
    Submodule.finrank_add_inf_finrank_orthogonal hWR
  have hd2 : Module.finrank ℝ R + z = Module.finrank ℝ E := Submodule.finrank_add_finrank_orthogonal R
  have hsum : 2 * q + c + z = N := by omega
  let b1 := stdOrthonormalBasis ℝ U1
  let b2 := stdOrthonormalBasis ℝ U2
  let f : Fin N → E := fun i =>
    if h1 : i.val < 2 * q then v (⟨i.val / 2, by omega⟩, ⟨1 - i.val % 2, by omega⟩)
    else if h2 : i.val < 2 * q + c then ((b1 ⟨i.val - 2 * q, by omega⟩ : U1) : E)
    else ((b2 ⟨i.val - 2 * q - c, by omega⟩ : U2) : E)
  have hfW : ∀ i : Fin N, i.val < 2 * q → f i ∈ W := by
    intro i h; simp only [f, dif_pos h]; exact hvW _
  have hf1 : ∀ i : Fin N, 2 * q ≤ i.val → i.val < 2 * q + c → f i ∈ U1 := by
    intro i h h'; simp only [f, dif_neg (show ¬ i.val < 2 * q by omega), dif_pos h']
    exact Submodule.coe_mem _
  have hf2 : ∀ i : Fin N, 2 * q + c ≤ i.val → f i ∈ U2 := by
    intro i h
    simp only [f, dif_neg (show ¬ i.val < 2 * q by omega), dif_neg (show ¬ i.val < 2 * q + c by omega)]
    exact Submodule.coe_mem _
  have hfR : ∀ i : Fin N, i.val < 2 * q + c → f i ∈ R := by
    intro i h
    by_cases h1 : i.val < 2 * q
    · exact hWR (hfW i h1)
    · exact (hf1 i (by omega) h).2
  have hA0 : ∀ j : Fin N, 2 * q ≤ j.val → A (f j) = 0 := by
    intro j h
    by_cases h2 : j.val < 2 * q + c
    · exact hWo _ (hf1 j h h2).1
    · exact hARo _ (hf2 j (by omega))
  have hb1 : ∀ a b, ⟪((b1 a : U1) : E), ((b1 b : U1) : E)⟫ = if a = b then 1 else 0 := by
    intro a b; rw [← Submodule.coe_inner]; exact orthonormal_iff_ite.mp b1.orthonormal a b
  have hb2 : ∀ a b, ⟪((b2 a : U2) : E), ((b2 b : U2) : E)⟫ = if a = b then 1 else 0 := by
    intro a b; rw [← Submodule.coe_inner]; exact orthonormal_iff_ite.mp b2.orthonormal a b
  -- cross terms vanish
  have hx : ∀ i j : Fin N, i.val < 2 * q → 2 * q ≤ j.val → ⟪f i, f j⟫ = 0 := by
    intro i j hi hj
    by_cases hj2 : j.val < 2 * q + c
    · exact Submodule.inner_right_of_mem_orthogonal (hfW i hi) (hf1 j hj hj2).1
    · exact Submodule.inner_right_of_mem_orthogonal (hWR (hfW i hi)) (hf2 j (by omega))
  have hy : ∀ i j : Fin N, i.val < 2 * q + c → 2 * q + c ≤ j.val → ⟪f i, f j⟫ = 0 := by
    intro i j hi hj
    exact Submodule.inner_right_of_mem_orthogonal (hfR i hi) (hf2 j hj)
  have horth : ∀ i j : Fin N, ⟪f i, f j⟫ = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      by_cases hi : i.val < 2 * q
      · simp only [f, dif_pos hi]; rw [hG]; simp
      by_cases hi2 : i.val < 2 * q + c
      · simp only [f, dif_neg hi, dif_pos hi2]; rw [hb1]; simp
      · simp only [f, dif_neg hi, dif_neg hi2]; rw [hb2]; simp
    rw [if_neg hij]
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    by_cases hi : i.val < 2 * q <;> by_cases hj : j.val < 2 * q
    · simp only [f, dif_pos hi, dif_pos hj]
      rw [hG, if_neg]
      intro h
      simp only [Prod.mk.injEq, Fin.mk.injEq] at h
      omega
    · exact hx i j hi (by omega)
    · rw [real_inner_comm]; exact hx j i hj (by omega)
    by_cases hi2 : i.val < 2 * q + c <;> by_cases hj2 : j.val < 2 * q + c
    · simp only [f, dif_neg hi, dif_neg hj, dif_pos hi2, dif_pos hj2]
      rw [hb1, if_neg]
      intro h; simp only [Fin.mk.injEq] at h; omega
    · exact hy i j hi2 (by omega)
    · rw [real_inner_comm]; exact hy j i hj2 (by omega)
    · simp only [f, dif_neg hi, dif_neg hj, dif_neg hi2, dif_neg hj2]
      rw [hb2, if_neg]
      intro h; simp only [Fin.mk.injEq] at h; omega
  refine ⟨q, c, z, mu, f, hsum, hmpos, horth, ?_, ?_⟩
  · intro i j
    by_cases hj : j.val < 2 * q + c
    · rw [hRfix _ (hfR j hj), horth]
      by_cases hij : i = j
      · subst hij; simp [hj]
      · simp [hij]
    · rw [hRo _ (hf2 j (by omega)), inner_zero_right]
      by_cases hij : i = j
      · subst hij; simp [hj]
      · simp [hij]
  · intro i j
    by_cases hj : j.val < 2 * q
    · by_cases hi : i.val < 2 * q
      · simp only [f, dif_pos hi, dif_pos hj]
        rw [hO]
        simp only [skw, interleavedSymplecticForm, nf]
        by_cases he : i.val / 2 = j.val / 2
        · rw [dif_pos ⟨hi, hj, he⟩]
          have he' : (⟨i.val / 2, by omega⟩ : Fin q) = ⟨j.val / 2, by omega⟩ := Fin.ext he
          rw [if_pos he']
          rcases Nat.mod_two_eq_zero_or_one i.val with h1 | h1 <;>
            rcases Nat.mod_two_eq_zero_or_one j.val with h2 | h2 <;>
            simp [h1, h2]
        · rw [dif_neg (by tauto)]
          have he' : (⟨i.val / 2, by omega⟩ : Fin q) ≠ ⟨j.val / 2, by omega⟩ :=
            fun h => he (Fin.ext_iff.mp h)
          rw [if_neg he', mul_zero]
      · have hAW : A (f j) ∈ W := LinearMap.mem_range_self A _
        have : ⟪f i, A (f j)⟫ = 0 := by
          by_cases hi2 : i.val < 2 * q + c
          · rw [real_inner_comm]
            exact Submodule.inner_right_of_mem_orthogonal hAW (hf1 i (by omega) hi2).1
          · rw [real_inner_comm]
            exact Submodule.inner_right_of_mem_orthogonal (hWR hAW) (hf2 i (by omega))
        rw [this, nf, dif_neg (by omega)]
    · rw [hA0 j (by omega), inner_zero_right, nf, dif_neg (by omega)]

end X5GW

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace Matrix

namespace X5GW
open Matrix

lemma gw_mat {N : ℕ} (P M : Matrix (Fin N) (Fin N) ℝ) (hPt : Pᵀ = P) (hPP : P * P = P)
    (hMt : Mᵀ = -M) (hMP : M * P = M) :
    ∃ (q c z : ℕ) (m : Fin q → ℝ) (V : Matrix (Fin N) (Fin N) ℝ), 2 * q + c + z = N ∧
      (∀ k, 0 < m k) ∧ Vᵀ * V = 1 ∧
      Vᵀ * P * V = diagonal (fun i => if i.val < 2 * q + c then 1 else 0) ∧
      Vᵀ * M * V = Matrix.of (fun i j => nf q m i j) := by
  have hPM : P * M = M := by
    have := congrArg Matrix.transpose hMP
    rw [transpose_mul, hMt, hPt, Matrix.mul_neg] at this
    exact neg_inj.mp this
  let A : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N) := Matrix.toLpLin 2 2 M
  let Pl : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N) := Matrix.toLpLin 2 2 P
  have hin : ∀ (X : Matrix (Fin N) (Fin N) ℝ) (x y : EuclideanSpace ℝ (Fin N)),
      ⟪x, Matrix.toLpLin 2 2 X y⟫ = WithLp.ofLp x ⬝ᵥ (X *ᵥ WithLp.ofLp y) := by
    intro X x y
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply]
    simp [dotProduct_comm]
  have happ : ∀ (X : Matrix (Fin N) (Fin N) ℝ) (x : EuclideanSpace ℝ (Fin N)),
      WithLp.ofLp (Matrix.toLpLin 2 2 X x) = X *ᵥ WithLp.ofLp x := by
    intro X x; rw [Matrix.toLpLin_apply]
  have hsymm : ∀ (X : Matrix (Fin N) (Fin N) ℝ) (x y : EuclideanSpace ℝ (Fin N)),
      ⟪Matrix.toLpLin 2 2 X x, y⟫ = WithLp.ofLp x ⬝ᵥ (Xᵀ *ᵥ WithLp.ofLp y) := by
    intro X x y
    rw [real_inner_comm, hin, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      dotProduct_comm]
  have hskew : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫ := by
    intro x y
    rw [hsymm, hin, hMt, Matrix.neg_mulVec, dotProduct_neg]
  have hPsym : ∀ x y, ⟪Pl x, y⟫ = ⟪x, Pl y⟫ := by
    intro x y; rw [hsymm, hin, hPt]
  have hext : ∀ x y : EuclideanSpace ℝ (Fin N), WithLp.ofLp x = WithLp.ofLp y → x = y :=
    fun x y h => by simpa using congrArg (WithLp.toLp 2) h
  have hPP' : ∀ x, Pl (Pl x) = Pl x := by
    intro x; apply hext; simp only [Pl, happ, Matrix.mulVec_mulVec, hPP]
  have hAP : ∀ x, A (Pl x) = A x := by
    intro x; apply hext; simp only [A, Pl, happ, Matrix.mulVec_mulVec, hMP]
  have hPA : ∀ x, Pl (A x) = A x := by
    intro x; apply hext; simp only [A, Pl, happ, Matrix.mulVec_mulVec, hPM]
  obtain ⟨q, c, z, m, f, hsum, hm, horth, hPf, hAf⟩ :=
    gw_euclid A Pl hskew hPsym hPP' hAP hPA N (finrank_euclideanSpace_fin)
  set V : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun k i => WithLp.ofLp (f i) k
  have hV : ∀ (X : Matrix (Fin N) (Fin N) ℝ) i j,
      (Vᵀ * X * V) i j = ⟪f i, Matrix.toLpLin 2 2 X (f j)⟫ := by
    intro X i j
    rw [hin, Matrix.mul_assoc]
    simp [V, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  refine ⟨q, c, z, m, V, hsum, hm, ?_, ?_, ?_⟩
  · ext i j
    have := hV 1 i j
    rw [Matrix.mul_one] at this
    rw [this, Matrix.toLpLin_one, LinearMap.id_apply, horth, Matrix.one_apply]
  · ext i j
    rw [hV, hPf, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · ext i j
    rw [hV, hAf, Matrix.of_apply]

end X5GW

noncomputable section
open scoped Matrix

namespace X5GW
open Matrix QAlgorithms.Papers.Independent.Frontier18.P11

lemma card_lt (N k : ℕ) (hk : k ≤ N) (w : Fin N → ℝ) (hw : ∀ i : Fin N, w i ≠ 0 ↔ i.val < k) :
    Fintype.card {i // w i ≠ 0} = k := by
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun i : Fin N => w i ≠ 0) =
      Finset.univ.filter fun i : Fin N => i.val < k := by
    ext i; simp [hw]
  rw [this, Fin.card_filter_val_lt]
  omega

lemma ncov_rank (N q c : ℕ) (nu : ℕ → ℝ) (hnu : ∀ k < q, 0 < nu k) (h : 2 * q + c ≤ N) :
    (normalCovariance N q c nu).rank = 2 * q + c := by
  unfold normalCovariance
  rw [rank_diagonal]
  apply card_lt N _ h
  intro i
  split_ifs with h1 h2
  · have := hnu (i.val / 2) (by omega)
    constructor
    · intro; omega
    · intro; exact this.ne'
  · simp [h2]
  · simp; omega

lemma ncom_sq (N q : ℕ) (hq : 2 * q ≤ N) :
    normalCommutator N q * normalCommutator N q =
      diagonal (fun i : Fin N => if i.val < 2 * q then (-1 : ℝ) else 0) := by
  ext i j
  rw [Matrix.mul_apply, diagonal_apply]
  by_cases hi : i.val < 2 * q
  · rcases Nat.mod_two_eq_zero_or_one i.val with hp | hp
    · set k0 : Fin N := ⟨i.val + 1, by omega⟩
      rw [Finset.sum_eq_single k0]
      · simp only [normalCommutator, k0]
        by_cases hij : i = j
        · subst hij; simp [hp, hi]; rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
        · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
          rw [if_neg hij]
          split_ifs <;> simp_all <;> omega
      · intro k _ hk
        have hne : k.val ≠ i.val + 1 := fun h => hk (Fin.ext h)
        simp only [normalCommutator]
        split_ifs <;> simp_all <;> omega
      · simp
    · set k0 : Fin N := ⟨i.val - 1, by omega⟩
      rw [Finset.sum_eq_single k0]
      · simp only [normalCommutator, k0]
        by_cases hij : i = j
        · subst hij; simp [hp, hi]; rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
        · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
          rw [if_neg hij]
          split_ifs <;> simp_all <;> omega
      · intro k _ hk
        have hne : k.val ≠ i.val - 1 := fun h => hk (Fin.ext h)
        simp only [normalCommutator]
        split_ifs <;> simp_all <;> omega
      · simp
  · rw [Finset.sum_eq_zero]
    · split_ifs <;> simp_all
    · intro k _
      simp [normalCommutator, hi]

lemma ncom_rank (N q : ℕ) (hq : 2 * q ≤ N) : (normalCommutator N q).rank = 2 * q := by
  set C := normalCommutator N q
  have hsq := ncom_sq N q hq
  have hPC : diagonal (fun i : Fin N => if i.val < 2 * q then (-1 : ℝ) else 0) * C = -C := by
    ext i j
    rw [diagonal_mul]
    simp only [C, normalCommutator, Matrix.neg_apply]
    split_ifs <;> simp_all
  have hC : C = (C * C) * (-C) := by
    rw [Matrix.mul_neg, hsq, hPC, neg_neg]
  have h1 : (C * C).rank ≤ C.rank := rank_mul_le_left _ _
  have h2 : C.rank ≤ (C * C).rank := by
    conv_lhs => rw [hC]
    exact rank_mul_le_left _ _
  have h3 : (C * C).rank = 2 * q := by
    rw [hsq, rank_diagonal]
    apply card_lt N _ hq
    intro i; split_ifs with h <;> simp [h]
  omega

end X5GW

noncomputable section
open scoped ComplexOrder
open Matrix

namespace X5FullRank

variable {a : Type*} [Fintype a] [DecidableEq a]
lemma real_spectral (M : Matrix a a ℝ) (hM : M.IsHermitian) :
    ∃ U : Matrix a a ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      M = U * diagonal hM.eigenvalues * Uᵀ := by
  have hst : ∀ X : Matrix a a ℝ, star X = Xᵀ := fun X => by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  refine ⟨(hM.eigenvectorUnitary : Matrix a a ℝ), ?_, ?_, ?_⟩
  · rw [← hst]; exact Unitary.coe_mul_star_self _
  · rw [← hst]; exact Unitary.coe_star_mul_self _
  · conv_lhs => rw [hM.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, hst]
    congr 2

/-- If `Y` is positive definite, `R` and `Y - R` are positive semidefinite and
`det (Y - R) = det Y`, then `R = 0`. -/
lemma eq_zero_of_det_sub_eq (Y R : Matrix a a ℝ) (hY : Y.PosDef) (hR : R.PosSemidef)
    (hQ : (Y - R).PosSemidef) (hdet : (Y - R).det = Y.det) : R = 0 := by
  obtain ⟨U, hU1, hU2, hYU⟩ := real_spectral Y hY.isHermitian
  set ev := hY.isHermitian.eigenvalues
  have hev : ∀ i, 0 < ev i := fun i => hY.eigenvalues_pos i
  set B : Matrix a a ℝ := U * diagonal (fun i => Real.sqrt (ev i)) with hB
  have hBB : B * Bᵀ = Y := by
    rw [hYU, hB, Matrix.transpose_mul, Matrix.diagonal_transpose]
    have : diagonal (fun i => Real.sqrt (ev i)) * diagonal (fun i => Real.sqrt (ev i)) =
        diagonal ev := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1; funext i; exact Real.mul_self_sqrt (hev i).le
    calc U * diagonal (fun i => Real.sqrt (ev i)) * (diagonal (fun i => Real.sqrt (ev i)) * Uᵀ)
        = U * (diagonal (fun i => Real.sqrt (ev i)) * diagonal (fun i => Real.sqrt (ev i))) * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = U * diagonal ev * Uᵀ := by rw [this]
  have hdetY : 0 < Y.det := hY.det_pos
  have hdetB : B.det ≠ 0 := by
    intro h0
    have : Y.det = B.det * B.det := by rw [← hBB, Matrix.det_mul, Matrix.det_transpose]
    rw [h0, zero_mul] at this
    linarith
  have hBu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hdetB)
  have hBtu : IsUnit Bᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hdetB
  set Bi := B⁻¹ with hBi
  have hBiB : Bi * B = 1 := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hBu)
  have hBBi : B * Bi = 1 := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hBu)
  have hBtBit : Bᵀ * Biᵀ = 1 := by rw [← Matrix.transpose_mul, hBiB, Matrix.transpose_one]
  have hBitBt : Biᵀ * Bᵀ = 1 := by rw [← Matrix.transpose_mul, hBBi, Matrix.transpose_one]
  have hct : ∀ X : Matrix a a ℝ, Xᴴ = Xᵀ := fun X => Matrix.conjTranspose_eq_transpose_of_trivial X
  set M := Bi * R * Biᵀ with hM
  have hMpsd : M.PosSemidef := by
    have := hR.mul_mul_conjTranspose_same Bi
    rwa [hct] at this
  have hYc : Bi * Y * Biᵀ = 1 := by
    rw [← hBB]
    calc Bi * (B * Bᵀ) * Biᵀ = (Bi * B) * (Bᵀ * Biᵀ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBiB, hBtBit, Matrix.one_mul]
  have hN : Bi * (Y - R) * Biᵀ = 1 - M := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hYc]
  have hNpsd : (1 - M).PosSemidef := by
    rw [← hN]
    have := hQ.mul_mul_conjTranspose_same Bi
    rwa [hct] at this
  have hdetN : (1 - M).det = 1 := by
    have h1 : (Bi * Y * Biᵀ).det = 1 := by rw [hYc, Matrix.det_one]
    rw [← hN]
    rw [Matrix.det_mul, Matrix.det_mul] at h1 ⊢
    rw [hdet]; exact h1
  -- diagonalize M
  obtain ⟨V, hV1, hV2, hMV⟩ := real_spectral M hMpsd.isHermitian
  set lam := hMpsd.isHermitian.eigenvalues
  have hlam0 : ∀ i, 0 ≤ lam i := fun i => hMpsd.eigenvalues_nonneg i
  have h1M : 1 - M = V * diagonal (fun i => 1 - lam i) * Vᵀ := by
    have : diagonal (fun i => 1 - lam i) = 1 - diagonal lam := by
      ext i j; by_cases h : i = j <;> simp [h]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV1, ← hMV]
  have hD : (diagonal (fun i => 1 - lam i)).PosSemidef := by
    have := hNpsd.conjTranspose_mul_mul_same V
    rw [hct, h1M] at this
    convert this using 1
    calc diagonal (fun i => 1 - lam i) = (Vᵀ * V) * diagonal (fun i => 1 - lam i) * (Vᵀ * V) := by
          rw [hV2, Matrix.one_mul, Matrix.mul_one]
      _ = Vᵀ * (V * diagonal (fun i => 1 - lam i) * Vᵀ) * V := by simp only [Matrix.mul_assoc]
  have hle1 : ∀ i, 0 ≤ 1 - lam i := fun i => by
    have := hD.diag_nonneg (i := i)
    simpa [Matrix.diagonal_apply] using this
  have hprod : ∏ i, (1 - lam i) = 1 := by
    have : (1 - M).det = ∏ i, (1 - lam i) := by
      rw [h1M, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose]
      have hVV : V.det * V.det = 1 := by
        have := congrArg Matrix.det hV1
        rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
      calc V.det * (∏ i, (1 - lam i)) * V.det = (V.det * V.det) * ∏ i, (1 - lam i) := by ring
        _ = ∏ i, (1 - lam i) := by rw [hVV, one_mul]
    rw [← this, hdetN]
  have hlam : lam = 0 := by
    funext i
    have hrest : ∏ j ∈ Finset.univ.erase i, (1 - lam j) ≤ 1 :=
      Finset.prod_le_one (fun j _ => hle1 j) (fun j _ => by linarith [hlam0 j])
    have := Finset.mul_prod_erase Finset.univ (fun j => 1 - lam j) (Finset.mem_univ i)
    rw [hprod] at this
    have h2 : (1 - lam i) * ∏ j ∈ Finset.univ.erase i, (1 - lam j) ≤ 1 - lam i :=
      mul_le_of_le_one_right (hle1 i) hrest
    have := hlam0 i
    simp only [Pi.zero_apply]
    linarith
  have hM0 : M = 0 := hMpsd.isHermitian.eigenvalues_eq_zero_iff.mp hlam
  calc R = (B * Bi) * R * (Biᵀ * Bᵀ) := by rw [hBBi, hBitBt, Matrix.one_mul, Matrix.mul_one]
    _ = B * M * Bᵀ := by simp only [hM, Matrix.mul_assoc]
    _ = 0 := by rw [hM0, Matrix.mul_zero, Matrix.zero_mul]

end X5FullRank

noncomputable section
open scoped Matrix ComplexOrder

namespace X5GW
open Matrix QAlgorithms.Papers.Independent.Frontier18.P11

variable {N : ℕ}

def cxv (x : Fin N → ℝ) : Fin N → ℂ := fun i => (x i : ℂ)

lemma cm_mulVec (A : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) :
    complexMatrix A *ᵥ cxv x = cxv (A *ᵥ x) := by
  ext i; simp [complexMatrix, cxv, Matrix.mulVec, dotProduct]

lemma cxv_dot (x y : Fin N → ℝ) : star (cxv x) ⬝ᵥ cxv y = ((x ⬝ᵥ y : ℝ) : ℂ) := by
  simp [cxv, dotProduct]

lemma cm_mul (A B : Matrix (Fin N) (Fin N) ℝ) :
    complexMatrix (A * B) = complexMatrix A * complexMatrix B := by
  ext i j; simp [complexMatrix, Matrix.mul_apply]

lemma cm_transpose (A : Matrix (Fin N) (Fin N) ℝ) :
    complexMatrix Aᵀ = (complexMatrix A)ᴴ := by
  ext i j; simp [complexMatrix, Matrix.conjTranspose_apply]

lemma col_ker (X Y Z : Matrix (Fin N) (Fin N) ℝ) (hker : ∀ x, X *ᵥ x = 0 → Y *ᵥ x = 0)
    (h : X * Z = 0) : Y * Z = 0 := by
  ext i j
  have hz := hker (fun k => Z k j) (by
    ext l
    have := congrFun (congrFun h l) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this)
  have := congrFun hz i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

lemma pre (mu Delta : Matrix (Fin N) (Fin N) ℝ) (hmu : mu.transpose = mu)
    (hDelta : Delta.transpose = -Delta)
    (hpositive : (complexMatrix mu - (Complex.I / 2) • complexMatrix Delta).PosSemidef) :
    mu.PosSemidef ∧ ∀ x, mu *ᵥ x = 0 → Delta *ᵥ x = 0 := by
  set H := complexMatrix mu - (Complex.I / 2) • complexMatrix Delta
  have hskew : ∀ x : Fin N → ℝ, x ⬝ᵥ (Delta *ᵥ x) = 0 := by
    intro x
    have : x ⬝ᵥ (Delta *ᵥ x) = -(x ⬝ᵥ (Delta *ᵥ x)) := by
      conv_lhs => rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hDelta,
        Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]
    linarith
  have hHv : ∀ x, H *ᵥ cxv x = cxv (mu *ᵥ x) - (Complex.I / 2) • cxv (Delta *ᵥ x) := by
    intro x
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, cm_mulVec, cm_mulVec]
  have hquad : ∀ x : Fin N → ℝ, star (cxv x) ⬝ᵥ (H *ᵥ cxv x) = ((x ⬝ᵥ (mu *ᵥ x) : ℝ) : ℂ) := by
    intro x
    rw [hHv, dotProduct_sub, dotProduct_smul, cxv_dot, cxv_dot, hskew]
    simp
  refine ⟨?_, ?_⟩
  · rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hmu]
    · have := hpositive.dotProduct_mulVec_nonneg (cxv x)
      rw [hquad] at this
      simpa using Complex.zero_le_real.1 this
  · intro x hx
    have h0 : star (cxv x) ⬝ᵥ (H *ᵥ cxv x) = 0 := by rw [hquad, hx]; simp
    have h1 := (hpositive.dotProduct_mulVec_zero_iff (cxv x)).mp h0
    rw [hHv, hx] at h1
    ext i
    have := congrArg Complex.im (congrFun h1 i)
    simp [cxv] at this
    simpa using this

lemma spec_step (mu Delta : Matrix (Fin N) (Fin N) ℝ) (hpsd : mu.PosSemidef)
    (hDelta : Delta.transpose = -Delta) (hker : ∀ x, mu *ᵥ x = 0 → Delta *ᵥ x = 0) :
    ∃ (B : Matrix (Fin N) (Fin N) ℝ) (p : Fin N → ℝ), B.det ≠ 0 ∧ (∀ i, p i * p i = p i) ∧
      Bᵀ * mu * B = diagonal p ∧ (Bᵀ * Delta * B) * diagonal p = Bᵀ * Delta * B := by
  obtain ⟨U, hU1, hU2, hmuU⟩ := X5FullRank.real_spectral mu hpsd.isHermitian
  set ev := hpsd.isHermitian.eigenvalues
  have hev : ∀ i, 0 ≤ ev i := fun i => hpsd.eigenvalues_nonneg i
  set β : Fin N → ℝ := fun i => if ev i = 0 then 1 else 1 / Real.sqrt (ev i)
  set p : Fin N → ℝ := fun i => if ev i = 0 then 0 else 1
  have hβ : ∀ i, β i ≠ 0 := by
    intro i; simp only [β]; split_ifs with h
    · norm_num
    · have : 0 < ev i := lt_of_le_of_ne (hev i) (Ne.symm h)
      positivity
  refine ⟨U * diagonal β, p, ?_, ?_, ?_, ?_⟩
  · rw [det_mul, det_diagonal]
    refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun i _ => hβ i)
    intro h
    have := congrArg det hU1
    rw [det_mul, det_transpose, h, zero_mul, det_one] at this
    exact zero_ne_one this
  · intro i; simp only [p]; split_ifs <;> norm_num
  · rw [hmuU, transpose_mul, diagonal_transpose]
    have : diagonal β * Uᵀ * (U * diagonal ev * Uᵀ) * (U * diagonal β) =
        diagonal β * (Uᵀ * U) * diagonal ev * (Uᵀ * U) * diagonal β := by
      simp only [Matrix.mul_assoc]
    rw [this, hU2, Matrix.mul_one, Matrix.mul_one, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; funext i
    simp only [β, p]
    split_ifs with h
    · simp [h]
    · have hpos : 0 < ev i := lt_of_le_of_ne (hev i) (Ne.symm h)
      have := Real.mul_self_sqrt hpos.le
      field_simp
      linarith
  · have hmuK : mu * (U * diagonal (fun i => 1 - p i)) = 0 := by
      rw [hmuU]
      have : U * diagonal ev * Uᵀ * (U * diagonal (fun i => 1 - p i)) =
          U * diagonal ev * (Uᵀ * U) * diagonal (fun i => 1 - p i) := by
        simp only [Matrix.mul_assoc]
      rw [this, hU2, Matrix.mul_one, Matrix.mul_assoc, diagonal_mul_diagonal]
      have : (fun i => ev i * (1 - p i)) = 0 := by
        funext i; simp only [p]; split_ifs with h <;> simp [h]
      rw [this]; simp
    have hΔK := col_ker mu Delta _ hker hmuK
    have hsplit : diagonal p = 1 - diagonal (fun i => 1 - p i) := by
      ext i j; by_cases h : i = j <;> simp [h, diagonal_apply, one_apply]
    rw [hsplit, Matrix.mul_sub, Matrix.mul_one, sub_eq_self]
    have : (U * diagonal β)ᵀ * Delta * (U * diagonal β) * diagonal (fun i => 1 - p i) =
        (U * diagonal β)ᵀ * (Delta * (U * diagonal (fun i => 1 - p i))) * diagonal β := by
      simp only [Matrix.mul_assoc, diagonal_mul_diagonal, mul_comm]
    rw [this, hΔK, Matrix.mul_zero, Matrix.zero_mul]

lemma gw_main (mu Delta : Matrix (Fin N) (Fin N) ℝ) (hmu : mu.transpose = mu)
    (hDelta : Delta.transpose = -Delta)
    (hpositive : (complexMatrix mu - (Complex.I / 2) • complexMatrix Delta).PosSemidef) :
    ∃ (q c z : ℕ) (nu : ℕ → ℝ) (T : Matrix (Fin N) (Fin N) ℝ),
      2 * q + c + z = N ∧ (∀ k < q, 0 < nu k) ∧ T.det ≠ 0 ∧
      T.transpose * mu * T = normalCovariance N q c nu ∧
      T.transpose * Delta * T = normalCommutator N q := by
  obtain ⟨hpsd, hker⟩ := pre mu Delta hmu hDelta hpositive
  obtain ⟨B, p, hB, hp, hBmu, hBD⟩ := spec_step mu Delta hpsd hDelta hker
  set D' := Bᵀ * Delta * B
  have hD't : D'ᵀ = -D' := by
    simp only [D', transpose_mul, transpose_transpose, hDelta, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc]
  obtain ⟨q, c, z, m, V, hsum, hm, hVV, hVP, hVM⟩ := gw_mat (diagonal p) D'
    (diagonal_transpose p) (by rw [diagonal_mul_diagonal]; congr 1; funext i; exact hp i) hD't hBD
  set δ : Fin N → ℝ := fun i =>
    if h : i.val < 2 * q then 1 / Real.sqrt (m ⟨i.val / 2, by omega⟩)
    else if i.val < 2 * q + c then 1 / Real.sqrt 2 else 1
  set nu : ℕ → ℝ := fun k => if h : k < q then 1 / m ⟨k, h⟩ else 0
  have hδ : ∀ i, 0 < δ i := by
    intro i; simp only [δ]; split_ifs with h1
    · have := hm ⟨i.val / 2, by omega⟩; positivity
    · positivity
    · norm_num
  refine ⟨q, c, z, nu, B * V * diagonal δ, hsum, ?_, ?_, ?_, ?_⟩
  · intro k hk; simp only [nu, dif_pos hk]; have := hm ⟨k, hk⟩; positivity
  · rw [det_mul, det_mul, det_diagonal]
    refine mul_ne_zero (mul_ne_zero hB ?_) (Finset.prod_ne_zero_iff.mpr fun i _ => (hδ i).ne')
    intro h
    have := congrArg det hVV
    rw [det_mul, det_transpose, h, zero_mul, det_one] at this
    exact zero_ne_one this
  · have : (B * V * diagonal δ)ᵀ * mu * (B * V * diagonal δ) =
        diagonal δ * (Vᵀ * (Bᵀ * mu * B) * V) * diagonal δ := by
      simp only [transpose_mul, diagonal_transpose, Matrix.mul_assoc]
    rw [this, hBmu, hVP]
    ext i j
    rw [mul_diagonal, diagonal_mul, diagonal_apply]
    simp only [normalCovariance, diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp only [if_true, δ, nu]
      by_cases h1 : i.val < 2 * q
      · have hmk := hm ⟨i.val / 2, by omega⟩
        rw [dif_pos h1, if_pos h1, if_pos (by omega), dif_pos (by omega)]
        field_simp
        rw [Real.sq_sqrt hmk.le]
      · rw [dif_neg h1, if_neg h1]
        by_cases h2 : i.val < 2 * q + c
        · rw [if_pos h2, if_pos h2, if_pos h2]
          field_simp
          rw [Real.sq_sqrt (by norm_num)]
        · rw [if_neg h2, if_neg h2, if_neg h2]; simp
    · simp [hij]
  · have : (B * V * diagonal δ)ᵀ * Delta * (B * V * diagonal δ) =
        diagonal δ * (Vᵀ * D' * V) * diagonal δ := by
      simp only [D', transpose_mul, diagonal_transpose, Matrix.mul_assoc]
    rw [this, hVM]
    ext i j
    rw [mul_diagonal, diagonal_mul, of_apply]
    simp only [normalCommutator, nf]
    by_cases h : i.val < 2 * q ∧ j.val < 2 * q ∧ i.val / 2 = j.val / 2
    · rw [dif_pos h, if_pos h]
      have hmk := hm ⟨i.val / 2, by omega⟩
      have hδi : δ i = 1 / Real.sqrt (m ⟨i.val / 2, by omega⟩) := by simp only [δ, dif_pos h.1]
      have hδj : δ j = 1 / Real.sqrt (m ⟨i.val / 2, by omega⟩) := by
        simp only [δ, dif_pos h.2.1, h.2.2]
      rw [hδi, hδj]
      have := Real.mul_self_sqrt hmk.le
      have hs : 0 < Real.sqrt (m ⟨i.val / 2, by omega⟩) := Real.sqrt_pos.mpr hmk
      split_ifs
      · field_simp; rw [Real.sq_sqrt hmk.le]
      · field_simp; rw [Real.sq_sqrt hmk.le]
      · simp
    · rw [dif_neg h, if_neg h]; simp

lemma quad2 (X : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) (hab : a ≠ b) :
    star (Pi.single a 1 + Pi.single b Complex.I : Fin N → ℂ) ⬝ᵥ
      (X *ᵥ (Pi.single a 1 + Pi.single b Complex.I)) =
      X a a + Complex.I * X a b - Complex.I * X b a + X b b := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_single, star_add, add_dotProduct, dotProduct_add,
    Pi.star_single, single_dotProduct, star_one, Complex.star_def, Complex.conj_I]
  simp [hab, Ne.symm hab]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma nu_half (mu Delta T : Matrix (Fin N) (Fin N) ℝ) (q c : ℕ) (nu : ℕ → ℝ)
    (hpositive : (complexMatrix mu - (Complex.I / 2) • complexMatrix Delta).PosSemidef)
    (hq : 2 * q ≤ N)
    (h1 : T.transpose * mu * T = normalCovariance N q c nu)
    (h2 : T.transpose * Delta * T = normalCommutator N q) (j : ℕ) (hj : j < q) :
    (1 / 2 : ℝ) ≤ nu j := by
  have hH := hpositive.conjTranspose_mul_mul_same (complexMatrix T)
  have e : (complexMatrix T)ᴴ * (complexMatrix mu - (Complex.I / 2) • complexMatrix Delta) *
      complexMatrix T = complexMatrix (normalCovariance N q c nu) -
        (Complex.I / 2) • complexMatrix (normalCommutator N q) := by
    rw [← h1, ← h2]
    simp only [cm_mul, cm_transpose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  rw [e] at hH
  set a : Fin N := ⟨2 * j, by omega⟩
  set b : Fin N := ⟨2 * j + 1, by omega⟩
  have hab : a ≠ b := fun h => by simp [a, b, Fin.ext_iff] at h
  have := hH.dotProduct_mulVec_nonneg (Pi.single a 1 + Pi.single b Complex.I)
  rw [quad2 _ a b hab] at this
  have hval : ((complexMatrix (normalCovariance N q c nu) -
        (Complex.I / 2) • complexMatrix (normalCommutator N q)) a a +
      Complex.I * (complexMatrix (normalCovariance N q c nu) -
        (Complex.I / 2) • complexMatrix (normalCommutator N q)) a b -
      Complex.I * (complexMatrix (normalCovariance N q c nu) -
        (Complex.I / 2) • complexMatrix (normalCommutator N q)) b a +
      (complexMatrix (normalCovariance N q c nu) -
        (Complex.I / 2) • complexMatrix (normalCommutator N q)) b b) =
      ((2 * nu j - 1 : ℝ) : ℂ) := by
    have ha2 : (2 * j) / 2 = j := by omega
    have hb2 : (2 * j + 1) / 2 = j := by omega
    simp [complexMatrix, normalCovariance, normalCommutator, a, b, diagonal_apply, Fin.ext_iff,
      ha2, hb2, show 2 * j < 2 * q by omega, show 2 * j + 1 < 2 * q by omega]
    ring_nf
    rw [Complex.I_sq]
    push_cast
    ring
  rw [hval] at this
  have := Complex.zero_le_real.1 this
  linarith

end X5GW

open QAlgorithms.Papers.Independent.Frontier18.P11 in
theorem solution (s : ℕ)
    (mu Delta : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ)
    (hmu : mu.transpose = mu) (hDelta : Delta.transpose = -Delta)
    (hpositive :
      (complexMatrix mu - (Complex.I / 2) • complexMatrix Delta).PosSemidef) :
    ∃ (q c z : ℕ) (nu : ℕ → ℝ)
        (T : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ),
      2 * q = Delta.rank ∧
      2 * q + c = mu.rank ∧
      2 * q + c + z = 2 * s ∧
      (∀ j < q, (1 / 2 : ℝ) ≤ nu j) ∧
      T.det ≠ 0 ∧
      T.transpose * mu * T = normalCovariance (2 * s) q c nu ∧
      T.transpose * Delta * T = normalCommutator (2 * s) q := by
  obtain ⟨q, c, z, nu, T, hsum, hnu, hdet, h1, h2⟩ :=
    X5GW.gw_main mu Delta hmu hDelta hpositive
  have hdet' : T.transpose.det ≠ 0 := by rwa [Matrix.det_transpose]
  have r : ∀ X : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ, (T.transpose * X * T).rank = X.rank := by
    intro X
    rw [Matrix.rank_mul_eq_left_of_det_ne_zero T _ hdet,
      Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hdet']
  refine ⟨q, c, z, nu, T, ?_, ?_, hsum, fun j hj => X5GW.nu_half mu Delta T q c nu hpositive
    (by omega) h1 h2 j hj, hdet, h1, h2⟩
  · rw [← r Delta, h2, X5GW.ncom_rank _ _ (by omega)]
  · rw [← r mu, h1, X5GW.ncov_rank _ _ _ _ hnu (by omega)]


