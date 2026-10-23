-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P10.minimalGaussianPurification
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:51:31.550332+00:00
-- url     : https://prove2.me/submissions/0a3adf40-0ab2-43c2-885c-14ed60f46f70

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10
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
open scoped Matrix ComplexOrder

namespace X5MGP
open QAlgorithms.Papers.Independent.Dependency50.P10 Matrix

variable {n : ℕ}

lemma cx_mul {a b c : Type*} [Fintype b] (A : Matrix a b ℝ) (B : Matrix b c ℝ) :
    complexify (A * B) = complexify A * complexify B := by
  ext i j; simp [complexify, Matrix.mul_apply]

lemma cx_transpose {a b : Type*} (A : Matrix a b ℝ) : complexify Aᵀ = (complexify A)ᴴ := by
  ext i j; simp [complexify, Matrix.conjTranspose_apply]

lemma cx_neg {a b : Type*} (A : Matrix a b ℝ) : complexify (-A) = -complexify A := by
  ext i j; simp [complexify]

lemma cx_sub {a b : Type*} (A B : Matrix a b ℝ) :
    complexify (A - B) = complexify A - complexify B := by
  ext i j; simp [complexify]

lemma cx_mulVec {a : Type*} [Fintype a] (A : Matrix a a ℝ) (x : a → ℝ) :
    complexify A *ᵥ (fun i => (x i : ℂ)) = fun i => ((A *ᵥ x) i : ℂ) := by
  ext i; simp [complexify, Matrix.mulVec, dotProduct]

lemma cx_det {a : Type*} [Fintype a] [DecidableEq a] (A : Matrix a a ℝ) :
    (complexify A).det = (A.det : ℂ) := by
  have : complexify A = (Complex.ofRealHom).mapMatrix A := rfl
  rw [this, ← RingHom.map_det]; rfl

lemma cx_submatrix {a b c d : Type*} (A : Matrix a b ℝ) (r : c → a) (s : d → b) :
    complexify (A.submatrix r s) = (complexify A).submatrix r s := rfl

lemma phys_congr {a : Type*} [Fintype a] (omega G T : Matrix a a ℝ)
    (hT : T * omega * Tᵀ = omega) (h : physicalCovariance G omega) :
    physicalCovariance (T * G * Tᵀ) omega := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, h.1,
      Matrix.mul_assoc]
  have := h.2.mul_mul_conjTranspose_same (complexify T)
  convert this using 1
  conv_lhs => rw [← hT]
  simp only [cx_mul, cx_transpose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul]

lemma exists_factor {a : Type*} [Fintype a] [DecidableEq a] (K : Matrix a a ℂ)
    (hK : K.PosSemidef) : ∃ Z : Matrix a a ℂ, Z * Zᴴ = K := by
  have hH := hK.isHermitian
  set U : Matrix a a ℂ := (hH.eigenvectorUnitary : Matrix a a ℂ)
  set lam := hH.eigenvalues
  have hlam : ∀ i, 0 ≤ lam i := fun i => hK.eigenvalues_nonneg i
  refine ⟨U * diagonal (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ)), ?_⟩
  conv_rhs => rw [hH.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose,
    ← Matrix.star_eq_conjTranspose]
  have hd : diagonal (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ)) *
      diagonal (star (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ))) =
      diagonal (RCLike.ofReal ∘ lam) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, Function.comp_apply]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hlam i)]
    rfl
  calc U * diagonal (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ)) *
        (diagonal (star (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ))) * star U)
      = U * (diagonal (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ)) *
        diagonal (star (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ)))) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * diagonal (RCLike.ofReal ∘ lam) * star U := by rw [hd]

lemma phys_posDef {a : Type*} [Fintype a] [DecidableEq a] (omega G : Matrix a a ℝ)
    (homt : omegaᵀ = -omega) (homd : omega.det ≠ 0)
    (h : physicalCovariance G omega) : G.PosDef := by
  obtain ⟨hVsym, h⟩ := h
  set K := complexify G - Complex.I • complexify omega with hK
  obtain ⟨Z, hZ⟩ := exists_factor K h
  have hskew : ∀ x : a → ℝ, x ⬝ᵥ (omega *ᵥ x) = 0 := by
    intro x
    have : x ⬝ᵥ (omega *ᵥ x) = -(x ⬝ᵥ (omega *ᵥ x)) := by
      conv_lhs => rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, homt,
        Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]
    linarith
  have key : ∀ x : a → ℝ,
      star (fun i => (x i : ℂ)) ⬝ᵥ (K *ᵥ (fun i => (x i : ℂ))) = ((x ⬝ᵥ (G *ᵥ x) : ℝ) : ℂ) := by
    intro x
    rw [hK, Matrix.sub_mulVec, Matrix.smul_mulVec, cx_mulVec, cx_mulVec, dotProduct_sub,
      dotProduct_smul]
    have h0 := hskew x
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum]
    simp only [dotProduct] at h0
    rw [h0]; simp
  have hV' : G.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hVsym]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hV' fun x hx => ?_
  simp only [star_trivial]
  have h1 := h.dotProduct_mulVec_nonneg (fun i => (x i : ℂ))
  rw [key] at h1
  have h2 := Complex.zero_le_real.1 h1
  refine lt_of_le_of_ne h2 fun h3 => hx ?_
  have h4 := key x
  rw [← h3, ← hZ] at h4
  simp only [Complex.ofReal_zero] at h4
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec] at h4
  have h5 : star (fun i => (x i : ℂ)) ᵥ* Z = star (Zᴴ *ᵥ (fun i => (x i : ℂ))) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [h5, dotProduct_star_self_eq_zero] at h4
  have h6 : K *ᵥ (fun i => (x i : ℂ)) = 0 := by
    rw [← hZ, ← Matrix.mulVec_mulVec, h4, Matrix.mulVec_zero]
  rw [hK, Matrix.sub_mulVec, Matrix.smul_mulVec, cx_mulVec, cx_mulVec] at h6
  have h7 : omega *ᵥ x = 0 := by
    ext i
    have := congrFun h6 i
    have := congrArg Complex.im this
    simpa using this
  exact Matrix.eq_zero_of_mulVec_eq_zero homd h7

lemma thermal_ge (D : Fin n → ℝ) (h : physicalCovariance (thermalCovariance D) (sigma n))
    (k : Fin n) : 1 ≤ D k := by
  set z : Phase n → ℂ := Sum.elim (fun j => if j = k then 1 else 0)
    (fun j => if j = k then -Complex.I else 0)
  have h1 := h.2.dotProduct_mulVec_nonneg z
  have key : star z ⬝ᵥ ((complexify (thermalCovariance D) - Complex.I • complexify (sigma n))
      *ᵥ z) = ((2 * (D k - 1) : ℝ) : ℂ) := by
    simp [z, dotProduct, Matrix.mulVec, thermalCovariance, sigma, complexify, Matrix.diagonal_apply,
      Matrix.sub_apply, Matrix.one_apply, Fintype.sum_sum_type]
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    apply Complex.ext <;> simp <;> ring
  rw [key] at h1
  have := Complex.zero_le_real.1 h1
  linarith

lemma det_T {N : ℕ} (T : Matrix (Phase N) (Phase N) ℝ) (hT : T * sigma N * Tᵀ = sigma N) :
    T.det ^ 2 = 1 := by
  have := congrArg Matrix.det hT
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at this
  have h := sigma_det N
  have : (T.det ^ 2 - 1) * (sigma N).det = 0 := by linear_combination this
  rcases mul_eq_zero.1 this with h1 | h1
  · linear_combination h1
  · exact absurd h1 h

/-- Structure of physical covariances. -/
theorem decomp (G : Matrix (Phase n) (Phase n) ℝ) (hG : physicalCovariance G (sigma n)) :
    ∃ D : Fin n → ℝ, ∃ T : Matrix (Phase n) (Phase n) ℝ, (∀ k, 1 ≤ D k) ∧
      T * sigma n * Tᵀ = sigma n ∧ G = T * thermalCovariance D * Tᵀ ∧ IsUnit T.det := by
  obtain ⟨D, T, -, hT, hGT⟩ := williamson_phase G (phys_posDef _ _ (sigma_t n) (sigma_det n) hG)
  have hTd : IsUnit T.det := by
    have := det_T T hT
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0] at this; norm_num at this
  refine ⟨D, T, fun k => ?_, hT, hGT, hTd⟩
  have hTi : T⁻¹ * sigma n * T⁻¹ᵀ = sigma n := by
    conv_lhs => rw [← hT]
    rw [Matrix.transpose_nonsing_inv]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose]), Matrix.mul_one,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mul]
  have hH : thermalCovariance D = T⁻¹ * G * T⁻¹ᵀ := by
    rw [hGT, Matrix.transpose_nonsing_inv]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose]), Matrix.mul_one,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mul]
  apply thermal_ge D _ k
  rw [hH]
  exact phys_congr _ _ _ hTi hG

end X5MGP

noncomputable section
open scoped Matrix ComplexOrder

namespace X5MGP
open QAlgorithms.Papers.Independent.Dependency50.P10 Matrix

variable {n : ℕ}

lemma card_elim {α β : Type*} [Fintype α] [Fintype β] (f : α → ℂ) (g : β → ℂ) :
    Fintype.card {i : α ⊕ β // Sum.elim f g i ≠ 0} =
      Fintype.card {i // f i ≠ 0} + Fintype.card {i // g i ≠ 0} := by
  rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
  rfl

lemma cx_thermal (E : Fin n → ℝ) :
    complexify (thermalCovariance E) = diagonal (Sum.elim (fun j => (E j : ℂ)) (fun j => (E j : ℂ))) := by
  ext (i | i) (j | j) <;> simp [complexify, thermalCovariance, diagonal_apply] <;> split_ifs <;> simp

lemma rank_cx_thermal (E : Fin n → ℝ) :
    (complexify (thermalCovariance E)).rank =
      2 * (Finset.univ.filter (fun j => E j ≠ 0)).card := by
  rw [cx_thermal, rank_diagonal, card_elim, Fintype.card_subtype]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  ring

lemma thermal_mul (E F : Fin n → ℝ) :
    thermalCovariance E * thermalCovariance F = thermalCovariance (E * F) := by
  simp [thermalCovariance, fromBlocks_multiply, diagonal_mul_diagonal]

lemma thermal_inv (D : Fin n → ℝ) (hD : ∀ k, D k ≠ 0) :
    (thermalCovariance D)⁻¹ = thermalCovariance (fun j => (D j)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [thermal_mul]
  have : (fun j => (D j)⁻¹) * D = fun _ => 1 := by
    funext j; simp [hD j]
  rw [this]
  simp [thermalCovariance, ← fromBlocks_one]

lemma sigma_thermal (E : Fin n → ℝ) :
    sigma n * thermalCovariance E * (sigma n)ᵀ = thermalCovariance E := by
  simp only [sigma, thermalCovariance, fromBlocks_transpose, fromBlocks_multiply]
  simp

lemma isUnit_cx {a : Type*} [Fintype a] [DecidableEq a] (T : Matrix a a ℝ) (h : IsUnit T.det) :
    IsUnit (complexify T).det := by
  rw [cx_det]; exact (isUnit_iff_ne_zero.2 (by exact_mod_cast h.ne_zero))

lemma rank_congr {a : Type*} [Fintype a] [DecidableEq a] (T : Matrix a a ℝ) (h : IsUnit T.det)
    (K : Matrix a a ℂ) : (complexify T * K * (complexify T)ᴴ).rank = K.rank := by
  have h1 := isUnit_cx T h
  have h2 : IsUnit (complexify T)ᴴ.det := by
    rw [det_conjTranspose]; exact h1.star
  rw [rank_mul_eq_left_of_isUnit_det _ _ h2, rank_mul_eq_right_of_isUnit_det _ _ h1]

lemma rank_HsH (D : Fin n → ℝ) (hD : ∀ k, 0 < D k) :
    (complexify (thermalCovariance D - sigma n * (thermalCovariance D)⁻¹ * (sigma n)ᵀ)).rank =
      2 * (Finset.univ.filter (fun j => D j ≠ 1)).card := by
  rw [thermal_inv D (fun k => (hD k).ne'), sigma_thermal]
  have : thermalCovariance D - thermalCovariance (fun j => (D j)⁻¹) =
      thermalCovariance (fun j => D j - (D j)⁻¹) := by
    ext (i | i) (j | j) <;> simp [thermalCovariance, diagonal_apply] <;> split_ifs <;> simp
  rw [this, rank_cx_thermal]
  congr 2
  apply Finset.filter_congr
  intro j _
  have := hD j
  constructor
  · intro h1 h2; apply h1; rw [h2]; norm_num
  · intro h1 h2; apply h1
    have h3 : D j * D j = 1 := by field_simp at h2; linarith
    nlinarith

lemma rank_HmS (D : Fin n → ℝ) (hD : ∀ k, 0 < D k) :
    (complexify (thermalCovariance D) - Complex.I • complexify (sigma n)).rank =
      n + (Finset.univ.filter (fun j => D j ≠ 1)).card := by
  set Dc : Fin n → ℂ := fun j => (D j : ℂ)
  set Di : Fin n → ℂ := fun j => ((D j)⁻¹ : ℂ)
  have hDc : ∀ j, Dc j ≠ 0 := fun j => by simp [Dc, (hD j).ne']
  have hM : complexify (thermalCovariance D) - Complex.I • complexify (sigma n) =
      fromBlocks (diagonal Dc) (-Complex.I • 1) (Complex.I • 1) (diagonal Dc) := by
    ext (i | i) (j | j) <;>
      simp [complexify, thermalCovariance, sigma, diagonal_apply, one_apply, Dc] <;>
      split_ifs <;> simp
  set L : Matrix (Phase n) (Phase n) ℂ := fromBlocks 1 0 (-Complex.I • diagonal Di) 1
  set R : Matrix (Phase n) (Phase n) ℂ := fromBlocks 1 (Complex.I • diagonal Di) 0 1
  have hL : IsUnit L.det := by simp [L, det_fromBlocks_zero₁₂]
  have hR : IsUnit R.det := by simp [R, det_fromBlocks_zero₂₁]
  have hDi : ∀ j, Dc j * Di j = 1 := fun j => by
    simp [Dc, Di]; field_simp [(hD j).ne']
  have hLMR : L * fromBlocks (diagonal Dc) (-Complex.I • 1) (Complex.I • 1) (diagonal Dc) * R =
      diagonal (Sum.elim Dc (Dc - Di)) := by
    simp only [L, R, fromBlocks_multiply]
    have e1 : diagonal (fun i => Dc i * Di i) = 1 := by
      rw [show (fun i => Dc i * Di i) = fun _ => 1 from funext hDi]; exact diagonal_one
    have e2 : diagonal (fun i => Di i * Dc i) = 1 := by
      rw [show (fun i => Di i * Dc i) = fun _ => 1 from funext fun i => by rw [mul_comm, hDi]]
      exact diagonal_one
    rw [← fromBlocks_diagonal]
    congr 1
    · simp
    · simp [e1]
    · simp [e2]
    · simp [e2, smul_smul, diagonal_sub, sub_eq_add_neg]
      intro i; ring
  rw [hM, ← rank_mul_eq_right_of_isUnit_det L _ hL, ← rank_mul_eq_left_of_isUnit_det R _ hR, hLMR,
    rank_diagonal, card_elim]
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have h1 : (Finset.univ.filter fun j => Dc j ≠ 0) = Finset.univ :=
    Finset.filter_true_of_mem fun j _ => hDc j
  rw [h1, Finset.card_univ, Fintype.card_fin]
  congr 2
  apply Finset.filter_congr
  intro j _
  have := hD j
  simp only [Pi.sub_apply, Dc, Di, ne_eq]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_sub, Complex.ofReal_eq_zero, sub_eq_zero]
  constructor
  · intro h1 h2; apply h1; rw [h2]; norm_num
  · intro h1 h2; apply h1
    have h3 : D j * D j = 1 := by field_simp at h2; linarith
    nlinarith

end X5MGP

noncomputable section
open scoped Matrix ComplexOrder

namespace X5MGP
open QAlgorithms.Papers.Independent.Dependency50.P10 Matrix

variable {n : ℕ}

def zc (α β : Fin n → ℂ) : (Fin n ⊕ Fin n) → (Phase n ⊕ Phase n) → ℂ
  | .inl r, .inl (.inl i) => if r = i then α i else 0
  | .inl r, .inl (.inr i) => if r = i then -Complex.I * α i else 0
  | .inl r, .inr (.inl i) => if r = i then Complex.I * β i else 0
  | .inl r, .inr (.inr i) => if r = i then -β i else 0
  | .inr r, .inl (.inl i) => if r = i then Complex.I * β i else 0
  | .inr r, .inl (.inr i) => if r = i then -β i else 0
  | .inr r, .inr (.inl i) => if r = i then α i else 0
  | .inr r, .inr (.inr i) => if r = i then -Complex.I * α i else 0

lemma purif_eq (D : Fin n → ℝ) (α β : Fin n → ℝ)
    (h1 : ∀ i, α i * α i + β i * β i = D i) (h2 : ∀ i, α i * α i - β i * β i = 1)
    (h3 : ∀ i, 2 * α i * β i = -thermalF (D i)) :
    complexify (thermalPurification D) - Complex.I • complexify (jointSigma n n) =
      (Matrix.of (zc (fun i => (α i : ℂ)) (fun i => (β i : ℂ))))ᴴ *
        Matrix.of (zc (fun i => (α i : ℂ)) (fun i => (β i : ℂ))) := by
  have c1 : ∀ i, (α i : ℂ) * α i + β i * β i = D i := fun i => by exact_mod_cast h1 i
  have c2 : ∀ i, (α i : ℂ) * α i - β i * β i = 1 := fun i => by exact_mod_cast h2 i
  have c3 : ∀ i, 2 * (α i : ℂ) * β i = -(thermalF (D i) : ℂ) := fun i => by exact_mod_cast h3 i
  ext ((i | i) | (i | i)) ((j | j) | (j | j)) <;>
    simp [Matrix.mul_apply, conjTranspose_apply, Fintype.sum_sum_type, zc, complexify,
      thermalPurification, thermalCovariance, thermalCross, jointSigma, sigma, diagonal_apply,
      one_apply] <;>
    split_ifs <;> subst_vars <;> simp [Complex.conj_ofReal] <;> (try contradiction) <;> (try ring_nf) <;> (try simp) <;>
    first
    | linear_combination -(c1 _)
    | linear_combination (c3 _)
    | linear_combination -Complex.I * (c2 _)
    | linear_combination Complex.I * (c2 _)

end X5MGP

noncomputable section
open scoped Matrix ComplexOrder

namespace X5MGP
open QAlgorithms.Papers.Independent.Dependency50.P10 Matrix

variable {n : ℕ}

lemma thermal_t (E : Fin n → ℝ) : (thermalCovariance E)ᵀ = thermalCovariance E := by
  simp [thermalCovariance, fromBlocks_transpose]

lemma cross_t (D : Fin n → ℝ) : (thermalCross D)ᵀ = thermalCross D := by
  simp [thermalCross, fromBlocks_transpose]

lemma purif_phys (D : Fin n → ℝ) (hD : ∀ k, 1 ≤ D k) :
    physicalCovariance (thermalPurification D) (jointSigma n n) := by
  refine ⟨?_, ?_⟩
  · simp only [thermalPurification, fromBlocks_transpose, thermal_t, Matrix.transpose_transpose]
  set α : Fin n → ℝ := fun i => Real.sqrt ((D i + 1) / 2)
  set β : Fin n → ℝ := fun i => Real.sqrt ((D i - 1) / 2)
  have ha : ∀ i, α i * α i = (D i + 1) / 2 := fun i =>
    Real.mul_self_sqrt (by linarith [hD i])
  have hb : ∀ i, β i * β i = (D i - 1) / 2 := fun i =>
    Real.mul_self_sqrt (by linarith [hD i])
  rw [purif_eq D α β (fun i => by rw [ha, hb]; ring) (fun i => by rw [ha, hb]; ring) (fun i => ?_)]
  · exact Matrix.posSemidef_conjTranspose_mul_self _
  · have h0 : 0 ≤ 2 * α i * β i := by positivity
    simp only [thermalF, neg_neg]
    rw [← Real.sqrt_sq h0]
    congr 1
    have : (2 * α i * β i) ^ 2 = 4 * (α i * α i) * (β i * β i) := by ring
    rw [this, ha, hb]; ring

def fmap {m : ℕ} (ι : Fin m → Fin n) : Phase n ⊕ Phase m → Phase n ⊕ Phase n :=
  Sum.map id (Sum.map ι ι)

lemma fmap_inj {m : ℕ} (ι : Fin m → Fin n) (hι : Function.Injective ι) :
    Function.Injective (fmap ι) :=
  Sum.map_injective.2 ⟨Function.injective_id, Sum.map_injective.2 ⟨hι, hι⟩⟩

lemma joint_sub {m : ℕ} (ι : Fin m → Fin n) (hι : Function.Injective ι) :
    (jointSigma n n).submatrix (fmap ι) (fmap ι) = jointSigma n m := by
  ext ((i | i) | (i | i)) ((j | j) | (j | j)) <;>
    simp [fmap, jointSigma, sigma, one_apply, hι.eq_iff]

lemma thermal_sub {m : ℕ} (D : Fin n → ℝ) (ι : Fin m → Fin n) (hι : Function.Injective ι) :
    (thermalCovariance D).submatrix (Sum.map ι ι) (Sum.map ι ι) = thermalCovariance (D ∘ ι) := by
  ext (i | i) (j | j) <;> simp [thermalCovariance, diagonal_apply, hι.eq_iff] <;>
    split_ifs <;> simp_all

lemma det_thermal (E : Fin n → ℝ) : (thermalCovariance E).det = (∏ j, E j) ^ 2 := by
  rw [thermalCovariance, det_fromBlocks_zero₂₁, det_diagonal]; ring

lemma purif_sub_eq {m : ℕ} (D : Fin n → ℝ) (ι : Fin m → Fin n) :
    (thermalPurification D).submatrix (fmap ι) (fmap ι) =
      fromBlocks (thermalCovariance D) ((thermalCross D).submatrix id (Sum.map ι ι))
        ((thermalCross D).submatrix (Sum.map ι ι) id)
        ((thermalCovariance D).submatrix (Sum.map ι ι) (Sum.map ι ι)) := by
  ext (x | x) (y | y) <;> simp [fmap, thermalPurification, cross_t]

lemma cross_mul (D E : Fin n → ℝ) :
    thermalCross D * thermalCovariance E * thermalCross D =
      thermalCovariance (fun j => thermalF (D j) * E j * thermalF (D j)) := by
  rw [thermalCross, thermalCovariance, thermalCovariance, fromBlocks_multiply, fromBlocks_multiply]
  simp [diagonal_mul_diagonal]

lemma purif_sub_det {m : ℕ} (D : Fin n → ℝ) (hD : ∀ k, 1 ≤ D k) (ι : Fin m → Fin n)
    (hι : Function.Injective ι) (hout : ∀ j, (∀ k, ι k ≠ j) → D j = 1) :
    ((thermalPurification D).submatrix (fmap ι) (fmap ι)).det = 1 := by
  have hD0 : ∀ k, D k ≠ 0 := fun k => by linarith [hD k]
  rw [purif_sub_eq]
  letI : Invertible (thermalCovariance D) :=
    ⟨thermalCovariance (fun j => (D j)⁻¹),
      by rw [thermal_mul]; convert (show thermalCovariance (fun _ : Fin n => (1 : ℝ)) = 1 by
            simp [thermalCovariance, ← fromBlocks_one]) using 2; funext j; simp [hD0 j],
      by rw [thermal_mul]; convert (show thermalCovariance (fun _ : Fin n => (1 : ℝ)) = 1 by
            simp [thermalCovariance, ← fromBlocks_one]) using 2; funext j; simp [hD0 j]⟩
  rw [det_fromBlocks₁₁]
  have hinv : ⅟(thermalCovariance D) = thermalCovariance (fun j => (D j)⁻¹) := rfl
  rw [hinv]
  have hS : (thermalCross D).submatrix (Sum.map ι ι) id * thermalCovariance (fun j => (D j)⁻¹) *
      (thermalCross D).submatrix id (Sum.map ι ι) =
      (thermalCovariance (fun j => thermalF (D j) * (D j)⁻¹ * thermalF (D j))).submatrix
        (Sum.map ι ι) (Sum.map ι ι) := by
    rw [← cross_mul]
    rw [← Matrix.submatrix_id_id (thermalCovariance fun j => (D j)⁻¹), Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]
    simp
  rw [hS, thermal_sub D ι hι, thermal_sub _ ι hι]
  have hsub : thermalCovariance (D ∘ ι) -
      thermalCovariance ((fun j => thermalF (D j) * (D j)⁻¹ * thermalF (D j)) ∘ ι) =
      thermalCovariance (fun k => (D (ι k))⁻¹) := by
    have hf : ∀ x, thermalF (D x) * thermalF (D x) = D x ^ 2 - 1 := fun x => by
      simp only [thermalF, neg_mul_neg]
      exact Real.mul_self_sqrt (by nlinarith [hD x])
    have key : ∀ x, D x - thermalF (D x) * (D x)⁻¹ * thermalF (D x) = (D x)⁻¹ := by
      intro x
      rw [show thermalF (D x) * (D x)⁻¹ * thermalF (D x) = (thermalF (D x) * thermalF (D x)) / D x
        by ring, hf]
      field_simp [hD0 x]; ring
    ext (i | i) (j | j) <;> simp [thermalCovariance, diagonal_apply] <;> split_ifs <;> simp [key]
  rw [hsub, det_thermal, det_thermal]
  have hprod : ∏ k, D (ι k) = ∏ j, D j := by
    rw [← Finset.prod_image (fun x _ y _ h => hι h)]
    apply Finset.prod_subset (Finset.subset_univ _)
    intro j _ hj
    apply hout
    intro k hk
    exact hj (Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩)
  have hne : ∏ j, D j ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hD0 j
  rw [Finset.prod_inv_distrib, hprod]
  field_simp

end X5MGP

noncomputable section
open scoped Matrix ComplexOrder

namespace X5MGP
open QAlgorithms.Papers.Independent.Dependency50.P10 Matrix

variable {n : ℕ}

lemma congr_K {a : Type*} [Fintype a] (omega G T H : Matrix a a ℝ)
    (hT : T * omega * Tᵀ = omega) (hG : G = T * H * Tᵀ) :
    complexify G - Complex.I • complexify omega =
      complexify T * (complexify H - Complex.I • complexify omega) * (complexify T)ᴴ := by
  conv_lhs => rw [hG, ← hT]
  simp only [cx_mul, cx_transpose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]

lemma inv_symp {N : ℕ} (T : Matrix (Phase N) (Phase N) ℝ) (hT : T * sigma N * Tᵀ = sigma N)
    (hTd : IsUnit T.det) : T⁻¹ * sigma N * T⁻¹ᵀ = sigma N := by
  conv_lhs => rw [← hT]
  rw [Matrix.transpose_nonsing_inv]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose]), Matrix.mul_one,
    ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mul]

lemma inv_congr (G T H : Matrix (Phase n) (Phase n) ℝ) (hT : T * sigma n * Tᵀ = sigma n)
    (hTd : IsUnit T.det) (hG : G = T * H * Tᵀ) :
    G - sigma n * G⁻¹ * (sigma n)ᵀ = T * (H - sigma n * H⁻¹ * (sigma n)ᵀ) * Tᵀ := by
  have hTt : IsUnit Tᵀ.det := by rwa [Matrix.det_transpose]
  have e1 : sigma n * Tᵀ⁻¹ = T * sigma n := by
    conv_lhs => rw [← hT]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hTt, Matrix.mul_one]
  have e2 : T⁻¹ * (sigma n)ᵀ = (sigma n)ᵀ * Tᵀ := by
    have : T⁻¹ * sigma n = sigma n * Tᵀ := by
      conv_lhs => rw [← hT]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mul]
    rw [sigma_t, Matrix.mul_neg, this, Matrix.neg_mul]
  have hGi : G⁻¹ = Tᵀ⁻¹ * H⁻¹ * T⁻¹ := by
    rw [hG, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
  calc G - sigma n * G⁻¹ * (sigma n)ᵀ
      = T * H * Tᵀ - (sigma n * Tᵀ⁻¹) * H⁻¹ * (T⁻¹ * (sigma n)ᵀ) := by
        rw [hGi, hG]; simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [e1, e2]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- Reindex the joint phase space onto a single canonical one. -/
def je (n q : ℕ) : Phase n ⊕ Phase q ≃ Phase (n + q) :=
  (Equiv.sumSumSumComm (Fin n) (Fin n) (Fin q) (Fin q)).trans
    (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)

lemma je_sigma (n q : ℕ) : (sigma (n + q)).submatrix (je n q) (je n q) = jointSigma n q := by
  ext ((i | i) | (i | i)) ((j | j) | (j | j)) <;>
    simp [je, Equiv.sumSumSumComm, sigma, jointSigma, one_apply] <;>
    simp [Fin.ext_iff] <;> omega

lemma pure_rank {q : ℕ} (Γ : Matrix (Phase n ⊕ Phase q) (Phase n ⊕ Phase q) ℝ)
    (h : pureCovariance Γ (jointSigma n q)) :
    (complexify Γ - Complex.I • complexify (jointSigma n q)).rank ≤ n + q := by
  set e := je n q
  set Γ' := Γ.submatrix e.symm e.symm
  have hs : jointSigma n q = (sigma (n + q)).submatrix e e := (je_sigma n q).symm
  have hs' : sigma (n + q) = (jointSigma n q).submatrix e.symm e.symm := by rw [hs]; simp
  have hphys : physicalCovariance Γ' (sigma (n + q)) := by
    refine ⟨by rw [transpose_submatrix, h.1.1], ?_⟩
    rw [hs']
    have := h.1.2.submatrix e.symm
    convert this using 1
    ext x y; simp [Γ', complexify]
  have hdet : Γ'.det = 1 := by
    rw [det_submatrix_equiv_self]; exact h.2
  obtain ⟨D, T, hD1, hT, hGT, hTu⟩ := decomp Γ' hphys
  have hall : ∀ j, D j = 1 := by
    have h1 := congrArg Matrix.det hGT
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_thermal, hdet] at h1
    have h2 := det_T T hT
    have h3 : (∏ j, D j) ^ 2 = 1 := by
      have : (∏ j, D j) ^ 2 * T.det ^ 2 = 1 := by linear_combination -h1
      rwa [h2, mul_one] at this
    have hge : ∀ s : Finset (Fin (n + q)), 1 ≤ ∏ j ∈ s, D j := fun s => by
      simpa using Finset.prod_le_prod (fun _ _ => zero_le_one) (fun j _ => hD1 j) (s := s)
        (f := fun _ => (1 : ℝ))
    have h4 := hge Finset.univ
    have h5 : ∏ j, D j = 1 := by nlinarith
    intro j
    rw [← Finset.mul_prod_erase Finset.univ D (Finset.mem_univ j)] at h5
    have h6 := hge (Finset.univ.erase j)
    nlinarith [hD1 j]
  have hK := congr_K _ _ _ _ hT hGT
  have hr : (complexify Γ' - Complex.I • complexify (sigma (n + q))).rank = n + q := by
    rw [hK, rank_congr T hTu, rank_HmS D (fun k => by linarith [hD1 k])]
    simp [hall]
  calc (complexify Γ - Complex.I • complexify (jointSigma n q)).rank
      = ((complexify Γ' - Complex.I • complexify (sigma (n + q))).submatrix e e).rank := by
        congr 1
        rw [hs']
        ext x y; simp [Γ', complexify]
    _ ≤ _ := rank_submatrix_le _ _ _
    _ = n + q := hr

end X5MGP

noncomputable section
open scoped Matrix ComplexOrder

namespace X5MGP
open QAlgorithms.Papers.Independent.Dependency50.P10 Matrix

lemma unit_card {n : ℕ} (D : Fin n → ℝ) :
    unitCount D + (Finset.univ.filter (fun j => D j ≠ 1)).card = n := by
  unfold unitCount
  rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]

end X5MGP

open QAlgorithms.Papers.Independent.Dependency50.P10 X5MGP Matrix in
theorem solution {n : ℕ}
    (G : Matrix (Phase n) (Phase n) ℝ)
    (hG : physicalCovariance G (sigma n)) :
    ∃ D : Fin n → ℝ,
      ∃ S : Matrix (Phase n) (Phase n) ℝ,
        (∀ j, 1 ≤ D j) ∧
        S * sigma n * S.transpose = sigma n ∧
        S * G * S.transpose = thermalCovariance D ∧
        pureCovariance (thermalPurification D) (jointSigma n n) ∧
        (unitCount D = n -
          (complexify (G - sigma n * G⁻¹ * (sigma n).transpose)).rank / 2) ∧
        hasGaussianPurification G (n - unitCount D) ∧
        (∀ q : ℕ, hasGaussianPurification G q → n - unitCount D ≤ q) ∧
        (n - unitCount D =
          (complexify G - Complex.I • complexify (sigma n)).rank - n) ∧
        (2 * (n - unitCount D) =
          (complexify (G - sigma n * G⁻¹ * (sigma n).transpose)).rank) := by
  obtain ⟨D, T, hD1, hT, hGT, hTu⟩ := decomp G hG
  have hD0 : ∀ k, 0 < D k := fun k => by linarith [hD1 k]
  set s := Finset.univ.filter (fun j => D j ≠ 1) with hs
  have hcard : unitCount D + s.card = n := unit_card D
  have hm : n - unitCount D = s.card := by omega
  -- ranks
  have hr1 : (complexify (G - sigma n * G⁻¹ * (sigma n).transpose)).rank = 2 * s.card := by
    rw [inv_congr G T _ hT hTu hGT, cx_mul, cx_mul, cx_transpose, rank_congr T hTu, rank_HsH D hD0]
  have hr2 : (complexify G - Complex.I • complexify (sigma n)).rank = n + s.card := by
    rw [congr_K _ _ _ _ hT hGT, rank_congr T hTu, rank_HmS D hD0]
  refine ⟨D, T⁻¹, hD1, inv_symp T hT hTu, ?_, ⟨purif_phys D hD1, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hGT, Matrix.transpose_nonsing_inv]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose]), Matrix.mul_one,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hTu, Matrix.one_mul]
  · have := purif_sub_det D hD1 id Function.injective_id (fun j h => absurd rfl (h j))
    have hf : fmap (id : Fin n → Fin n) = id := by
      funext x; rcases x with x | (x | x) <;> rfl
    rwa [hf, submatrix_id_id] at this
  · rw [hr1]; omega
  · -- explicit purification with `n - unitCount D` ancillas
    set ι := s.orderEmbOfFin hm.symm
    have hι : Function.Injective ι := ι.injective
    have hout : ∀ j, (∀ k, ι k ≠ j) → D j = 1 := by
      intro j hj
      by_contra hne
      have : j ∈ Set.range ι := by
        rw [Finset.range_orderEmbOfFin]; simp [hs, hne]
      obtain ⟨k, hk⟩ := this
      exact hj k hk
    set Γ0 := (thermalPurification D).submatrix (fmap ι) (fmap ι)
    have hΓ0p : physicalCovariance Γ0 (jointSigma n (n - unitCount D)) := by
      refine ⟨?_, ?_⟩
      · rw [transpose_submatrix, (purif_phys D hD1).1]
      · rw [← joint_sub ι hι]
        have := (purif_phys D hD1).2.submatrix (fmap ι)
        convert this using 1
        ext x y; simp [Γ0, complexify]
    have hΓ0d : Γ0.det = 1 := purif_sub_det D hD1 ι hι hout
    set C0 := (thermalCross D).submatrix id (Sum.map ι ι)
    set B0 := (thermalCovariance D).submatrix (Sum.map ι ι) (Sum.map ι ι)
    have hΓ0 : Γ0 = fromBlocks (thermalCovariance D) C0 C0ᵀ B0 := by
      show (thermalPurification D).submatrix _ _ = _
      rw [purif_sub_eq]; congr 1
      rw [transpose_submatrix, cross_t]
    set T' : Matrix (Phase n ⊕ Phase (n - unitCount D)) (Phase n ⊕ Phase (n - unitCount D)) ℝ :=
      fromBlocks T 0 0 1
    have hT' : T' * jointSigma n (n - unitCount D) * T'ᵀ = jointSigma n (n - unitCount D) := by
      simp [T', jointSigma, fromBlocks_transpose, fromBlocks_multiply, hT]
    refine ⟨B0, T * C0, ⟨?_, ?_⟩⟩
    · have := phys_congr _ _ _ hT' hΓ0p
      convert this using 1
      rw [hΓ0, hGT]
      simp [T', fromBlocks_transpose, fromBlocks_multiply, Matrix.mul_assoc, Matrix.transpose_mul]
    · have e : fromBlocks G (T * C0) (T * C0)ᵀ B0 = T' * Γ0 * T'ᵀ := by
        rw [hΓ0, hGT]
        simp [T', fromBlocks_transpose, fromBlocks_multiply, Matrix.mul_assoc, Matrix.transpose_mul]
      rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hΓ0d]
      have : T'.det = T.det := by simp [T', det_fromBlocks_zero₂₁]
      rw [this]
      linear_combination det_T T hT
  · intro q ⟨B, C, hp⟩
    have h1 := pure_rank _ hp
    have h2 : (complexify G - Complex.I • complexify (sigma n)).rank ≤
        (complexify (fromBlocks G C Cᵀ B) - Complex.I • complexify (jointSigma n q)).rank := by
      have : complexify G - Complex.I • complexify (sigma n) =
          (complexify (fromBlocks G C Cᵀ B) - Complex.I • complexify (jointSigma n q)).submatrix
            Sum.inl Sum.inl := by
        ext x y; simp [complexify, jointSigma]
      rw [this]; exact rank_submatrix_le _ _ _
    omega
  · rw [hr2]; omega
  · rw [hr1]; omega

