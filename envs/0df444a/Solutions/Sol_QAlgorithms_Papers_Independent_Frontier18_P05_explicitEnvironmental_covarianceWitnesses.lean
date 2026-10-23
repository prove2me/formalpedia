-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P05.explicitEnvironmental_covarianceWitnesses
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:21:26.508875+00:00
-- url     : https://prove2.me/submissions/2c934648-0017-4dcb-8028-e10ef76f2fb4

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P05
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

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace Matrix

namespace X5MGP
open QAlgorithms.Papers.Independent.Dependency50.P10 QAlgorithms.Papers.Independent.Frontier18.P05
  Matrix

lemma skew_normal {n : ℕ} (M : Matrix (Phase n) (Phase n) ℝ) (hMt : Mᵀ = -M) :
    ∃ O : Matrix (Phase n) (Phase n) ℝ, ∃ mu : Fin n → ℝ,
      O * Oᵀ = 1 ∧ (∀ j, 0 ≤ mu j) ∧ O * M * Oᵀ = normalizedDefect mu := by
  let A : EuclideanSpace ℝ (Phase n) →ₗ[ℝ] EuclideanSpace ℝ (Phase n) := Matrix.toLpLin 2 2 M
  have hin : ∀ x y : EuclideanSpace ℝ (Phase n),
      ⟪x, A y⟫ = WithLp.ofLp x ⬝ᵥ (M *ᵥ WithLp.ofLp y) := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply]
    simp [dotProduct_comm]
  have hskew : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫ := by
    intro x y
    rw [real_inner_comm, hin, hin, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hMt,
      Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]
  obtain ⟨v, mu, -, hmu, hG, hO⟩ := sk_core A hskew n ⊤ (fun _ _ => Submodule.mem_top)
    (by rw [finrank_top, finrank_euclideanSpace]; simp; ring)
  set e := ep n
  refine ⟨Matrix.of fun x i => WithLp.ofLp (v (e.symm x)) i, mu, ?_, hmu, ?_⟩
  · ext x y
    have := hG (e.symm x) (e.symm y)
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    simp only [e.symm.injective.eq_iff] at this
    rw [← this]
    simp [dotProduct, mul_comm]
  · ext x y
    have := hO (e.symm x) (e.symm y)
    rw [hin] at this
    have h2 : (Matrix.of fun x i => WithLp.ofLp (v (e.symm x)) i) * M *
        (Matrix.of fun x i => WithLp.ofLp (v (e.symm x)) i)ᵀ =
        Matrix.of fun x y => WithLp.ofLp (v (e.symm x)) ⬝ᵥ (M *ᵥ WithLp.ofLp (v (e.symm y))) := by
      ext x y
      rw [Matrix.mul_assoc]
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [h2, Matrix.of_apply, this]
    rcases x with i | i <;> rcases y with j | j <;>
      simp [e, ep, skw, interleavedSymplecticForm, normalizedDefect, diagonal_apply, eq_comm] <;>
      split_ifs <;> simp_all

end X5MGP

noncomputable section
open scoped Matrix ComplexOrder

namespace X5MGP
open QAlgorithms.Papers.Independent.Dependency50.P10 QAlgorithms.Papers.Independent.Frontier18.P05
  Matrix

lemma psd_sqrt {a : Type*} [Fintype a] [DecidableEq a] (V : Matrix a a ℝ) (hV : V.PosDef) :
    ∃ R : Matrix a a ℝ, Rᵀ = R ∧ R.PosDef ∧ R * R = V := by
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
  have hUU : U.transpose * U = 1 := by
    have := (hM.eigenvectorUnitary).2
    rw [Matrix.mem_unitaryGroup_iff'] at this
    rwa [hst] at this
  have hUU' : U * U.transpose = 1 := by
    have := (hM.eigenvectorUnitary).2
    rw [Matrix.mem_unitaryGroup_iff] at this
    rwa [hst] at this
  set Dq := Matrix.diagonal (fun i => Real.sqrt (ev i))
  refine ⟨U * Dq * U.transpose, ?_, ?_, ?_⟩
  · simp [Matrix.transpose_mul, Dq, Matrix.mul_assoc]
  · have hD : Dq.PosDef := Matrix.PosDef.diagonal fun i => Real.sqrt_pos.2 (hev i)
    have := hD.mul_mul_conjTranspose_same (B := U) (by
      intro x y hxy
      have := congrArg (fun z => z ᵥ* U.transpose) hxy
      simpa [Matrix.vecMul_vecMul, hUU'] using this)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  · have hDD : Dq * Dq = Matrix.diagonal ev := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1; funext i; exact Real.mul_self_sqrt (hev i).le
    rw [hVU]
    calc U * Dq * Uᵀ * (U * Dq * Uᵀ) = U * Dq * (Uᵀ * U) * Dq * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = U * diagonal ev * Uᵀ := by rw [hUU, Matrix.mul_one, Matrix.mul_assoc U Dq Dq, hDD]

lemma defect_ge {n : ℕ} (mu : Fin n → ℝ)
    (h : (complexify (1 : Matrix (Phase n) (Phase n) ℝ) -
      Complex.I • complexify (normalizedDefect mu)).PosSemidef) (k : Fin n) : mu k ≤ 1 := by
  set z : Phase n → ℂ := Sum.elim (fun j => if j = k then 1 else 0)
    (fun j => if j = k then -Complex.I else 0)
  have h1 := h.dotProduct_mulVec_nonneg z
  have key : star z ⬝ᵥ ((complexify (1 : Matrix (Phase n) (Phase n) ℝ) -
      Complex.I • complexify (normalizedDefect mu)) *ᵥ z) = ((2 * (1 - mu k) : ℝ) : ℂ) := by
    simp [z, dotProduct, Matrix.mulVec, normalizedDefect, complexify, Matrix.diagonal_apply,
      Matrix.sub_apply, Matrix.one_apply, Fintype.sum_sum_type]
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    apply Complex.ext <;> simp <;> ring
  rw [key] at h1
  have := Complex.zero_le_real.1 h1
  linarith

end X5MGP

noncomputable section
open scoped Matrix ComplexOrder

namespace X5MGP
open QAlgorithms.Papers.Independent.Dependency50.P10 QAlgorithms.Papers.Independent.Frontier18.P05
  Matrix

variable {n : ℕ}

lemma FJF (mu : Fin n → ℝ) (hmu : ∀ j, 0 ≤ mu j) :
    fullCoupling mu * jointSigma n n * (fullCoupling mu)ᵀ = normalizedDefect mu := by
  have ha : ∀ j, couplingWeight (mu j) * couplingWeight (mu j) = if mu j = 0 then 1 else mu j := by
    intro j; unfold couplingWeight; split_ifs with h
    · ring
    · exact Real.mul_self_sqrt (hmu j)
  ext (i | i) (j | j) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, fullCoupling, thermalCovariance, nullSwap,
      diagonal_apply, jointSigma, sigma, one_apply, normalizedDefect] <;>
    split_ifs <;> subst_vars <;> simp_all [ha, couplingWeight]

lemma FGF (mu : Fin n → ℝ) (hmu : ∀ j, 0 ≤ mu j) (hmu1 : ∀ j, mu j ≤ 1) :
    fullCoupling mu * thermalPurification (fun j => environmentVariance (mu j)) *
      (fullCoupling mu)ᵀ = 1 := by
  have hf0 : thermalF (5 / 4) = -3 / 4 := by
    unfold thermalF
    rw [show ((5 : ℝ) / 4) ^ 2 - 1 = (3 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  ext (i | i) (j | j) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, fullCoupling, thermalCovariance, nullSwap,
      diagonal_apply, thermalPurification, thermalCross, one_apply] <;>
    split_ifs <;> subst_vars <;> simp_all [couplingWeight, environmentVariance] <;>
    first
    | (norm_num; done)
    | (rw [mul_right_comm, Real.mul_self_sqrt (hmu _)]; field_simp)

end X5MGP

noncomputable section
open scoped Matrix ComplexOrder

namespace X5MGP
open QAlgorithms.Papers.Independent.Dependency50.P10 QAlgorithms.Papers.Independent.Frontier18.P05
  Matrix

lemma sum_range_eq {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq γ] (e : β → γ)
    (he : Function.Injective e) (g : γ → ℝ) (hg : ∀ u, (∀ l, e l ≠ u) → g u = 0) :
    ∑ l, g (e l) = ∑ u, g u := by
  rw [← Finset.sum_image (fun x _ y _ h => he h)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro u _ hu
  apply hg
  intro l hl
  exact hu (Finset.mem_image.2 ⟨l, Finset.mem_univ _, hl⟩)

lemma sub_zero_cols {α β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq γ]
    (B : Matrix α γ ℝ) (M : Matrix γ γ ℝ) (e : β → γ) (he : Function.Injective e)
    (hB : ∀ i u, (∀ l, e l ≠ u) → B i u = 0) :
    B.submatrix id e * M.submatrix e e * (B.submatrix id e)ᵀ = B * M * Bᵀ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, id]
  have inner : ∀ w, ∑ l, B i (e l) * M (e l) w = ∑ u, B i u * M u w := fun w =>
    sum_range_eq e he (fun u => B i u * M u w) (fun u hu => by rw [hB i u hu, zero_mul])
  simp_rw [inner]
  exact sum_range_eq e he (fun w => (∑ u, B i u * M u w) * B j w)
    (fun w hw => by rw [hB j w hw, mul_zero])

lemma card_elimR {α β : Type*} [Fintype α] [Fintype β] (f : α → ℝ) (g : β → ℝ) :
    Fintype.card {i : α ⊕ β // Sum.elim f g i ≠ 0} =
      Fintype.card {i // f i ≠ 0} + Fintype.card {i // g i ≠ 0} := by
  rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
  rfl

lemma rank_thermalR {n : ℕ} (E : Fin n → ℝ) :
    (thermalCovariance E).rank = 2 * (Finset.univ.filter (fun j => E j ≠ 0)).card := by
  rw [thermalCovariance, fromBlocks_diagonal, rank_diagonal, card_elimR, Fintype.card_subtype]
  ring

lemma rank_defect {n : ℕ} (mu : Fin n → ℝ) :
    (normalizedDefect mu).rank = 2 * (Finset.univ.filter (fun j => mu j ≠ 0)).card := by
  have h : normalizedDefect mu * (sigma n)ᵀ = thermalCovariance mu := by
    simp [normalizedDefect, sigma, thermalCovariance, fromBlocks_transpose, fromBlocks_multiply]
  have hu : IsUnit (sigma n)ᵀ.det := by
    rw [det_transpose]; exact isUnit_iff_ne_zero.2 (sigma_det n)
  rw [← rank_mul_eq_left_of_isUnit_det _ _ hu, h, rank_thermalR]

lemma rank_block {a : Type*} [Fintype a] [DecidableEq a] (A P : Matrix a a ℝ)
    (hPP : P * P = P) (hPA : P * A = A) (hAP : A * P = A) :
    (A + (1 - P)).rank = A.rank + (1 - P).rank := by
  set Q := 1 - P
  have hQP : Q * P = 0 := by simp [Q, Matrix.sub_mul, hPP]
  have hPQ : P * Q = 0 := by simp [Q, Matrix.mul_sub, hPP]
  have hQQ : Q * Q = Q := by simp [Q, Matrix.sub_mul, Matrix.mul_sub, hPP]
  have h1 : (A + Q) * P = A := by rw [Matrix.add_mul, hAP, hQP, add_zero]
  have h2 : (A + Q) * Q = Q := by
    rw [Matrix.add_mul, hQQ]
    have : A * Q = 0 := by simp [Q, Matrix.mul_sub, hAP]
    rw [this, zero_add]
  unfold Matrix.rank
  set RA := LinearMap.range A.mulVecLin
  set RQ := LinearMap.range Q.mulVecLin
  set RM := LinearMap.range (A + Q).mulVecLin
  have hle : RA ⊔ RQ ≤ RM := by
    apply sup_le
    · rintro _ ⟨v, rfl⟩
      refine ⟨P *ᵥ v, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1]
    · rintro _ ⟨v, rfl⟩
      refine ⟨Q *ᵥ v, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h2]
  have hge : RM ≤ RA ⊔ RQ := by
    rintro _ ⟨v, rfl⟩
    simp only [Matrix.mulVecLin_apply, Matrix.add_mulVec]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  have hinf : RA ⊓ RQ = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    simp only [Matrix.mulVecLin_apply] at hu hv
    have e1 : P *ᵥ w = w := by rw [← hu, Matrix.mulVec_mulVec, hPA]
    have e2 : P *ᵥ w = 0 := by rw [← hv, Matrix.mulVec_mulVec, hPQ, Matrix.zero_mulVec]
    rw [Submodule.mem_bot, ← e1, e2]
  have := Submodule.finrank_sup_add_finrank_inf_eq RA RQ
  rw [hinf, finrank_bot, add_zero] at this
  rw [le_antisymm hge hle, this]

end X5MGP

noncomputable section
open scoped Matrix ComplexOrder

namespace X5MGP
open QAlgorithms.Papers.Independent.Dependency50.P10 QAlgorithms.Papers.Independent.Frontier18.P05
  Matrix

variable {n : ℕ}

lemma retained_inj (mu : Fin n → ℝ) (pure : Bool) :
    Function.Injective (retainedIndex mu pure) :=
  Subtype.val_injective.comp (retainedModes mu pure).equivFin.symm.injective

lemma retained_mem (mu : Fin n → ℝ) (pure : Bool) (j : Fin n)
    (hj : ∀ l, retainedIndex mu pure l ≠ j) : j ∉ retainedModes mu pure := by
  intro hm
  apply hj ((retainedModes mu pure).equivFin ⟨j, hm⟩)
  simp [retainedIndex]

lemma retained_true (mu : Fin n → ℝ) :
    retainedModes mu true = Finset.univ.filter (fun j => mu j ≠ 1) := by
  ext j; simp [retainedModes]

lemma retained_false (mu : Fin n → ℝ) :
    retainedModes mu false = Finset.univ.filter (fun j => mu j = 0) := by
  ext j; simp [retainedModes]

lemma rank_triple {a : Type*} [Fintype a] [DecidableEq a] (U V : Matrix a a ℝ) (hU : IsUnit U.det)
    (hV : IsUnit V.det) (K : Matrix a a ℝ) : (U * K * V).rank = K.rank := by
  rw [rank_mul_eq_left_of_isUnit_det _ _ hV, rank_mul_eq_right_of_isUnit_det _ _ hU]

end X5MGP


noncomputable section

open scoped ComplexOrder
open Matrix QAlgorithms.Papers.Independent.Dependency50.P10
  QAlgorithms.Papers.Independent.Frontier18.P05

namespace X5KernelRank

variable {a : Type*} [Fintype a] [DecidableEq a]

/-- The real projection matrix acts as the orthogonal projection onto the range. -/
lemma proj_mulVec (A : Matrix a a ℝ) (v : a → ℝ) :
    realRangeProjection A *ᵥ v =
      WithLp.ofLp ((LinearMap.range (Matrix.toEuclideanLin A)).starProjection
        (WithLp.toLp 2 v)) := by
  set U := LinearMap.range (Matrix.toEuclideanLin A)
  have hlin : (Matrix.toLin' (realRangeProjection A)) =
      (WithLp.linearEquiv 2 ℝ (a → ℝ)).toLinearMap ∘ₗ
        (U.starProjection : EuclideanSpace ℝ a →ₗ[ℝ] EuclideanSpace ℝ a) ∘ₗ
          (WithLp.linearEquiv 2 ℝ (a → ℝ)).symm.toLinearMap := by
    refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
    funext i
    simp [Matrix.toLin'_apply, realRangeProjection, Matrix.mulVec_single_one,
      EuclideanSpace.single]
    rfl
  have := congrArg (fun f => f v) hlin
  simpa [Matrix.toLin'_apply] using this

section real
variable (A : Matrix a a ℝ)

lemma toLp_mulVec_mem (v : a → ℝ) :
    WithLp.toLp 2 (A *ᵥ v) ∈ LinearMap.range (Matrix.toEuclideanLin A) :=
  ⟨WithLp.toLp 2 v, rfl⟩

lemma proj_idem (v : a → ℝ) :
    realRangeProjection A *ᵥ (realRangeProjection A *ᵥ v) = realRangeProjection A *ᵥ v := by
  rw [proj_mulVec, proj_mulVec, WithLp.toLp_ofLp,
    Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ _)]

lemma proj_A (v : a → ℝ) : realRangeProjection A *ᵥ (A *ᵥ v) = A *ᵥ v := by
  rw [proj_mulVec, Submodule.starProjection_eq_self_iff.2 (toLp_mulVec_mem A v)]

lemma mem_orth_iff (hA : Aᵀ = A) (w : EuclideanSpace ℝ a) :
    w ∈ (LinearMap.range (Matrix.toEuclideanLin A))ᗮ ↔ A *ᵥ WithLp.ofLp w = 0 := by
  rw [LinearMap.orthogonal_range, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    conjTranspose_eq_transpose_of_trivial, hA, LinearMap.mem_ker]
  constructor
  · intro h; have := congrArg WithLp.ofLp h; simpa using this
  · intro h; apply_fun WithLp.ofLp using WithLp.ofLp_injective 2; simpa using h

lemma A_proj (hA : Aᵀ = A) (v : a → ℝ) : A *ᵥ (realRangeProjection A *ᵥ v) = A *ᵥ v := by
  set U := LinearMap.range (Matrix.toEuclideanLin A)
  have hmem : WithLp.toLp 2 v - U.starProjection (WithLp.toLp 2 v) ∈ Uᗮ :=
    Submodule.sub_starProjection_mem_orthogonal _
  rw [mem_orth_iff A hA] at hmem
  rw [proj_mulVec]
  have : A *ᵥ (v - WithLp.ofLp (U.starProjection (WithLp.toLp 2 v))) = 0 := by simpa using hmem
  rw [Matrix.mulVec_sub, sub_eq_zero] at this
  exact this.symm

lemma proj_ker (hA : Aᵀ = A) (v : a → ℝ) (h : A *ᵥ v = 0) : realRangeProjection A *ᵥ v = 0 := by
  rw [proj_mulVec, (Submodule.starProjection_apply_eq_zero_iff _).2 ((mem_orth_iff A hA _).2 h)]
  rfl

lemma mat_ext {M N : Matrix a a ℝ} (h : ∀ v, M *ᵥ v = N *ᵥ v) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)

lemma B_unit (hA : Aᵀ = A) : IsUnit (A + (1 - realRangeProjection A)) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  rw [← sub_eq_zero] at hvw ⊢
  rw [← Matrix.mulVec_sub] at hvw
  set u := v - w
  have h1 := congrArg (realRangeProjection A *ᵥ ·) hvw
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_sub, proj_A, proj_idem, Matrix.mulVec_zero] at h1
  have hAu : A *ᵥ u = 0 := by simpa using h1
  have hPu := proj_ker A hA u hAu
  simpa [Matrix.add_mulVec, Matrix.sub_mulVec, hAu, hPu] using hvw

lemma B_mulVec_proj (hA : Aᵀ = A) (x : a → ℝ) :
    (A + (1 - realRangeProjection A)) *ᵥ (realRangeProjection A *ᵥ x) = A *ᵥ x := by
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, A_proj A hA, proj_idem, sub_self,
    add_zero]

lemma proj_B_mulVec (z : a → ℝ) :
    realRangeProjection A *ᵥ ((A + (1 - realRangeProjection A)) *ᵥ z) = A *ᵥ z := by
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_sub, proj_A, proj_idem, sub_self, add_zero]

lemma supportInverse_mulVec (x : a → ℝ) :
    supportInverse A *ᵥ x = realRangeProjection A *ᵥ
      ((A + (1 - realRangeProjection A))⁻¹ *ᵥ (realRangeProjection A *ᵥ x)) := by
  simp [supportInverse, Matrix.mulVec_mulVec, Matrix.mul_assoc]

lemma S1 (hA : Aᵀ = A) (x : a → ℝ) :
    A *ᵥ (supportInverse A *ᵥ x) = realRangeProjection A *ᵥ x := by
  have hB := B_unit A hA
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hB
  rw [supportInverse_mulVec, A_proj A hA]
  set y := realRangeProjection A *ᵥ x
  have hz : (A + (1 - realRangeProjection A)) *ᵥ
      ((A + (1 - realRangeProjection A))⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have := congrArg (realRangeProjection A *ᵥ ·) hz
  simp only [proj_B_mulVec] at this
  rw [this]
  exact proj_idem A x

lemma S2 (hA : Aᵀ = A) (x : a → ℝ) :
    supportInverse A *ᵥ (A *ᵥ x) = realRangeProjection A *ᵥ x := by
  have hB := B_unit A hA
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hB
  have hQB : ∀ y, (A + (1 - realRangeProjection A))⁻¹ *ᵥ
      ((A + (1 - realRangeProjection A)) *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  rw [supportInverse_mulVec, proj_A, ← B_mulVec_proj A hA, hQB, proj_idem]

lemma S3 (x : a → ℝ) :
    realRangeProjection A *ᵥ (supportInverse A *ᵥ x) = supportInverse A *ᵥ x := by
  rw [supportInverse_mulVec, proj_idem]

lemma S4 (x : a → ℝ) :
    supportInverse A *ᵥ (realRangeProjection A *ᵥ x) = supportInverse A *ᵥ x := by
  rw [supportInverse_mulVec, supportInverse_mulVec, proj_idem]

lemma M_AAp (hA : Aᵀ = A) : A * supportInverse A = realRangeProjection A :=
  mat_ext fun v => by rw [← Matrix.mulVec_mulVec, S1 A hA]
lemma M_ApA (hA : Aᵀ = A) : supportInverse A * A = realRangeProjection A :=
  mat_ext fun v => by rw [← Matrix.mulVec_mulVec, S2 A hA]
lemma M_PAp : realRangeProjection A * supportInverse A = supportInverse A :=
  mat_ext fun v => by rw [← Matrix.mulVec_mulVec, S3]
lemma M_ApP : supportInverse A * realRangeProjection A = supportInverse A :=
  mat_ext fun v => by rw [← Matrix.mulVec_mulVec, S4]
lemma M_AP (hA : Aᵀ = A) : A * realRangeProjection A = A :=
  mat_ext fun v => by rw [← Matrix.mulVec_mulVec, A_proj A hA]
lemma M_PA : realRangeProjection A * A = A :=
  mat_ext fun v => by rw [← Matrix.mulVec_mulVec, proj_A]
lemma M_PP : realRangeProjection A * realRangeProjection A = realRangeProjection A :=
  mat_ext fun v => by rw [← Matrix.mulVec_mulVec, proj_idem]

lemma M_SP (hA : Aᵀ = A) (S : Matrix a a ℝ) (hker : ∀ w, A *ᵥ w = 0 → S *ᵥ w = 0) :
    S * realRangeProjection A = S :=
  mat_ext fun v => by
    rw [← Matrix.mulVec_mulVec]
    have h : A *ᵥ (v - realRangeProjection A *ᵥ v) = 0 := by
      rw [Matrix.mulVec_sub, A_proj A hA, sub_self]
    have := hker _ h
    rw [Matrix.mulVec_sub, sub_eq_zero] at this
    exact this.symm

lemma M_PS (hA : Aᵀ = A) (S : Matrix a a ℝ) (hSt : Sᵀ = -S)
    (hker : ∀ w, A *ᵥ w = 0 → S *ᵥ w = 0) :
    realRangeProjection A * S = S :=
  mat_ext fun v => by
    rw [← Matrix.mulVec_mulVec, proj_mulVec]
    set U := LinearMap.range (Matrix.toEuclideanLin A)
    have hmem : WithLp.toLp 2 (S *ᵥ v) ∈ U := by
      rw [← Submodule.orthogonal_orthogonal U, Submodule.mem_orthogonal]
      intro w hw
      rw [mem_orth_iff A hA] at hw
      have h0 := hker _ hw
      have : WithLp.ofLp w ⬝ᵥ (S *ᵥ v) = 0 := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hSt, Matrix.neg_mulVec, h0,
          neg_zero, zero_dotProduct]
      simpa [PiLp.inner_apply, dotProduct, mul_comm] using this
    rw [Submodule.starProjection_eq_self_iff.2 hmem]

end real

section cx

lemma cx_mul {b c d : Type*} [Fintype c] (A : Matrix b c ℝ) (B : Matrix c d ℝ) :
    complexify (A * B) = complexify A * complexify B := by
  ext i j; simp [complexify, Matrix.mul_apply]

lemma cx_sub {b c : Type*} (A B : Matrix b c ℝ) :
    complexify (A - B) = complexify A - complexify B := by
  ext i j; simp [complexify]

lemma cx_transpose {b c : Type*} (A : Matrix b c ℝ) :
    complexify Aᵀ = (complexify A)ᵀ := by
  ext i j; simp [complexify]

lemma cx_neg {b c : Type*} (A : Matrix b c ℝ) : complexify (-A) = -complexify A := by
  ext i j; simp [complexify]

lemma cx_mulVec (A : Matrix a a ℝ) (v : a → ℝ) :
    complexify A *ᵥ (fun i => (v i : ℂ)) = fun i => ((A *ᵥ v) i : ℂ) := by
  funext i; simp [complexify, Matrix.mulVec, dotProduct]

lemma mem_cker {M : Matrix a a ℂ} {v : a → ℂ} : v ∈ complexKernel M ↔ M *ᵥ v = 0 := by
  simp [complexKernel]

lemma rank_add_finrank_ker (M : Matrix a a ℂ) :
    M.rank + Module.finrank ℂ (complexKernel M) = Fintype.card a := by
  have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at this
  exact this

end cx

open scoped InnerProductSpace in
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

lemma proj_symm (A : Matrix a a ℝ) : (realRangeProjection A)ᵀ = realRangeProjection A := by
  ext i j
  simp only [Matrix.transpose_apply, realRangeProjection]
  have h := Submodule.inner_starProjection_left_eq_right
    (LinearMap.range (Matrix.toEuclideanLin A)) (EuclideanSpace.single i (1 : ℝ))
    (EuclideanSpace.single j (1 : ℝ))
  simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] using h

lemma supportInverse_symm (A : Matrix a a ℝ) (hA : Aᵀ = A) :
    (supportInverse A)ᵀ = supportInverse A := by
  simp only [supportInverse, Matrix.transpose_mul, proj_symm, Matrix.transpose_nonsing_inv,
    Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, hA, Matrix.mul_assoc]

lemma cx_conjTranspose' {b c : Type*} (A : Matrix b c ℝ) :
    (complexify A)ᴴ = complexify Aᵀ := by
  ext i j; simp [complexify, Matrix.conjTranspose_apply]

lemma cx_psd (M : Matrix a a ℝ) (h : M.PosSemidef) : (complexify M).PosSemidef := by
  have hMt : Mᵀ = M := by
    have := h.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · rw [Matrix.IsHermitian, cx_conjTranspose', hMt]
  · set re : a → ℝ := fun i => (v i).re
    set im : a → ℝ := fun i => (v i).im
    have hre := h.dotProduct_mulVec_nonneg re
    have him := h.dotProduct_mulVec_nonneg im
    have key : star v ⬝ᵥ (complexify M *ᵥ v) =
        ((re ⬝ᵥ (M *ᵥ re) + im ⬝ᵥ (M *ᵥ im) : ℝ) : ℂ) := by
      have hsym : ∑ i, ∑ j, M i j * (re i * im j - im i * re j) = 0 := by
        have h1 : ∑ i, ∑ j, M i j * (im i * re j) = ∑ i, ∑ j, M i j * (re i * im j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          have : M j i = M i j := by
            have := congrFun (congrFun hMt i) j
            simpa [Matrix.transpose_apply] using this
          rw [this]; ring
        simp only [mul_sub, Finset.sum_sub_distrib, h1, sub_self]
      apply Complex.ext
      · simp only [dotProduct, Matrix.mulVec, complexify, Pi.star_apply, Complex.re_sum,
          Finset.mul_sum, Complex.ofReal_re, star_trivial]
        simp [Complex.mul_re, Finset.mul_sum, Finset.sum_add_distrib, re, im, mul_comm,
          mul_left_comm, mul_assoc]
      · simp only [dotProduct, Matrix.mulVec, complexify, Pi.star_apply, Complex.im_sum,
          Finset.mul_sum, Complex.ofReal_im]
        simp only [Complex.mul_im, Complex.mul_re, Complex.star_def, Complex.conj_re,
          Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.im_sum, Complex.re_sum,
          Finset.mul_sum]
        refine Eq.trans ?_ hsym
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [re, im]
        ring
    rw [key]
    exact_mod_cast add_nonneg (by simpa using hre) (by simpa using him)

lemma cx_smul {b c : Type*} (r : ℝ) (A : Matrix b c ℝ) :
    complexify (r • A) = (r : ℂ) • complexify A := by
  ext i j; simp [complexify]

lemma cx_inj {b c : Type*} {A B : Matrix b c ℝ} (h : complexify A = complexify B) : A = B := by
  ext i j
  have := congrFun (congrFun h i) j
  simpa [complexify] using this

end X5KernelRank

noncomputable section
open scoped Matrix ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P10 QAlgorithms.Papers.Independent.Frontier18.P05
  Matrix X5MGP in
theorem solution {n : ℕ} (hn : 0 < n)
    (X Y : Matrix (Phase n) (Phase n) ℝ) (hCP : (cpMatrix X Y).PosSemidef) :
    let P := realRangeProjection Y
    let Ybar := Y + (1 - P)
    ∃ R O : Matrix (Phase n) (Phase n) ℝ,
      ∃ mu : Fin n → ℝ,
        R.transpose = R ∧ R.PosDef ∧ R * R = Ybar ∧
        O * O.transpose = 1 ∧
        (∀ j, 0 ≤ mu j ∧ mu j ≤ 1) ∧
        O * R⁻¹ * commutatorDefect X * (R⁻¹).transpose * O.transpose =
          normalizedDefect mu ∧
        P * Ybar * P = Y ∧
        (let B := P * R * O.transpose * fullCoupling mu
         let G := thermalPurification (fun j => environmentVariance (mu j))
         pureCovariance G (jointSigma n n) ∧
         B * jointSigma n n * B.transpose = commutatorDefect X ∧
         B * G * B.transpose = Y ∧
         ∀ pure : Bool,
           let q := retainedCount mu pure
           let e := retainedEmbedding mu pure
           let Bsmall := B.submatrix id e
           let Gsmall := G.submatrix e e
           physicalCovariance Gsmall (jointSigma n q) ∧
           (pure = true → pureCovariance Gsmall (jointSigma n q)) ∧
           Bsmall * jointSigma n q * Bsmall.transpose = commutatorDefect X ∧
           Bsmall * Gsmall * Bsmall.transpose = Y ∧
           (pure = true →
             (2 : ℤ) * ((n + q : ℕ) : ℤ) = (4 : ℤ) * (n : ℤ) -
               ((Y.rank : ℤ) - ((rankResidual Y (commutatorDefect X)).rank : ℤ))) ∧
           (pure = false →
             2 * (n + q) + (commutatorDefect X).rank = 4 * n)) := by
  intro P Ybar
  set S := commutatorDefect X with hSdef
  set K := cpMatrix X Y with hKdef
  have hsig : (sigma n)ᵀ = -sigma n := sigma_t n
  have hSt : Sᵀ = -S := by
    simp only [S, commutatorDefect, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_transpose, hsig]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    abel
  have hYt : Yᵀ = Y := by
    ext i j
    have h := hCP.isHermitian.apply j i
    have h2 := congrArg Complex.re h
    simp [K, cpMatrix, complexify, Matrix.sub_apply] at h2
    simpa [Matrix.transpose_apply] using h2.symm
  -- kernel inclusion
  have hkerR : ∀ w, Y *ᵥ w = 0 → S *ᵥ w = 0 := by
    have hKt : Kᵀ = complexify Y + Complex.I • complexify S := by
      have : (complexify S)ᵀ = -complexify S := by
        ext i j; have := congrFun (congrFun hSt j) i; simp [complexify] at this ⊢; simp [this]
      have hYc : (complexify Y)ᵀ = complexify Y := by
        ext i j; have := congrFun (congrFun hYt j) i; simp [complexify] at this ⊢; simp [this]
      simp [K, cpMatrix, Matrix.transpose_sub, Matrix.transpose_smul, hYc, this, S,
        sub_eq_add_neg]
    have hKtpsd : Kᵀ.PosSemidef := hCP.transpose
    intro w hw
    set v : Phase n → ℂ := fun i => (w i : ℂ)
    have hYv : complexify Y *ᵥ v = 0 := by
      rw [cx_mulVec, hw]; funext i; simp
    have hKmv : K *ᵥ v = complexify Y *ᵥ v - Complex.I • (complexify S *ᵥ v) := by
      simp [K, cpMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, S]
    have hKtmv : Kᵀ *ᵥ v = complexify Y *ᵥ v + Complex.I • (complexify S *ᵥ v) := by
      rw [hKt, Matrix.add_mulVec, Matrix.smul_mulVec]
    have h1 := hCP.dotProduct_mulVec_nonneg v
    have h2 := hKtpsd.dotProduct_mulVec_nonneg v
    rw [hKmv, hYv, zero_sub, dotProduct_neg] at h1
    rw [hKtmv, hYv, zero_add] at h2
    have h3 : star v ⬝ᵥ (K *ᵥ v) = 0 := by
      rw [hKmv, hYv, zero_sub, dotProduct_neg]
      exact le_antisymm (by simpa using h2) h1
    have h4 := (hCP.dotProduct_mulVec_zero_iff v).1 h3
    rw [hKmv, hYv, zero_sub, neg_eq_zero, smul_eq_zero] at h4
    have h5 := h4.resolve_left Complex.I_ne_zero
    rw [cx_mulVec] at h5
    funext i
    have := congrFun h5 i
    simpa using this
  -- projection facts
  have hPdef : P = realRangeProjection Y := rfl
  have hPt : Pᵀ = P := X5KernelRank.proj_symm Y
  have hPP : P * P = P := X5KernelRank.M_PP Y
  have hPY : P * Y = Y := X5KernelRank.M_PA Y
  have hYP : Y * P = Y := X5KernelRank.M_AP Y hYt
  have hPS : P * S = S := X5KernelRank.M_PS Y hYt S hSt hkerR
  have hSP : S * P = S := X5KernelRank.M_SP Y hYt S hkerR
  have hYbar : Ybar = Y + (1 - P) := rfl
  -- positivity
  have hYpsd : Y.PosSemidef := by
    have hK : (complexify Y - Complex.I • complexify S).PosSemidef := hCP
    have hYh : Y.IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hYt]
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hYh fun x => ?_
    have hskew : x ⬝ᵥ (S *ᵥ x) = 0 := by
      have : x ⬝ᵥ (S *ᵥ x) = -(x ⬝ᵥ (S *ᵥ x)) := by
        conv_lhs => rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hSt,
          Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]
      linarith
    have key : star (fun i => (x i : ℂ)) ⬝ᵥ ((complexify Y - Complex.I • complexify S) *ᵥ
        (fun i => (x i : ℂ))) = ((x ⬝ᵥ (Y *ᵥ x) : ℝ) : ℂ) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, cx_mulVec, cx_mulVec, dotProduct_sub,
        dotProduct_smul]
      simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
      simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum]
      simp only [dotProduct] at hskew
      rw [hskew]; simp
    have h1 := hK.dotProduct_mulVec_nonneg (fun i => (x i : ℂ))
    rw [key] at h1
    simpa using Complex.zero_le_real.1 h1
  have hQpsd : (1 - P).PosSemidef := by
    have hQ : 1 - P = (1 - P)ᴴ * (1 - P) := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub, hPt,
        Matrix.transpose_one]
      simp [Matrix.sub_mul, Matrix.mul_sub, hPP]
    rw [hQ]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have hYbpd : Ybar.PosDef :=
    (hYpsd.add hQpsd).posDef_iff_isUnit.2 (X5KernelRank.B_unit Y hYt)
  obtain ⟨R, hRt, hRpd, hRR⟩ := psd_sqrt Ybar hYbpd
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.2 hRpd.det_pos.ne'
  have hRi : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul _ hRu
  have hRi' : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv _ hRu
  have hRit : R⁻¹ᵀ = R⁻¹ := by rw [Matrix.transpose_nonsing_inv, hRt]
  set M := R⁻¹ * S * R⁻¹ᵀ with hM
  have hMt : Mᵀ = -M := by
    rw [hM, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hSt]
    simp [Matrix.mul_assoc]
  obtain ⟨O, mu, hOO, hmu0, hON⟩ := skew_normal M hMt
  have hOu : IsUnit O.det := by
    have := congrArg Matrix.det hOO
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    exact isUnit_iff_ne_zero.2 fun h => by rw [h, zero_mul] at this; exact zero_ne_one this
  have hOO' : Oᵀ * O = 1 := by
    rw [← Matrix.inv_eq_right_inv hOO]; exact Matrix.nonsing_inv_mul _ hOu
  -- the two normal-form identities
  have hSN : S = R * Oᵀ * normalizedDefect mu * O * R := by
    rw [← hON, hM, hRit]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Oᵀ O, hOO', Matrix.one_mul, ← Matrix.mul_assoc Oᵀ O, hOO',
      Matrix.one_mul, hRi, Matrix.mul_one,
      ← Matrix.mul_assoc R R⁻¹, hRi', Matrix.one_mul]
  have hYO : Ybar = R * Oᵀ * O * R := by rw [Matrix.mul_assoc R, hOO', Matrix.mul_one, hRR]
  -- mu ≤ 1
  have hmu1 : ∀ j, mu j ≤ 1 := by
    apply defect_ge mu
    have hKb : (complexify Ybar - Complex.I • complexify S).PosSemidef := by
      have : complexify Ybar - Complex.I • complexify S =
          (complexify Y - Complex.I • complexify S) + complexify (1 - P) := by
        rw [hYbar]; ext i j; simp [complexify]; ring
      rw [this]
      exact (show (complexify Y - Complex.I • complexify S).PosSemidef from hCP).add
        (X5KernelRank.cx_psd _ hQpsd)
    set T := O * R⁻¹
    have := hKb.mul_mul_conjTranspose_same (complexify T)
    convert this using 1
    have e1 : T * Ybar * Tᵀ = 1 := by
      rw [hYO]; simp only [T, Matrix.transpose_mul, hRit, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc R R⁻¹, hRi', Matrix.one_mul, ← Matrix.mul_assoc Oᵀ O, hOO',
        Matrix.one_mul, ← Matrix.mul_assoc R⁻¹ R, hRi, Matrix.one_mul, hOO]
    have e2 : T * S * Tᵀ = normalizedDefect mu := by
      rw [← hON]; simp only [T, hM, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← e1, ← e2]
    simp only [cx_mul, cx_transpose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  have hPYP : P * Ybar * P = Y := by
    rw [hYbar, Matrix.mul_add, Matrix.add_mul, hPY, hYP, Matrix.mul_sub, Matrix.mul_one, hPP,
      sub_self, Matrix.zero_mul, add_zero]
  refine ⟨R, O, mu, hRt, hRpd, hRR, hOO, fun j => ⟨hmu0 j, hmu1 j⟩,
    by rw [← hON, hM]; simp only [Matrix.mul_assoc], hPYP, ?_⟩
  intro B G
  have hd1 : ∀ j, 1 ≤ environmentVariance (mu j) := by
    intro j; unfold environmentVariance; split_ifs with h
    · norm_num
    · have h0 : 0 < mu j := lt_of_le_of_ne (hmu0 j) (Ne.symm h)
      rw [le_inv_comm₀ zero_lt_one h0, inv_one]; exact hmu1 j
  have hGphys : physicalCovariance G (jointSigma n n) := purif_phys _ hd1
  have hGp : pureCovariance G (jointSigma n n) := by
    refine ⟨hGphys, ?_⟩
    have := purif_sub_det _ hd1 id Function.injective_id (fun j h => absurd rfl (h j))
    have hf : fmap (id : Fin n → Fin n) = id := by
      funext x; rcases x with x | (x | x) <;> rfl
    rwa [hf, submatrix_id_id] at this
  have hBt : Bᵀ = (fullCoupling mu)ᵀ * O * R * P := by
    simp [B, Matrix.transpose_mul, hRt, hPt, Matrix.mul_assoc]
  have hBJ : B * jointSigma n n * Bᵀ = S := by
    rw [hBt]
    calc P * R * Oᵀ * fullCoupling mu * jointSigma n n * ((fullCoupling mu)ᵀ * O * R * P)
        = P * R * Oᵀ * (fullCoupling mu * jointSigma n n * (fullCoupling mu)ᵀ) * O * R * P := by
          simp only [Matrix.mul_assoc]
      _ = P * (R * Oᵀ * normalizedDefect mu * O * R) * P := by
          rw [FJF mu hmu0]; simp only [Matrix.mul_assoc]
      _ = S := by rw [← hSN, hPS, hSP]
  have hBG : B * G * Bᵀ = Y := by
    rw [hBt]
    calc P * R * Oᵀ * fullCoupling mu * G * ((fullCoupling mu)ᵀ * O * R * P)
        = P * R * Oᵀ * (fullCoupling mu * G * (fullCoupling mu)ᵀ) * O * R * P := by
          simp only [Matrix.mul_assoc]
      _ = P * (R * Oᵀ * O * R) * P := by
          rw [FGF mu hmu0 hmu1]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = Y := by rw [← hYO, hPYP]
  refine ⟨hGp, hBJ, hBG, fun pure => ?_⟩
  intro q e Bsmall Gsmall
  set ι := retainedIndex mu pure with hιdef
  have hι := retained_inj mu pure
  have he : e = fmap ι := rfl
  have heinj : Function.Injective e := fmap_inj ι hι
  have hnot : ∀ j, (∀ l, ι l ≠ j) → mu j ≠ 0 := by
    intro j hj
    have hm := retained_mem mu pure j hj
    cases pure
    · rw [retained_false] at hm; simpa using hm
    · rw [retained_true] at hm; simp at hm; rw [hm]; norm_num
  have hBz : ∀ i u, (∀ l, e l ≠ u) → B i u = 0 := by
    intro i u hu
    rcases u with u | (j | j)
    · exact absurd rfl (hu (Sum.inl u))
    · have hj : ∀ l, ι l ≠ j := fun l h => hu (Sum.inr (Sum.inl l)) (by simp [he, fmap, h])
      have h0 := hnot j hj
      simp [B, Matrix.mul_apply, fullCoupling, nullSwap, h0, Fintype.sum_sum_type, diagonal_apply]
    · have hj : ∀ l, ι l ≠ j := fun l h => hu (Sum.inr (Sum.inr l)) (by simp [he, fmap, h])
      have h0 := hnot j hj
      simp [B, Matrix.mul_apply, fullCoupling, nullSwap, h0, Fintype.sum_sum_type, diagonal_apply]
  have hJq : jointSigma n q = (jointSigma n n).submatrix e e := (joint_sub ι hι).symm
  have hGs : physicalCovariance Gsmall (jointSigma n q) := by
    refine ⟨?_, ?_⟩
    · show (G.submatrix e e)ᵀ = G.submatrix e e
      rw [transpose_submatrix, hGphys.1]
    · rw [hJq]
      have := hGphys.2.submatrix e
      convert this using 1
      ext x y; simp [Gsmall, complexify]
  -- rank facts
  have hROu : IsUnit (R * Oᵀ).det := by
    rw [Matrix.det_mul, Matrix.det_transpose]; exact hRu.mul hOu
  have hORu : IsUnit (O * R).det := by
    rw [Matrix.det_mul]; exact hOu.mul hRu
  have hSrank : S.rank = 2 * (Finset.univ.filter (fun j => mu j ≠ 0)).card := by
    rw [hSN, show R * Oᵀ * normalizedDefect mu * O * R = (R * Oᵀ) * normalizedDefect mu * (O * R)
      by simp only [Matrix.mul_assoc], rank_triple _ _ hROu hORu, rank_defect]
  refine ⟨hGs, ?_, ?_, ?_, ?_, ?_⟩
  · intro hp
    refine ⟨hGs, ?_⟩
    apply purif_sub_det _ hd1 ι hι
    intro j hj
    have hm := retained_mem mu pure j hj
    subst hp
    rw [retained_true] at hm; simp at hm
    simp [environmentVariance, hm]
  · rw [hJq]; exact (sub_zero_cols B _ e heinj hBz).trans hBJ
  · exact (sub_zero_cols B G e heinj hBz).trans hBG
  · intro hp
    have hq : q = (Finset.univ.filter (fun j => mu j ≠ 1)).card := by
      show retainedCount mu pure = _
      subst hp; rw [retainedCount, retained_true]
    -- residual
    have hSi : supportInverse Y = P * Ybar⁻¹ * P := rfl
    have hPSt : P * Sᵀ = Sᵀ := by
      rw [← hPt, ← Matrix.transpose_mul, hSP]
    have hYbi : Ybar⁻¹ = R⁻¹ * R⁻¹ := by rw [← hRR, Matrix.mul_inv_rev]
    have hSt' : Sᵀ = R * Oᵀ * (normalizedDefect mu)ᵀ * O * R := by
      conv_lhs => rw [hSN]
      simp only [Matrix.transpose_mul, hRt, Matrix.transpose_transpose, Matrix.mul_assoc]
    have hres : rankResidual Y S + (1 - P) =
        (R * Oᵀ) * (1 - normalizedDefect mu * (normalizedDefect mu)ᵀ) * (O * R) := by
      have e1 : S * supportInverse Y * Sᵀ = S * Ybar⁻¹ * Sᵀ := by
        rw [hSi, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hSP, Matrix.mul_assoc, Matrix.mul_assoc,
          hPSt, ← Matrix.mul_assoc]
      have e2 : S * Ybar⁻¹ * Sᵀ =
          R * Oᵀ * (normalizedDefect mu * (normalizedDefect mu)ᵀ) * O * R := by
        rw [hYbi, hSt']
        conv_lhs => rw [hSN]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc R R⁻¹, hRi', Matrix.one_mul, ← Matrix.mul_assoc R⁻¹ R, hRi,
          Matrix.one_mul, ← Matrix.mul_assoc O Oᵀ, hOO, Matrix.one_mul]
      unfold rankResidual
      rw [e1, e2]
      have e3 : Y - R * Oᵀ * (normalizedDefect mu * (normalizedDefect mu)ᵀ) * O * R + (1 - P) =
          Ybar - R * Oᵀ * (normalizedDefect mu * (normalizedDefect mu)ᵀ) * O * R := by
        rw [hYbar]; abel
      rw [e3, hYO]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    have hNN : 1 - normalizedDefect mu * (normalizedDefect mu)ᵀ =
        thermalCovariance (fun j => 1 - mu j * mu j) := by
      ext (i | i) (j | j) <;>
        simp [normalizedDefect, thermalCovariance, fromBlocks_transpose, fromBlocks_multiply,
          diagonal_apply, one_apply, Matrix.mul_apply] <;> split_ifs <;> simp_all
    have hr1 : (rankResidual Y S + (1 - P)).rank =
        2 * (Finset.univ.filter (fun j => mu j ≠ 1)).card := by
      rw [hres, rank_triple _ _ hROu hORu, hNN, rank_thermalR]
      congr 2
      apply Finset.filter_congr
      intro j _
      have := hmu0 j
      constructor
      · intro h1 h2; apply h1; rw [h2]; ring
      · intro h1 h2; apply h1
        have h3 : (mu j - 1) * (mu j + 1) = 0 := by linear_combination -h2
        rcases mul_eq_zero.1 h3 with h4 | h4
        · linarith
        · linarith
    have hPr : P * rankResidual Y S = rankResidual Y S := by
      unfold rankResidual
      rw [Matrix.mul_sub, hPY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPS]
    have hrP : rankResidual Y S * P = rankResidual Y S := by
      unfold rankResidual
      rw [Matrix.sub_mul, hYP, Matrix.mul_assoc, ← hPt, ← Matrix.transpose_mul, hPS]
    have hb1 := rank_block (rankResidual Y S) P hPP hPr hrP
    have hb2 := rank_block Y P hPP hPY hYP
    have hYbu : IsUnit Ybar := hYbpd.isUnit
    have hrYb : Ybar.rank = n + n := by
      rw [Matrix.rank_of_isUnit Ybar hYbu]; simp
    rw [← hYbar, hrYb] at hb2
    rw [hr1] at hb1
    rw [hq]
    push_cast
    omega
  · intro hp
    have hq : q = (Finset.univ.filter (fun j => mu j = 0)).card := by
      show retainedCount mu pure = _
      subst hp; rw [retainedCount, retained_false]
    have hc : (Finset.univ.filter (fun j => mu j = 0)).card +
        (Finset.univ.filter (fun j => mu j ≠ 0)).card = n := by
      rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
    rw [hq, hSrank]
    omega

